// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! CPU-local execution leases. All bookkeeping is protected by the kernel IRQ
//! mask. No allocation, thread reference counting, or atomic RMW is required.
use crate::{arch, support::DisableInterruptGuard, types::NotThreadSafe};
use core::{
    cell::Cell,
    sync::atomic::{compiler_fence, Ordering},
};

const CPUS: usize = blueos_kconfig::CONFIG_NUM_CORES as usize;
#[cfg(not(smp))]
const _: () = assert!(CPUS == 1, "the local lock backend requires exactly one CPU");

struct CpuState {
    irq: Cell<usize>,
    plain: Cell<usize>,
    saved: Cell<usize>,
    pending: Cell<bool>,
}

impl CpuState {
    const fn new() -> Self {
        Self {
            irq: Cell::new(0),
            plain: Cell::new(0),
            saved: Cell::new(0),
            pending: Cell::new(false),
        }
    }
}

struct States([CpuState; CPUS]);
// SAFETY: each CPU accesses only its slot, with all kernel-capable asynchronous
// interrupts masked. Scheduling cannot move a live lease to another CPU.
unsafe impl Sync for States {}
static STATES: States = States([const { CpuState::new() }; CPUS]);

#[cold]
fn invalid_context() -> ! {
    // Do not enter the ordinary logger or panic handler from an excluded IRQ.
    #[cfg(target_board = "qemu_mps2_an385")]
    semihosting::println!("LOCAL_LOCK_INVALID_CONTEXT");
    core::intrinsics::abort()
}

#[inline(always)]
fn admit() {
    #[cfg(cortex_m)]
    {
        let ipsr: u32;
        unsafe {
            core::arch::asm!("mrs {}, ipsr", out(reg) ipsr, options(nomem, nostack, preserves_flags));
        }
        let exception = ipsr & 0x1ff;
        if exception != 0 {
            admit_exception(exception);
        }
    }
}

#[cfg(cortex_m)]
#[cold]
#[inline(never)]
fn admit_exception(exception: u32) {
    match exception {
        // SVC is synchronous. Borrow-state/lease updates never invoke SVC
        // or callbacks. The actual switch gateway separately checks leases.
        11 | 14 => (),
        15 => {
            if unsafe {
                cortex_m::peripheral::SCB::get_priority(
                    cortex_m::peripheral::scb::SystemHandler::SysTick,
                )
            } < arch::irq::IRQ_PRIORITY_FOR_SCHEDULER
            {
                invalid_context();
            }
        }
        n if n >= 16 => {
            if arch::irq::get_irq_priority(arch::irq::IrqNumber::new((n - 16) as u16))
                < arch::irq::IRQ_PRIORITY_FOR_SCHEDULER
            {
                invalid_context();
            }
        }
        _ => invalid_context(),
    }
}

#[cfg(not(smp))]
#[must_use]
struct ShortMask(usize);
#[cfg(not(smp))]
impl Drop for ShortMask {
    #[inline(always)]
    fn drop(&mut self) {
        // SAFETY: this scope is strictly nested; the operation preserves the mask.
        unsafe { arch::enable_local_irq_restore(self.0) };
    }
}

/// A bounded UP operation that only accesses kernel-IRQ-serialized state.
///
/// # Safety
/// The operation must not reschedule, invoke arbitrary code, or change the IRQ
/// mask or drop an owning IRQ lease. Any borrow surviving the scope needs
/// independent protection. Releasing the last preemption lease must retry
/// pending scheduling after the hardware mask has been restored.
#[cfg(not(smp))]
#[inline(always)]
pub(crate) unsafe fn with_short_mask<R>(
    op: impl for<'a> FnOnce(&'a DisableInterruptGuard) -> R,
) -> R {
    admit();
    let _restore = ShortMask(arch::disable_local_irq_save());
    // SAFETY: the saved mask stays held throughout this bounded operation.
    op(unsafe { DisableInterruptGuard::assume_disabled() })
}

/// Finish a scalar fast operation or promote its hardware mask to one owned
/// lease without briefly unmasking IRQs on the slow path.
///
/// # Safety
/// The closure must only access IRQ-serialized scalars without calling out.
#[cfg(not(smp))]
#[inline(always)]
pub(super) unsafe fn short_or_owned(op: impl FnOnce() -> bool) -> Option<DisableInterruptGuard> {
    admit();
    let mask = ShortMask(arch::disable_local_irq_save());
    if op() {
        return None;
    }
    register_masked(mask.0);
    core::mem::forget(mask);
    // SAFETY: ownership of exactly the lease just registered moves to the caller.
    Some(unsafe { DisableInterruptGuard::from_registered() })
}

/// # Safety
/// Stay on the current CPU with kernel IRQs masked while accessing this slot.
#[inline(always)]
unsafe fn state() -> &'static CpuState {
    &STATES.0[arch::current_cpu_id()]
}

#[inline(always)]
pub(crate) fn enter_irq() {
    admit();
    let old = arch::disable_local_irq_save();
    register_masked(old);
}

#[inline(always)]
fn register_masked(old: usize) {
    // SAFETY: both callers mask IRQs before selecting the CPU slot.
    let s = unsafe { state() };
    let n = s.irq.get();
    if n == usize::MAX {
        invalid_context();
    }
    if n == 0 {
        s.saved.set(old);
    }
    s.irq.set(n + 1);
}

#[inline(always)]
pub(crate) fn exit_irq() {
    let s = unsafe { state() };
    let n = s.irq.get();
    assert_ne!(n, 0);
    s.irq.set(n - 1);
    if n != 1 {
        return;
    }
    let old = s.saved.get();
    let kick = s.pending.get() && take_deferred(s);
    compiler_fence(Ordering::SeqCst);
    unsafe {
        arch::enable_local_irq_restore(old);
    }
    if kick {
        crate::scheduler::yield_me_now_or_later();
    }
}

// Only called after observing a pending request, under the kernel IRQ mask.
#[cold]
fn take_deferred(s: &CpuState) -> bool {
    if s.plain.get() != 0 || s.irq.get() != 0 {
        return false;
    }
    s.pending.set(false);
    true
}

#[derive(Debug)]
#[must_use]
pub(crate) struct PreemptLease {
    _not_send: NotThreadSafe,
}
impl PreemptLease {
    #[inline(always)]
    pub(crate) fn new_with(_irq: &DisableInterruptGuard) -> Self {
        // SAFETY: the borrowed guard protects this update on the current CPU.
        let s = unsafe { state() };
        s.plain.set(
            s.plain
                .get()
                .checked_add(1)
                .unwrap_or_else(|| invalid_context()),
        );
        Self {
            _not_send: NotThreadSafe,
        }
    }
    #[inline(always)]
    pub(super) unsafe fn release_after(
        lease: &mut core::mem::ManuallyDrop<Self>,
        unlock: impl FnOnce(),
    ) {
        // SAFETY: the caller supplies only the backend payload guard release.
        #[cfg(not(smp))]
        {
            let kick = unsafe {
                with_short_mask(|irq| {
                    unlock();
                    lease.unregister(irq);
                    let s = state();
                    s.pending.get() && take_deferred(s)
                })
            };
            if kick {
                crate::scheduler::yield_me_now_or_later();
            }
        }
        #[cfg(smp)]
        {
            unlock();
            lease.unregister(&DisableInterruptGuard::new());
        }
    }

    #[inline(always)]
    fn unregister(&mut self, _irq: &DisableInterruptGuard) {
        let s = unsafe { state() };
        s.plain.set(
            s.plain
                .get()
                .checked_sub(1)
                .expect("unbalanced preemption lease"),
        );
    }
}

impl Drop for PreemptLease {
    #[inline(always)]
    fn drop(&mut self) {
        self.unregister(&DisableInterruptGuard::new());
    }
}

// Called with the hardware kernel mask held, including in PendSV before any
// ordinary guard exists. A queued request is retried when the last lease exits.
#[inline(always)]
pub(crate) fn defer_if_held() -> bool {
    admit();
    let old = arch::disable_local_irq_save();
    // SAFETY: this admitted, masked section only inspects execution leases.
    let held = defer_if_held_with(unsafe { DisableInterruptGuard::assume_disabled() });
    unsafe {
        arch::enable_local_irq_restore(old);
    }
    held
}

#[inline(always)]
pub(crate) fn defer_if_held_with(_irq: &DisableInterruptGuard) -> bool {
    let s = unsafe { state() };
    let held = s.irq.get() != 0 || s.plain.get() != 0;
    if held {
        s.pending.set(true);
    }
    held
}

pub(crate) fn assert_can_suspend(irq_guard: bool) {
    admit();
    let old = arch::disable_local_irq_save();
    let s = unsafe { state() };
    let resume_mask = if irq_guard { s.saved.get() } else { old };
    #[cfg(cortex_m)]
    let resumes_enabled = resume_mask == 0;
    #[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
    let resumes_enabled = resume_mask & (1 << 3) != 0;
    #[cfg(target_arch = "aarch64")]
    let resumes_enabled = resume_mask & (1 << 7) == 0;
    let ok = s.irq.get() == usize::from(irq_guard) && s.plain.get() == 0 && resumes_enabled;
    unsafe {
        arch::enable_local_irq_restore(old);
    }
    assert!(ok, "cannot suspend while other execution leases are held");
}

pub(crate) fn assert_can_switch() {
    assert!(
        !defer_if_held(),
        "cannot switch while an execution lease is held"
    );
}
