// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

pub use bluekernel_arch::interface::*;

#[cfg(target_arch = "arm")]
pub mod arm;
#[cfg(target_arch = "arm")]
pub use bluekernel_arch::irq;
#[cfg(all(target_arch = "arm", use_mpu))]
pub use arm::mpu;
#[cfg(target_arch = "arm")]
pub use arm::panic_on_hardfault;

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
pub mod riscv;
#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
pub(crate) use riscv::irq;

#[cfg(target_arch = "aarch64")]
pub mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::irq;
#[cfg(target_arch = "aarch64")]
pub(crate) use aarch64::{asm, mmu, psci, registers, vector, virt};
#[cfg(target_arch = "aarch64")]
pub use aarch64::secondary_cpu_setup;

#[allow(dead_code)]
pub(crate) struct KernelArch;

#[cfg(target_arch = "arm")]
impl ThreadContext for arm::Context {
    fn init(&mut self) -> &mut Self {
        arm::Context::init(self)
    }

    fn set_return_address(&mut self, address: usize) -> &mut Self {
        arm::Context::set_return_address(self, address)
    }

    fn set_arg(&mut self, index: usize, value: usize) -> &mut Self {
        arm::Context::set_arg(self, index, value)
    }
}

#[cfg(target_arch = "arm")]
impl ArchInterface for KernelArch {
    type Context = arm::Context;
    type IsrContext = arm::IsrContext;

    fn disable_local_irq() {
        arm::disable_local_irq();
    }

    fn enable_local_irq() {
        arm::enable_local_irq();
    }

    fn disable_local_irq_save() -> IrqState {
        arm::disable_local_irq_save()
    }

    fn enable_local_irq_restore(old: IrqState) {
        arm::enable_local_irq_restore(old);
    }

    fn local_irq_enabled() -> bool {
        arm::local_irq_enabled()
    }

    fn current_cpu_id() -> CpuId {
        arm::current_cpu_id()
    }

    fn current_sp() -> usize {
        arm::current_sp()
    }

    fn idle() {
        arm::idle();
    }

    fn start_schedule(cont: ScheduleEntry) {
        arm::start_schedule(cont);
    }

    fn pend_switch_context() {
        arm::pend_switch_context();
    }

    fn switch_context_with_hook(hook: RawContextSwitchHook) {
        arm::switch_context_with_hook(hook.cast());
    }

    fn restore_context_with_hook(hook: RawContextSwitchHook) -> ! {
        arm::restore_context_with_hook(hook.cast())
    }

    fn switch_stack(to_sp: usize, cont: StackSwitchContinuation) -> ! {
        arm::switch_stack(to_sp, cont)
    }
}

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
impl ThreadContext for riscv::Context {
    fn init(&mut self) -> &mut Self {
        riscv::Context::init(self)
    }

    fn set_return_address(&mut self, address: usize) -> &mut Self {
        riscv::Context::set_return_address(self, address)
    }

    fn set_arg(&mut self, index: usize, value: usize) -> &mut Self {
        riscv::Context::set_arg(self, index, value)
    }
}

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
impl ArchInterface for KernelArch {
    type Context = riscv::Context;
    type IsrContext = riscv::IsrContext;

    fn disable_local_irq() {
        riscv::disable_local_irq();
    }

    fn enable_local_irq() {
        riscv::enable_local_irq();
    }

    fn disable_local_irq_save() -> IrqState {
        riscv::disable_local_irq_save()
    }

    fn enable_local_irq_restore(old: IrqState) {
        riscv::enable_local_irq_restore(old);
    }

    fn local_irq_enabled() -> bool {
        riscv::local_irq_enabled()
    }

    fn current_cpu_id() -> CpuId {
        riscv::current_cpu_id()
    }

    fn current_sp() -> usize {
        riscv::current_sp()
    }

    fn idle() {
        riscv::idle();
    }

    fn start_schedule(cont: ScheduleEntry) {
        riscv::start_schedule(cont);
    }

    fn pend_switch_context() {
        riscv::pend_switch_context();
    }

    fn switch_context_with_hook(hook: RawContextSwitchHook) {
        riscv::switch_context_with_hook(hook.cast());
    }

    fn restore_context_with_hook(hook: RawContextSwitchHook) -> ! {
        riscv::restore_context_with_hook(hook.cast())
    }

    fn switch_stack(to_sp: usize, cont: StackSwitchContinuation) -> ! {
        riscv::switch_stack(to_sp, cont)
    }
}

#[cfg(target_arch = "aarch64")]
impl ThreadContext for aarch64::Context {
    fn init(&mut self) -> &mut Self {
        aarch64::Context::init(self)
    }

    fn set_return_address(&mut self, address: usize) -> &mut Self {
        aarch64::Context::set_return_address(self, address)
    }

    fn set_arg(&mut self, index: usize, value: usize) -> &mut Self {
        aarch64::Context::set_arg(self, index, value)
    }
}

#[cfg(target_arch = "aarch64")]
impl ArchInterface for KernelArch {
    type Context = aarch64::Context;
    type IsrContext = aarch64::Context;

    fn disable_local_irq() {
        aarch64::disable_local_irq();
    }

    fn enable_local_irq() {
        aarch64::enable_local_irq();
    }

    fn disable_local_irq_save() -> IrqState {
        aarch64::disable_local_irq_save()
    }

    fn enable_local_irq_restore(old: IrqState) {
        aarch64::enable_local_irq_restore(old);
    }

    fn local_irq_enabled() -> bool {
        aarch64::local_irq_enabled()
    }

    fn current_cpu_id() -> CpuId {
        aarch64::current_cpu_id()
    }

    fn current_sp() -> usize {
        aarch64::current_sp()
    }

    fn idle() {
        aarch64::idle();
    }

    fn start_schedule(cont: ScheduleEntry) {
        aarch64::start_schedule(cont);
    }

    fn pend_switch_context() {
        aarch64::pend_switch_context();
    }

    fn switch_context_with_hook(hook: RawContextSwitchHook) {
        aarch64::switch_context_with_hook(hook.cast());
    }

    fn restore_context_with_hook(hook: RawContextSwitchHook) -> ! {
        aarch64::restore_context_with_hook(hook.cast())
    }

    fn switch_stack(to_sp: usize, cont: StackSwitchContinuation) -> ! {
        aarch64::switch_stack(to_sp, cont)
    }
}

pub(crate) type Context = <KernelArch as ArchInterface>::Context;
pub(crate) type IsrContext = <KernelArch as ArchInterface>::IsrContext;

#[inline]
pub extern "C" fn disable_local_irq() {
    <KernelArch as ArchInterface>::disable_local_irq();
}

#[inline]
pub extern "C" fn enable_local_irq() {
    <KernelArch as ArchInterface>::enable_local_irq();
}

#[inline]
pub extern "C" fn disable_local_irq_save() -> IrqState {
    <KernelArch as ArchInterface>::disable_local_irq_save()
}

#[inline]
pub extern "C" fn enable_local_irq_restore(old: IrqState) {
    <KernelArch as ArchInterface>::enable_local_irq_restore(old);
}

#[inline]
pub extern "C" fn local_irq_enabled() -> bool {
    <KernelArch as ArchInterface>::local_irq_enabled()
}

#[inline]
pub extern "C" fn current_cpu_id() -> CpuId {
    <KernelArch as ArchInterface>::current_cpu_id()
}

#[inline]
pub extern "C" fn current_sp() -> usize {
    <KernelArch as ArchInterface>::current_sp()
}

#[inline]
pub extern "C" fn idle() {
    <KernelArch as ArchInterface>::idle();
}

#[inline]
pub extern "C" fn start_schedule(cont: ScheduleEntry) {
    <KernelArch as ArchInterface>::start_schedule(cont);
}

#[inline]
pub extern "C" fn pend_switch_context() {
    <KernelArch as ArchInterface>::pend_switch_context();
}

#[inline]
pub(crate) extern "C" fn switch_context_with_hook(
    hook: *mut crate::scheduler::ContextSwitchHookHolder,
) {
    <KernelArch as ArchInterface>::switch_context_with_hook(hook.cast());
}

#[inline]
pub(crate) extern "C" fn restore_context_with_hook(
    hook: *mut crate::scheduler::ContextSwitchHookHolder,
) -> ! {
    <KernelArch as ArchInterface>::restore_context_with_hook(hook.cast())
}

#[inline]
pub(crate) extern "C" fn switch_stack(to_sp: usize, cont: StackSwitchContinuation) -> ! {
    <KernelArch as ArchInterface>::switch_stack(to_sp, cont)
}

#[cfg(target_arch = "arm")]
#[inline]
pub(crate) extern "C" fn send_ipi(id: usize) {
    arm::send_ipi(id);
}

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
#[inline]
pub(crate) extern "C" fn send_ipi(id: usize) {
    riscv::send_ipi(id);
}

#[cfg(target_arch = "aarch64")]
#[inline]
pub(crate) extern "C" fn send_ipi(id: usize) {
    aarch64::send_ipi(id);
}

#[no_mangle]
pub extern "C" fn blueos_kernel_handle_timer_tick() {
    #[cfg(target_arch = "arm")]
    {
        use blueos_hal::clock::Clock;
        if !crate::boards::ClockImpl::claim_interrupt() {
            return;
        }
    }
    crate::time::handle_clock_interrupt();
}

#[no_mangle]
pub extern "C" fn blueos_kernel_dispatch_syscall(req: *const SyscallRequest) -> usize {
    let req = unsafe { &*req };
    let ctx = crate::syscalls::Context {
        nr: req.nr,
        args: req.args,
    };
    crate::syscalls::dispatch_syscall(&ctx)
}

#[no_mangle]
pub extern "C" fn blueos_kernel_enter_irq() -> usize {
    crate::irq::enter_irq()
}

#[no_mangle]
pub extern "C" fn blueos_kernel_leave_irq() -> usize {
    crate::irq::leave_irq()
}

#[no_mangle]
pub extern "C" fn blueos_kernel_should_preempt_after_irq() -> bool {
    crate::scheduler::is_schedule_ready()
}

#[no_mangle]
pub extern "C" fn blueos_kernel_save_context_finish_hook(
    hook: RawContextSwitchHook,
    from_sp: usize,
) -> usize {
    let hook = unsafe { &mut *hook.cast::<crate::scheduler::ContextSwitchHookHolder>() };
    crate::scheduler::save_context_finish_hook(hook, from_sp)
}

#[no_mangle]
pub extern "C" fn blueos_kernel_relinquish_me_and_return_next_sp(old_sp: usize) -> usize {
    crate::scheduler::relinquish_me_and_return_next_sp(old_sp)
}

#[no_mangle]
pub extern "C" fn blueos_kernel_dispatch_external_irq(
    frame: RawExceptionFrame,
    cause: usize,
    value: usize,
) -> usize {
    #[cfg(all(any(target_arch = "riscv64", target_arch = "riscv32"), has_plic))]
    {
        // This mirrors the old RISC-V trap path: the arch crate owns trap
        // entry/dispatch now, but board-specific PLIC handling remains kernel
        // policy and still receives the saved RISC-V Context layout.
        let ctx = unsafe { &*frame.cast::<riscv::Context>() };
        crate::boards::handle_plic_irq(ctx, cause, value);
    }

    #[cfg(all(any(target_arch = "riscv64", target_arch = "riscv32"), not(has_plic)))]
    {
        // ESP32-C3-style boards use a non-PLIC interrupt controller. Keep the
        // same board callback shape as the original trap implementation while
        // the entry code lives in bluekernel_arch.
        let ctx = unsafe { &*frame.cast::<riscv::Context>() };
        crate::boards::handle_intc_irq(ctx, cause, value);
    }

    let _ = (frame, cause, value);
    0
}

#[no_mangle]
#[cfg(not(any(target_arch = "riscv64", target_arch = "riscv32")))]
pub extern "C" fn blueos_kernel_fatal_trap(
    frame: RawExceptionFrame,
    cause: usize,
    value: usize,
) -> ! {
    panic!(
        "Fatal architecture trap: frame={:?}, cause=0x{:x}, value=0x{:x}",
        frame, cause, value
    )
}

#[no_mangle]
#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
pub extern "C" fn blueos_kernel_fatal_trap(
    frame: RawExceptionFrame,
    cause: usize,
    value: usize,
) -> ! {
    // Preserve the old RISC-V panic payload even though trap entry moved into
    // bluekernel_arch. The raw frame has the same repr(C) Context layout until
    // Phase 4 moves context ownership.
    let ctx = unsafe { &*frame.cast::<riscv::Context>() };
    let thread = crate::scheduler::current_thread_ref();
    panic!(
        "[C#{}:0x{:x}] Unexpected trap: context: {:?}, mcause: 0x{:x}, mtval: 0x{:x}",
        riscv::current_cpu_id(),
        crate::thread::Thread::id(thread),
        ctx,
        cause,
        value
    );
}

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
#[no_mangle]
pub extern "C" fn blueos_kernel_clear_software_irq(cpu_id: usize) {
    crate::boards::clear_ipi(cpu_id);
}

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
#[no_mangle]
pub extern "C" fn blueos_kernel_riscv_handle_ecall_switch(
    frame: RawExceptionFrame,
    cont: usize,
) -> usize {
    riscv::handle_ecall_switch_from_raw(frame, cont)
}

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
#[no_mangle]
pub extern "C" fn blueos_kernel_riscv_might_switch_context(
    frame: RawExceptionFrame,
    cont: usize,
) -> usize {
    riscv::might_switch_context_from_raw(frame, cont)
}
