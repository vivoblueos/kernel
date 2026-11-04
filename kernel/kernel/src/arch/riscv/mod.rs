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

pub(crate) mod irq;
// Sv39 needs 64-bit registers; the 32-bit boards compile this module too,
// so the page-table half is gated on the target arch rather than a Kconfig.
#[cfg(target_arch = "riscv64")]
pub(crate) mod mmu;
mod pmp;
// The SBI shim: client calls from the kernel plus the firmware-side
// dispatch that today passes straight through to the board layer. Phase 0
// wires the encode/decode round-trip; Phase 1+ swaps the transport to
// `ecall` without touching either end. See S_MODE_MIGRATION.md.
pub(crate) mod sbi;
mod trap;

use crate::{boards, irq as sysirq, scheduler, scheduler::ContextSwitchHookHolder};
use core::{
    cell::Cell,
    mem::offset_of,
    sync::atomic::{compiler_fence, Ordering},
};
pub use trap::*;

pub(crate) const NR_SWITCH: usize = !0;
const NUM_CORES: usize = blueos_kconfig::CONFIG_NUM_CORES as usize;

// ---------------------------------------------------------------------------
// Privilege-level constants
// ---------------------------------------------------------------------------
//
// The kernel runs in **M-mode** on every supported RISC-V target. The trap
// entry, `enter_user` and the interrupt helpers all use `mstatus`/`mie`, so
// these positions are the machine-level ones on rv32 and rv64 alike.
//
// See https://five-embeddev.com/riscv-priv-isa-manual/Priv-v1.12/machine.html
pub(crate) mod priv_csr {
    /// `mstatus.MIE`: interrupts enabled at the current level.
    pub(crate) const STATUS_IE: usize = 1 << 3;
    /// `mstatus.MPIE`: what `MIE` is loaded from by `mret`.
    pub(crate) const STATUS_IE_PRIOR: usize = 1 << 7;
    /// `mstatus.MPP`, the two-bit previous-privilege field.
    pub(crate) const PP_MASK: usize = 0b11 << 11;
    /// The trap came from U-mode.
    pub(crate) const PP_U: usize = 0b00 << 11;
    /// The trap came from the kernel itself.
    pub(crate) const PP_KERNEL: usize = 0b11 << 11;
    pub(crate) const IE_TIMER: usize = 1 << 7;
    pub(crate) const IE_SOFT: usize = 1 << 3;
    pub(crate) const IE_EXTERN: usize = 1 << 11;
}

pub(crate) use priv_csr::*;

// FIXME: We don't need atomic here.
static mut PENDING_SWITCH_CONTEXT: [Cell<bool>; NUM_CORES] =
    [const { Cell::new(false) }; NUM_CORES];

#[inline]
pub(crate) extern "C" fn pend_switch_context() {
    if !sysirq::is_in_irq() {
        scheduler::relinquish_me();
        return;
    }
    let level = disable_local_irq_save();
    let id = current_cpu_id();
    unsafe { PENDING_SWITCH_CONTEXT[id].set(true) };
    enable_local_irq_restore(level);
}

#[inline]
pub(crate) extern "C" fn claim_switch_context() -> bool {
    let level = disable_local_irq_save();
    let id = current_cpu_id();
    let ok = unsafe { PENDING_SWITCH_CONTEXT[id].get() };
    unsafe { PENDING_SWITCH_CONTEXT[id].set(false) };
    enable_local_irq_restore(level);
    ok
}

/// The privilege level the trap came *from*, as encoded in `mstatus.MPP`.
///
/// Only meaningful inside a trap handler: outside one, the previous-privilege
/// field is whatever the next `mret` will restore, which is not necessarily
/// where we came from. Compared against [`PP_U`] it answers the one question
/// the handler needs — "was the code that trapped a user process?".
#[inline]
pub(crate) fn previous_privilege() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("csrr {}, mstatus", out(reg) x, options(nostack)) };
    x & PP_MASK
}

#[inline]
pub(crate) extern "C" fn local_irq_enabled() -> bool {
    let x: usize;
    unsafe { core::arch::asm!("csrr {}, mstatus", out(reg) x, options(nostack)) };
    x & STATUS_IE != 0
}

// Per-hart system stack size carved out in arch_bootstrap! below. Any value
// works: the naked bootstrap multiplies hart_id by it with a real mul.
//
// FIXME: ".option arch, +zmmul" in arch_bootstrap! is a temporary pass, not
// a fix. It forces the assembler to accept mul unconditionally, so on a
// RISC-V core without the M extension the emitted mul traps as an illegal
// instruction at boot. Every *-vivo-blueos target carries +m today, so this
// is safe here, but an M-less board would boot straight into a fault with
// no compile-time warning. Replace (power-of-two size + slli, or
// linker-provided per-hart stack symbols) before such a board lands.
//
// Why the pass is needed: the 1.96 toolchain (rustc 1.96.0-dev, LLVM 22)
// lowers naked_asm! to module-level assembly — the global_asm! path —
// instead of an inline-asm call inside the naked function. The integrated
// assembler validates module-level asm against the baseline ISA, blind to
// target features: +m is in our target spec, yet bare mul fails with
// "instruction requires the following: 'Zmmul'", and nothing reaches that
// validator (-Ctarget-feature=+m and -Cllvm-args=-mattr both fail;
// #[target_feature] is not allowed on naked functions). The old 1.84
// toolchain (LLVM 19) lowered naked_asm! to an in-function inline-asm call
// that inherited the function's target-features="+m,+a,+c" — the only
// reason mul used to compile there. Regular asm! and compiler-generated
// mul are unaffected on both. ".option push/pop" scopes the pass to this
// one mul.
//
// Upstream trail: rust-lang/rust#128004 (merged 2024-12-12, first in 1.85)
// moved naked functions onto the global-asm path; the feature blindness it
// introduced is rust-lang/rust#136280, and the fix — teaching naked
// functions their target features again — is rust-lang/rust#137720 (merged
// 2026-09-01, 13 days after this toolchain's 2026-08-19 snapshot). Once the
// toolchain rides past #137720, drop the .option pass and retry bare mul
// (fall back to #[target_feature(enable = "m")] if the target-spec features
// alone don't reach the validator — verify on the day).
pub const BOOT_STACK_SIZE: usize = 0x1000;
// The rv64 `arch_bootstrap!` derives each hart's stack offset with `slli t0, x, 12`,
// which hard-codes the shift for a 0x1000-byte stack. Guard that assumption so a
// future resize cannot silently produce overlapping per-hart stacks or an out-of-
// range shift immediate.
const _: () = assert!(
    BOOT_STACK_SIZE == 0x1000,
    "BOOT_STACK_SIZE must stay 0x1000: the rv64 arch_bootstrap! hard-codes `slli ..., 12`"
);

// Guard for the FIXME above: arch_bootstrap! emits a real mul, so a target
// without the M extension must fail the build instead of trapping at boot.
#[cfg(not(target_feature = "m"))]
compile_error!(
    "arch_bootstrap! uses mul; this target lacks the M extension (see FIXME at BOOT_STACK_SIZE)"
);

// Two entry points, both leaving the hart in **M-mode**. The kernel never
// delegates to S-mode: it does the machine-level bring-up (PMP, the trap CSRs,
// the timer/software-interrupt CSRs) itself and runs U-mode user processes
// directly under `mret`.
//
// * rv64 scales each hart's boot stack with a shift, which is exact because
//   `BOOT_STACK_SIZE` is a power of two and guarded by the assert above.
// * rv32 has no `slli`-friendly guarantee, so it emits a real `mul` behind the
//   `.option arch, +zmmul` pass described in the FIXME above.
//
// `tp` carries the hart id: the entry point reads `mhartid` into it, and
// [`current_cpu_id`] needs no CSR access to name the running hart.
#[cfg(target_arch = "riscv64")]
#[macro_export]
macro_rules! arch_bootstrap {
    ($stack_start:path, $stack_end:path, $cont: path) => {
        core::arch::naked_asm!(
            "csrci mstatus, 0x8",
            "la gp, __global_pointer$",
            "la sp, {stack_end}",
            "csrr t0, mhartid",
            "mv tp, t0",
            "slli t0, t0, 12",                   // BOOT_STACK_SIZE == 0x1000 (see assert above)
            "sub sp, sp, t0",
            "call {bootstrap}",
            "la t0, {cont}",
            "jalr x0, t0, 0",
            stack_end = sym $stack_end,
            bootstrap = sym $crate::arch::riscv::bootstrap,
            cont = sym $cont,
        );
    }
}

#[cfg(not(target_arch = "riscv64"))]
#[macro_export]
macro_rules! arch_bootstrap {
    ($stack_start:path, $stack_end:path, $cont: path) => {
        core::arch::naked_asm!(
            "csrci mstatus, 0x8",
            "la gp, __global_pointer$",
            "la sp, {stack_end}",
            "csrr t0, mhartid",
            ".option push",
            ".option arch, +zmmul",
            "li t1, {stack_size}",
            "mul t0, t0, t1",
            ".option pop",
            "sub sp, sp, t0",
            "call {bootstrap}",
            "la t0, {cont}",
            "jalr x0, t0, 0",
            stack_size = const $crate::arch::riscv::BOOT_STACK_SIZE,
            stack_end = sym $stack_end,
            bootstrap = sym $crate::arch::riscv::bootstrap,
            cont = sym $cont,
        );
    }
}

#[cfg(target_pointer_width = "64")]
#[macro_export]
macro_rules! rv_save_context_prologue {
    () => {
        "
        addi sp, sp, -{stack_size}
        sd ra, {ra}(sp)
        "
    };
}

#[cfg(target_pointer_width = "32")]
#[macro_export]
macro_rules! rv_save_context_prologue {
    () => {
        "
        addi sp, sp, -{stack_size}
        sw ra, {ra}(sp)
        "
    };
}

#[cfg(target_pointer_width = "64")]
#[macro_export]
macro_rules! rv_restore_context_epilogue {
    () => {
        "
        ld ra, {ra}(sp)
        addi sp, sp, {stack_size}
        "
    };
}

#[cfg(target_pointer_width = "32")]
#[macro_export]
macro_rules! rv_restore_context_epilogue {
    () => {
        "
        lw ra, {ra}(sp)
        addi sp, sp, {stack_size}
        "
    };
}

// Disable/enable the machine-mode interrupt enable bit. The kernel runs in
// M-mode on every target, so both the CSR name and the bit position are fixed.
macro_rules! clear_local_irq_bit {
    () => {
        "
        csrci mstatus, 0x8
        "
    };
}

macro_rules! set_local_irq_bit {
    () => {
        "
        csrsi mstatus, 0x8
        "
    };
}

#[cfg(target_pointer_width = "64")]
#[macro_export]
macro_rules! rv_restore_context {
    () => {
        "
        // Restore `mscratch` *first*: the return path swaps `sp` with it, so it
        // has to hold the user `sp` (U-mode return) or zero (M-mode return)
        // before the epilogue runs. `t1` is clobbered here only because the
        // very next block reloads it from the context anyway.
        ld t1, {mscratch}(sp)
        csrw mscratch, t1
        ld t0, {mepc}(sp)
        csrw  mepc, t0
        // Privilege is not in the register file, but it has to be restored
        // *with* it. `mret` takes the target mode from `mstatus.MPP`, and after
        // a context switch that field belongs to whichever thread trapped
        // **last** on this hart, not to the one being resumed. Left alone, a
        // kernel thread resumed right after a user thread's trap returns to
        // U-mode at a kernel address (illegal `csrr`, `mcause = 2`), and a user
        // thread resumed after a kernel trap returns to M-mode with its
        // untranslated user PC — both seen in the same boot before this fix.
        //
        // The discriminator is the context's own `mscratch`: nonzero means the
        // thread was in U-mode (it holds the user `sp` now, and the kernel
        // stack top before), zero means it was in the kernel. That is exactly
        // the test the `sp`/`mscratch` swap below performs, so the two blocks
        // cannot disagree.
        ld t0, {mscratch}(sp)
        li t1, {mpp_mask}
        beqz t0, 94f
        csrrc zero, mstatus, t1
        j 95f
        94:
        csrs mstatus, t1
        95:
        ld gp, {gp}(sp)
        ld tp, {tp}(sp)
        ld t0, {t0}(sp)
        ld t1, {t1}(sp)
        ld t2, {t2}(sp)
        ld t3, {t3}(sp)
        ld t4, {t4}(sp)
        ld t5, {t5}(sp)
        ld t6, {t6}(sp)
        ld a0, {a0}(sp)
        ld a1, {a1}(sp)
        ld a2, {a2}(sp)
        ld a3, {a3}(sp)
        ld a4, {a4}(sp)
        ld a5, {a5}(sp)
        ld a6, {a6}(sp)
        ld a7, {a7}(sp)
        ld fp, {fp}(sp)
        ld s1, {s1}(sp)
        ld s2, {s2}(sp)
        ld s3, {s3}(sp)
        ld s4, {s4}(sp)
        ld s5, {s5}(sp)
        ld s6, {s6}(sp)
        ld s7, {s7}(sp)
        ld s8, {s8}(sp)
        ld s9, {s9}(sp)
        ld s10, {s10}(sp)
        ld s11, {s11}(sp)
        "
    };
}

#[cfg(target_pointer_width = "32")]
#[macro_export]
macro_rules! rv_restore_context {
    () => {
        "
        // Same ordering as the 64-bit variant, and a no-op in practice: this
        // port never enters U-mode, so nothing but zero is ever parked in
        // `mscratch`. Keeping the sequence identical is what lets `trap_entry`
        // stay one piece of asm for both widths.
        lw t1, {mscratch}(sp)
        csrw mscratch, t1
        lw t0, {mepc}(sp)
        csrw  mepc, t0
        // Same privilege restore as the 64-bit variant. On this port nothing
        // ever writes a nonzero `mscratch`, so the branch always takes the
        // M-mode path and the sequence is a no-op — kept identical so
        // `trap_entry` stays one piece of asm for both widths.
        lw t0, {mscratch}(sp)
        li t1, {mpp_mask}
        beqz t0, 94f
        csrrc zero, mstatus, t1
        j 95f
        94:
        csrs mstatus, t1
        95:
        lw gp, {gp}(sp)
        lw tp, {tp}(sp)
        lw t0, {t0}(sp)
        lw t1, {t1}(sp)
        lw t2, {t2}(sp)
        lw t3, {t3}(sp)
        lw t4, {t4}(sp)
        lw t5, {t5}(sp)
        lw t6, {t6}(sp)
        lw a0, {a0}(sp)
        lw a1, {a1}(sp)
        lw a2, {a2}(sp)
        lw a3, {a3}(sp)
        lw a4, {a4}(sp)
        lw a5, {a5}(sp)
        lw a6, {a6}(sp)
        lw a7, {a7}(sp)
        lw fp, {fp}(sp)
        lw s1, {s1}(sp)
        lw s2, {s2}(sp)
        lw s3, {s3}(sp)
        lw s4, {s4}(sp)
        lw s5, {s5}(sp)
        lw s6, {s6}(sp)
        lw s7, {s7}(sp)
        lw s8, {s8}(sp)
        lw s9, {s9}(sp)
        lw s10, {s10}(sp)
        lw s11, {s11}(sp)
        "
    };
}

#[cfg(target_pointer_width = "64")]
#[macro_export]
macro_rules! rv_save_context {
    () => {
        "
        sd gp, {gp}(sp)
        sd tp, {tp}(sp)
        sd t0, {t0}(sp)
        sd t1, {t1}(sp)
        sd t2, {t2}(sp)
        sd t3, {t3}(sp)
        sd t4, {t4}(sp)
        sd t5, {t5}(sp)
        sd t6, {t6}(sp)
        sd a0, {a0}(sp)
        sd a1, {a1}(sp)
        sd a2, {a2}(sp)
        sd a3, {a3}(sp)
        sd a4, {a4}(sp)
        sd a5, {a5}(sp)
        sd a6, {a6}(sp)
        sd a7, {a7}(sp)
        sd fp, {fp}(sp)
        sd s1, {s1}(sp)
        sd s2, {s2}(sp)
        sd s3, {s3}(sp)
        sd s4, {s4}(sp)
        sd s5, {s5}(sp)
        sd s6, {s6}(sp)
        sd s7, {s7}(sp)
        sd s8, {s8}(sp)
        sd s9, {s9}(sp)
        sd s10, {s10}(sp)
        sd s11, {s11}(sp)
        csrr t0, mepc
        sd t0, {mepc}(sp)
        // Park the user `sp` (or zero, for an M-mode trap from the kernel) in
        // the context and leave `mscratch` clear. Clearing is what keeps a
        // *nested* trap — an interrupt taken while this handler is running —
        // from reading the stale user-sp value and swapping `sp` onto a user
        // stack.
        csrr t1, mscratch
        sd t1, {mscratch}(sp)
        csrw mscratch, zero
        "
    };
}

#[cfg(target_pointer_width = "32")]
#[macro_export]
macro_rules! rv_save_context {
    () => {
        "
        sw gp, {gp}(sp)
        sw tp, {tp}(sp)
        sw t0, {t0}(sp)
        sw t1, {t1}(sp)
        sw t2, {t2}(sp)
        sw t3, {t3}(sp)
        sw t4, {t4}(sp)
        sw t5, {t5}(sp)
        sw t6, {t6}(sp)
        sw a0, {a0}(sp)
        sw a1, {a1}(sp)
        sw a2, {a2}(sp)
        sw a3, {a3}(sp)
        sw a4, {a4}(sp)
        sw a5, {a5}(sp)
        sw a6, {a6}(sp)
        sw a7, {a7}(sp)
        sw fp, {fp}(sp)
        sw s1, {s1}(sp)
        sw s2, {s2}(sp)
        sw s3, {s3}(sp)
        sw s4, {s4}(sp)
        sw s5, {s5}(sp)
        sw s6, {s6}(sp)
        sw s7, {s7}(sp)
        sw s8, {s8}(sp)
        sw s9, {s9}(sp)
        sw s10, {s10}(sp)
        sw s11, {s11}(sp)
        csrr t0, mepc
        sw t0, {mepc}(sp)
        csrr t1, mscratch
        sw t1, {mscratch}(sp)
        csrw mscratch, zero
        "
    };
}

#[inline]
pub(crate) extern "C" fn disable_local_irq() {
    compiler_fence(Ordering::SeqCst);
    unsafe { core::arch::asm!(clear_local_irq_bit!(), options(nostack)) };
}

#[inline]
pub(crate) extern "C" fn enable_local_irq() {
    unsafe { core::arch::asm!(set_local_irq_bit!(), options(nostack)) };
    compiler_fence(Ordering::SeqCst);
}

#[inline]
pub(crate) extern "C" fn idle() {
    unsafe { core::arch::asm!("wfi", options(nostack)) };
}

#[inline]
pub(crate) extern "C" fn disable_local_irq_save() -> usize {
    compiler_fence(Ordering::SeqCst);
    let old: usize;
    unsafe {
        core::arch::asm!("csrrci {old}, mstatus, {bit}",
                         bit = const STATUS_IE,
                         old = out(reg) old,
                         options(nostack),
        )
    };
    old
}

#[inline]
pub(crate) extern "C" fn enable_local_irq_restore(old: usize) {
    unsafe {
        core::arch::asm!("csrw mstatus, {old}", old = in(reg) old,
                         options(nostack))
    };
    compiler_fence(Ordering::SeqCst);
}

#[inline]
pub extern "C" fn current_sp() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("mv {}, sp", out(reg) x, options(nostack, nomem)) };
    x
}

pub(crate) extern "C" fn ecall_switch_context_with_hook(hook: *mut ContextSwitchHookHolder) {
    unsafe {
        core::arch::asm!(
            "ecall",
            in("a0") hook as usize,
            in("a7") NR_SWITCH,
            options(nostack),
        )
    }
}

#[inline(always)]
pub(crate) extern "C" fn switch_context_with_hook(hook: *mut ContextSwitchHookHolder) {
    ecall_switch_context_with_hook(hook)
}

#[inline(always)]
#[allow(clippy::empty_loop)]
pub(crate) extern "C" fn restore_context_with_hook(hook: *mut ContextSwitchHookHolder) -> ! {
    switch_context_with_hook(hook);
    unreachable!("Should have switched to another thread");
}

// This context is used when we are performing context switching in
// thread mode or in the first level ISR.
#[cfg_attr(target_pointer_width = "64", repr(C, align(16)))]
#[cfg_attr(target_pointer_width = "32", repr(C, align(8)))]
#[derive(Default, Debug, Clone)]
pub(crate) struct Context {
    pub ra: usize,
    pub mepc: usize,
    pub gp: usize,
    pub tp: usize,
    pub t0: usize,
    pub t1: usize,
    pub t2: usize,
    pub fp: usize,
    pub a0: usize,
    pub a1: usize,
    pub a2: usize,
    pub a3: usize,
    pub a4: usize,
    pub a5: usize,
    pub a6: usize,
    pub a7: usize,
    pub t3: usize,
    pub t4: usize,
    pub t5: usize,
    pub t6: usize,
    pub s1: usize,
    pub s2: usize,
    pub s3: usize,
    pub s4: usize,
    pub s5: usize,
    pub s6: usize,
    pub s7: usize,
    pub s8: usize,
    pub s9: usize,
    pub s10: usize,
    pub s11: usize,
    /// The trap-time value of `mscratch`.
    ///
    /// Two different things live in that CSR depending on where the trap came
    /// from, and this field is what makes the difference recoverable after a
    /// context switch:
    ///
    /// - **U-mode trap**: `mscratch` held the top of this thread's *kernel*
    ///   stack, so the swap at the trap entry put the interrupted **user** `sp`
    ///   in its place. That user `sp` is saved here, because on the way back
    ///   out `sp` must become the user stack again — and if the scheduler
    ///   switches threads in between, the value can only come from here.
    /// - **M-mode trap**: `mscratch` is zero by convention, so this is zero,
    ///   and the return path keeps `sp` where it is.
    ///
    /// It occupies the slot that used to be pure padding: with it, the struct
    /// is still exactly 32 words / 256 bytes, so `size_of::<Context>()` stays
    /// 16-byte aligned and every `addi sp, sp, -{stack_size}` in the trap path
    /// keeps the stack aligned.
    pub mscratch: usize,
}

#[repr(C, align(16))]
#[derive(Default, Debug)]
pub(crate) struct IsrContext {
    pub mstatus: usize,
    pub mcause: usize,
    pub mtval: usize,
    pub mepc: usize,
}

impl Context {
    #[inline]
    pub(crate) fn init(&mut self) -> &mut Self {
        self.gp = Self::__global_pointer();
        self
    }

    #[inline]
    pub(crate) fn __global_pointer() -> usize {
        let gp_val: usize;
        unsafe {
            core::arch::asm!("la {}, __global_pointer$", out(reg) gp_val,
                             options(nostack, nomem))
        }
        gp_val
    }

    // We are following C-ABI, since Rust ABI is not stabilized.
    // FIXME: rustc miscompiles it if inlined.
    #[inline(never)]
    pub(crate) fn set_return_address(&mut self, pc: usize) -> &mut Self {
        self.mepc = pc;
        self
    }

    #[inline(never)]
    pub(crate) fn set_arg(&mut self, index: usize, val: usize) -> &mut Self {
        match index {
            0 => self.a0 = val,
            1 => self.a1 = val,
            2 => self.a2 = val,
            3 => self.a3 = val,
            4 => self.a4 = val,
            5 => self.a5 = val,
            6 => self.a6 = val,
            7 => self.a7 = val,
            _ => {}
        }
        self
    }
}

pub(crate) extern "C" fn bootstrap() {
    // PMP first: it is per-hart state, and `bootstrap` is the only code that is
    // guaranteed to run on every hart before the scheduler exists. Without it
    // the first U-mode fetch faults with `mcause = 1` no matter how correct the
    // page table is — see `pmp`'s module docs.
    //
    // SAFETY: early boot, single-threaded per hart, before any U-mode entry.
    unsafe { pmp::open_user_window() };

    #[cfg(has_mie)]
    unsafe {
        core::arch::asm!(
            "csrs mstatus, {mstatus}",
            "csrs mie, {mie}",
            mstatus = in(reg) PP_KERNEL | STATUS_IE_PRIOR,
            mie = in(reg) IE_TIMER | IE_SOFT | IE_EXTERN,
            options(nostack),
        )
    };
    #[cfg(not(has_mie))]
    unsafe {
        core::arch::asm!(
            "csrs mstatus, {mstatus}",
            mstatus = in(reg) PP_KERNEL | STATUS_IE_PRIOR,
            options(nostack),
        )
    };
}

// ---------------------------------------------------------------------------
// The user/kernel boundary
// ---------------------------------------------------------------------------
//
// Both entry points below end in `mret`, and both are only reachable when a
// page table is installed — i.e. on the 64-bit target. The 32-bit boards have
// no `mmu` module and no user processes, so the code is compiled out there.
#[cfg(target_pointer_width = "64")]
/// Drop into U-mode: install `satp` for the target address space and `mret` to
/// `entry` running on `user_sp`.
///
/// This is the user/kernel boundary of roadmap item #1. Everything after it is
/// translated by the page table named by `satp`, while the kernel itself keeps
/// running in M-mode, which is never translated and so is unaffected.
///
/// # Safety
///
/// - `satp` must be [`mmu::satp_sv39`] of a root table built by
///   [`mmu::new_root`].
/// - `entry` and `user_sp` must be addresses mapped by that table **with the
///   `U` bit set** — otherwise the first fetch or stack access faults.
/// - The caller must never return: there is no path back into the code that
///   called this.
pub(crate) unsafe extern "C" fn enter_user(satp: u64, entry: usize, user_sp: usize) -> ! {
    // Step 1: shape `mstatus` before the final, diverging `mret`.
    //
    // MPP = U, so `mret` lands in user mode. Cleared with the *register* form
    // on purpose: the CSR-immediate instructions only take a 5-bit uimm, far
    // too small for MSTATUS_MPP_MASK (0x1800). `mret` also loads MIE from MPIE,
    // so MPIE is set to keep interrupts alive in user mode — otherwise a user
    // process could never be preempted.
    //
    // This is a separate `asm!` block because it needs scratch registers, and
    // `options(noreturn)` forbids declaring any outputs. Doing it here means
    // the diverging block below needs *only* input operands.
    core::arch::asm!(
        "li {t}, {mpp_mask}",
        "csrrc {tmp}, mstatus, {t}",
        "li {t}, {mpie}",
        "csrs mstatus, {t}",
        t = out(reg) _,
        tmp = out(reg) _,
        mpp_mask = const PP_MASK,
        mpie = const STATUS_IE_PRIOR,
        options(nostack),
    );

    // Step 2: remember the kernel `sp` while it is still the current one. It is
    // handed to `mscratch` in the diverging block below; `csrw mscratch, reg`
    // takes any x-register, so no scratch is needed there either.
    let kernel_sp: usize;
    core::arch::asm!("mv {}, sp", out(reg) kernel_sp, options(nomem, nostack));

    // Step 3: the actual privilege switch. Never returns.
    //
    // Interrupts are masked for the whole block, and that is not decoration:
    // the block parks the kernel stack in `mscratch`, and `trap_entry` reads a
    // nonzero `mscratch` as "the interrupted thread was in U-mode". A timer
    // interrupt landing between `csrw mscratch` and `mret` would therefore be
    // filed as a user trap, with the user `sp` slot holding a kernel stack
    // pointer — the context would later be resumed in U-mode on kernel memory.
    // `mret` itself restores `MIE` from `MPIE`, which step 1 set, so U-mode
    // starts with interrupts enabled and nothing needs to re-enable them here.
    core::arch::asm!(
        "csrci mstatus, 0x8",
        // Installing satp must be ordered before the first fetch that is
        // translated through it.
        "csrw satp, {satp}",
        "sfence.vma zero, zero",
        "csrw mepc, {entry}",
        // Park the kernel stack in `mscratch` *while `sp` is still the kernel
        // one*: the first trap from user code swaps the two, so this is the
        // stack the kernel wakes up on, and the user `sp` is what gets parked
        // in its place. `sp` sits at or near the top of this thread's kernel
        // stack here and `trap_entry` grows downwards from whatever it finds in
        // `mscratch`, so the space below is unused by construction.
        //
        // Only the *first* entry into user mode needs this. Every later one
        // goes back through the trap return path, which leaves `mscratch`
        // holding the kernel stack top by itself.
        "csrw mscratch, {kernel_sp}",
        "mv sp, {usp}",
        "mret",
        satp = in(reg) satp,
        entry = in(reg) entry,
        kernel_sp = in(reg) kernel_sp,
        usp = in(reg) user_sp,
        options(noreturn),
    )
}

/// Enter U-mode with **every general-purpose register restored from a saved
/// trap frame** instead of starting a fresh program.
///
/// [`enter_user`] can only start an image at its entry point with a clean
/// register file — correct for `exec`, useless for `fork`, where the child must
/// resume at the instruction after the parent's `ecall` with the parent's
/// registers (except `a0`, which carries the "I am the child" zero).
///
/// The frame is a [`Context`] captured from the parent's trap. Two fields do
/// double duty and must be read in this order:
///
/// - `mepc` is where `mret` lands: the parent's return address, already advanced
///   past the `ecall`.
/// - `mscratch` is the saved **user** `sp`. On the way out it has to end up in
///   `mscratch` with the kernel stack top in `sp`, which is exactly what the
///   trap epilogue does — reproduced here because there is no trap to return
///   from on a thread's first entry into user mode.
///
/// `t0` is left holding the user stack pointer rather than the parent's value.
/// That is allowed: `t0` is caller-saved, so no caller may assume it survives a
/// syscall, and there is no free register left to stage the two stack pointers
/// through.
///
/// # Safety
/// `frame` must point at a live `Context` that stays mapped until `mret`, and
/// `satp` must name the address space its `mepc`/`mscratch` belong to.
#[cfg(target_pointer_width = "64")]
pub(crate) unsafe extern "C" fn enter_user_from_frame(frame: *const Context, satp: u64) -> ! {
    core::arch::asm!(
        "li {t}, {mpp_mask}",
        "csrrc {tmp}, mstatus, {t}",
        "li {t}, {mpie}",
        "csrs mstatus, {t}",
        t = out(reg) _,
        tmp = out(reg) _,
        mpp_mask = const PP_MASK,
        mpie = const STATUS_IE_PRIOR,
        options(nostack),
    );

    core::arch::asm!(
        // Same reason as in `enter_user`: `mscratch` is about to hold a kernel
        // stack pointer while the hart is still in M-mode, and an interrupt in
        // between would be misread as a user trap on the way out.
        "csrci mstatus, 0x8",
        "csrw satp, {satp}",
        "sfence.vma zero, zero",
        // `s0` doubles as the frame pointer for the whole restore; it is put
        // back from the frame as the very last load.
        "mv s0, {frame}",
        "ld t0, {mepc}(s0)",
        "csrw mepc, t0",
        "ld gp, {gp}(s0)",
        "ld tp, {tp}(s0)",
        "ld t1, {t1}(s0)",
        "ld t2, {t2}(s0)",
        "ld t3, {t3}(s0)",
        "ld t4, {t4}(s0)",
        "ld t5, {t5}(s0)",
        "ld t6, {t6}(s0)",
        "ld a0, {a0}(s0)",
        "ld a1, {a1}(s0)",
        "ld a2, {a2}(s0)",
        "ld a3, {a3}(s0)",
        "ld a4, {a4}(s0)",
        "ld a5, {a5}(s0)",
        "ld a6, {a6}(s0)",
        "ld a7, {a7}(s0)",
        "ld ra, {ra}(s0)",
        "ld s1, {s1}(s0)",
        "ld s2, {s2}(s0)",
        "ld s3, {s3}(s0)",
        "ld s4, {s4}(s0)",
        "ld s5, {s5}(s0)",
        "ld s6, {s6}(s0)",
        "ld s7, {s7}(s0)",
        "ld s8, {s8}(s0)",
        "ld s9, {s9}(s0)",
        "ld s10, {s10}(s0)",
        "ld s11, {s11}(s0)",
        // Park the kernel stack in `mscratch` and the user stack in `sp`,
        // mirroring the trap return path. After this the kernel stack is only
        // reachable through `mscratch`, which is where the next trap looks.
        "csrrw t0, mscratch, sp",
        "ld t0, {mscratch}(s0)",
        "mv sp, t0",
        "ld s0, {fp}(s0)",
        "mret",
        frame = in(reg) frame,
        satp = in(reg) satp,
        ra = const offset_of!(Context, ra),
        mepc = const offset_of!(Context, mepc),
        mscratch = const offset_of!(Context, mscratch),
        gp = const offset_of!(Context, gp),
        tp = const offset_of!(Context, tp),
        t1 = const offset_of!(Context, t1),
        t2 = const offset_of!(Context, t2),
        t3 = const offset_of!(Context, t3),
        t4 = const offset_of!(Context, t4),
        t5 = const offset_of!(Context, t5),
        t6 = const offset_of!(Context, t6),
        a0 = const offset_of!(Context, a0),
        a1 = const offset_of!(Context, a1),
        a2 = const offset_of!(Context, a2),
        a3 = const offset_of!(Context, a3),
        a4 = const offset_of!(Context, a4),
        a5 = const offset_of!(Context, a5),
        a6 = const offset_of!(Context, a6),
        a7 = const offset_of!(Context, a7),
        fp = const offset_of!(Context, fp),
        s1 = const offset_of!(Context, s1),
        s2 = const offset_of!(Context, s2),
        s3 = const offset_of!(Context, s3),
        s4 = const offset_of!(Context, s4),
        s5 = const offset_of!(Context, s5),
        s6 = const offset_of!(Context, s6),
        s7 = const offset_of!(Context, s7),
        s8 = const offset_of!(Context, s8),
        s9 = const offset_of!(Context, s9),
        s10 = const offset_of!(Context, s10),
        s11 = const offset_of!(Context, s11),
        options(noreturn),
    )
}

pub(crate) extern "C" fn start_schedule(cont: extern "C" fn() -> !) {
    let current = crate::scheduler::current_thread_ref();
    current.reset_saved_sp();
    let sp = current.saved_sp();
    unsafe {
        core::arch::asm!(
            "li ra, 0",
            "mv sp, {sp}",
            "jalr x0, {cont}, 0",
            sp = in(reg) sp,
            cont = in(reg) cont,
            options(noreturn),
        )
    }
}

#[inline(always)]
pub(crate) extern "C" fn current_cpu_id() -> usize {
    let id: usize;
    // All supported targets run the kernel in M-mode, where `mhartid` is a
    // readable CSR on every width. Reading it directly is what makes the id a
    // property of the *running hart* rather than of the thread: a thread's
    // saved `tp` is zeroed on creation (`Context::default`), so a context
    // restore would otherwise drop every hart to id 0 and make them share
    // `RUNNING_THREADS[0]` — the SMP corruption that shows up as an illegal
    // instruction in the scheduler on `-smp 32`.
    unsafe { core::arch::asm!("csrr {}, mhartid", out(reg) id, options(nostack)) };
    id
}

#[cfg_attr(compatible_old_toolchain, naked)]
#[cfg_attr(not(compatible_old_toolchain), unsafe(naked))]
pub(crate) extern "C" fn switch_stack(
    to_sp: usize,
    cont: extern "C" fn(sp: usize, old_sp: usize),
) -> ! {
    unsafe {
        core::arch::naked_asm!(
            "
            mv t0, a1
            mv a1, sp
            mv sp, a0
            jalr x0, t0, 0
            "
        )
    }
}

pub(crate) extern "C" fn send_ipi(hart: usize) {
    boards::send_ipi(hart);
}
