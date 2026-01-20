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
mod trap;

use crate::{irq as sysirq, scheduler, scheduler::ContextSwitchHookHolder};
use core::{
    cell::Cell,
    mem::offset_of,
    sync::atomic::{compiler_fence, Ordering},
};
pub use trap::*;

pub(crate) const NR_SWITCH: usize = !0;
const NUM_CORES: usize = blueos_kconfig::CONFIG_NUM_CORES as usize;
// See https://five-embeddev.com/riscv-priv-isa-manual/Priv-v1.12/machine.html#machine-status-registers-mstatus-and-mstatush
pub(crate) const MSTATUS_MIE: usize = 1 << 3;
pub(crate) const MSTATUS_MPIE: usize = 1 << 7;
pub(crate) const MSTATUS_MPP_MASK: usize = 0b11 << 11;
pub(crate) const MSTATUS_MPP_U: usize = 0b00 << 11;
pub(crate) const MSTATUS_MPP_S: usize = 0b01 << 11;
pub(crate) const MSTATUS_MPP_M: usize = 0b11 << 11;
pub(crate) const MIE_SSIE: usize = 1 << 1;
pub(crate) const MIE_MSIE: usize = 1 << 3;
pub(crate) const MIE_STIE: usize = 1 << 5;
pub(crate) const MIE_MTIE: usize = 1 << 7;
pub(crate) const MIE_SEIE: usize = 1 << 9;
pub(crate) const MIE_MEIE: usize = 1 << 11;
// We haven't supported supervisor mode and user mode yet.

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

#[inline]
pub(crate) extern "C" fn local_irq_enabled() -> bool {
    let x: usize;
    unsafe {
        core::arch::asm!("csrr {}, mstatus", out(reg) x,
                         options(nostack))
    };
    x & MSTATUS_MIE != 0
}

#[macro_export]
macro_rules! arch_bootstrap {
    ($stack_start:path, $stack_end:path, $cont: path) => {
        core::arch::naked_asm!(
            "csrci mstatus, 0x8",
            "la gp, __global_pointer$",
            "la sp, {stack_end}",
            "csrr t0, mhartid",
            "li t1, {stack_size}",
            "mul t0, t0, t1",
            "sub sp, sp, t0",
            "call {bootstrap}",
            "la t0, {cont}",
            "jalr x0, t0, 0",
            stack_size = const 0x1000,
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

macro_rules! clear_mstatus_mie {
    () => {
        "
        csrci mstatus, 0x8
        "
    };
}

macro_rules! set_mstatus_mie {
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
        ld t0, {mepc}(sp)
        csrw  mepc, t0
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
        lw t0, {mepc}(sp)
        csrw  mepc, t0
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
        "
    };
}

#[inline]
pub(crate) extern "C" fn disable_local_irq() {
    compiler_fence(Ordering::SeqCst);
    unsafe { core::arch::asm!(clear_mstatus_mie!(), options(nostack)) };
}

#[inline]
pub(crate) extern "C" fn enable_local_irq() {
    unsafe { core::arch::asm!(set_mstatus_mie!(), options(nostack)) };
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
                         bit = const MSTATUS_MIE,
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
#[derive(Default, Debug)]
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
    // So that it's 16-byte aligned.
    pub padding: usize,
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
        let gp_val: usize;
        unsafe {
            core::arch::asm!("la {}, __global_pointer$", out(reg) gp_val,
                             options(nostack, nomem))
        }
        self.gp = gp_val;
        self
    }

    // We are following C-ABI, since Rust ABI is not stablized.
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
    unsafe {
        core::arch::asm!(
            "csrs mstatus, {mstatus}",
            "csrs mie, {mie}",
            mstatus = in(reg) MSTATUS_MPP_M | MSTATUS_MPIE,
            mie = in(reg) MIE_MTIE|MIE_MSIE|MIE_MEIE,
            options(nostack),
        )
    };
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
    unsafe {
        core::arch::asm!("csrr {}, mhartid", out(reg) id,
                              options(nostack))
    };
    id
}

#[naked]
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
