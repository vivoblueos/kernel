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

// pub(crate) mod asm;
// pub(crate) mod mmu;
mod exception;
pub mod irq;
pub(crate) mod psci;
pub(crate) mod registers;
pub(crate) mod vector;

use crate::{arch::registers::mpidr_el1::MPIDR_EL1, scheduler};
use core::{
    fmt,
    mem::offset_of,
    sync::{
        atomic,
        atomic::{AtomicU8, Ordering},
    },
};
use scheduler::ContextSwitchHookHolder;
use tock_registers::interfaces::Readable;

pub(crate) const NR_SWITCH: usize = !0;

macro_rules! disable_interrupt {
    () => {
        "
        msr daifset, #3
        "
    };
}

macro_rules! enable_interrupt {
    () => {
        "
        msr daifclr, #3
        "
    };
}

#[macro_export]
macro_rules! enter_el1 {
    () => {
        "
        mrs x0, cpacr_el1
        orr x0, x0, #(0x3 << 20)
        msr cpacr_el1, x0
        isb
        // Enable CNTP to EL1 for systick.
        mrs     x0, cnthctl_el2
        orr     x0, x0, #3
        msr     cnthctl_el2, x0
        msr     cntvoff_el2, xzr
        // Enable AArch64 in EL1.
        mov x0, #(1 << 31)
        orr x0, x0, #(1 << 1)
        msr hcr_el2, x0
        // Set EL1 sp and mask daif in EL2.
        mov x0, #0x3C5
        msr spsr_el2, x0
        // Set EL1 entry and enter.
        ldr x0, ={stack_start}
        ldr x1, ={stack_end}
        ldr x2, ={cont}
        adr x3, {entry}
        msr elr_el2, x3
        eret
        "
    };
}

#[macro_export]
macro_rules! arch_bootstrap {
    ($stack_start:path, $stack_end:path, $cont: path) => {
        core::arch::naked_asm!(
            $crate::enter_el1!(),
            entry = sym $crate::arch::aarch64::init,
            stack_start = sym $stack_start,
            stack_end = sym $stack_end,
            cont = sym $cont,
        )
    };
}

#[macro_export]
macro_rules! aarch64_save_context_prologue {
    () => {
        "
        sub sp, sp, #{stack_size}
        str lr, [sp, #{lr}]
        "
    };
}

#[macro_export]
macro_rules! aarch64_restore_context_epilogue {
    () => {
        "
        ldr lr, [sp, #{lr}]
        add sp, sp, #{stack_size}
        "
    };
}

#[macro_export]
macro_rules! aarch64_save_context {
    () => {
        "
        stp x0, x1, [sp, #{x0}]
        stp x2, x3, [sp, #{x2}]
        stp x4, x5, [sp, #{x4}]
        stp x6, x7, [sp, #{x6}]
        stp x8, x9, [sp, #{x8}]
        stp x10, x11, [sp, #{x10}]
        stp x12, x13, [sp, #{x12}]
        stp x14, x15, [sp, #{x14}]
        stp x16, x17, [sp, #{x16}]
        stp x18, x19, [sp, #{x18}]
        stp x20, x21, [sp, #{x20}]
        stp x22, x23, [sp, #{x22}]
        stp x24, x25, [sp, #{x24}]
        stp x26, x27, [sp, #{x26}]
        stp x28, x29, [sp, #{x28}]
        mrs x8, elr_el1
        str x8, [sp, #{elr}]
        mrs x8, spsr_el1
        str x8, [sp, #{spsr}]
        stp q0, q1, [sp, #{v0}]
        stp q2, q3, [sp, #{v2}]
        stp q4, q5, [sp, #{v4}]
        stp q6, q7, [sp, #{v6}]
        stp q8, q9, [sp, #{v8}]
        stp q10, q11, [sp, #{v10}]
        stp q12, q13, [sp, #{v12}]
        stp q14, q15, [sp, #{v14}]
        stp q16, q17, [sp, #{v16}]
        stp q18, q19, [sp, #{v18}]
        stp q20, q21, [sp, #{v20}]
        stp q22, q23, [sp, #{v22}]
        stp q24, q25, [sp, #{v24}]
        stp q26, q27, [sp, #{v26}]
        stp q28, q29, [sp, #{v28}]
        stp q30, q31, [sp, #{v30}]
        mrs x8, fpcr
        str x8, [sp, #{fpcr}]
        mrs x8, fpsr
        str x8, [sp, #{fpsr}]   
        "
    };
}

#[macro_export]
macro_rules! aarch64_restore_context {
    () => {
        "
        ldr x8, [sp, #{fpcr}]
        msr fpcr, x8
        ldr x8, [sp, #{fpsr}]
        msr fpsr, x8
        ldp q0, q1, [sp, #{v0}]
        ldp q2, q3, [sp, #{v2}]
        ldp q4, q5, [sp, #{v4}]
        ldp q6, q7, [sp, #{v6}]
        ldp q8, q9, [sp, #{v8}]
        ldp q10, q11, [sp, #{v10}]
        ldp q12, q13, [sp, #{v12}]
        ldp q14, q15, [sp, #{v14}]
        ldp q16, q17, [sp, #{v16}]
        ldp q18, q19, [sp, #{v18}]
        ldp q20, q21, [sp, #{v20}]
        ldp q22, q23, [sp, #{v22}]
        ldp q24, q25, [sp, #{v24}]
        ldp q26, q27, [sp, #{v26}]
        ldp q28, q29, [sp, #{v28}]
        ldp q30, q31, [sp, #{v30}]
        ldr x8, [sp, #{spsr}]
        and x9, x8, #~(1 << 7)
        msr spsr_el1, x9
        ldr x8, [sp, #{elr}]
        msr elr_el1, x8
        ldp x0, x1, [sp, #{x0}]
        ldp x2, x3, [sp, #{x2}]
        ldp x4, x5, [sp, #{x4}]
        ldp x6, x7, [sp, #{x6}]
        ldp x8, x9, [sp, #{x8}]
        ldp x10, x11, [sp, #{x10}]
        ldp x12, x13, [sp, #{x12}]
        ldp x14, x15, [sp, #{x14}]
        ldp x16, x17, [sp, #{x16}]
        ldp x18, x19, [sp, #{x18}]
        ldp x20, x21, [sp, #{x20}]
        ldp x22, x23, [sp, #{x22}]
        ldp x24, x25, [sp, #{x24}]
        ldp x26, x27, [sp, #{x26}]
        ldp x28, x29, [sp, #{x28}]
        "
    };
}

#[derive(Default, Debug)]
#[repr(C, align(16))]
pub struct Context {
    pub x0: usize,
    pub x1: usize,
    pub x2: usize,
    pub x3: usize,
    pub x4: usize,
    pub x5: usize,
    pub x6: usize,
    pub x7: usize,
    pub x8: usize,
    pub x9: usize,
    pub x10: usize,
    pub x11: usize,
    pub x12: usize,
    pub x13: usize,
    pub x14: usize,
    pub x15: usize,
    pub x16: usize,
    pub x17: usize,
    pub x18: usize,
    pub x19: usize,
    pub x20: usize,
    pub x21: usize,
    pub x22: usize,
    pub x23: usize,
    pub x24: usize,
    pub x25: usize,
    pub x26: usize,
    pub x27: usize,
    pub x28: usize,
    pub fp: usize, // x29
    pub lr: usize, // x30
    pub elr: usize,
    pub spsr: usize,
    pub padding: usize,
    pub v0: [u64; 2],
    pub v1: [u64; 2],
    pub v2: [u64; 2],
    pub v3: [u64; 2],
    pub v4: [u64; 2],
    pub v5: [u64; 2],
    pub v6: [u64; 2],
    pub v7: [u64; 2],
    pub v8: [u64; 2],
    pub v9: [u64; 2],
    pub v10: [u64; 2],
    pub v11: [u64; 2],
    pub v12: [u64; 2],
    pub v13: [u64; 2],
    pub v14: [u64; 2],
    pub v15: [u64; 2],
    pub v16: [u64; 2],
    pub v17: [u64; 2],
    pub v18: [u64; 2],
    pub v19: [u64; 2],
    pub v20: [u64; 2],
    pub v21: [u64; 2],
    pub v22: [u64; 2],
    pub v23: [u64; 2],
    pub v24: [u64; 2],
    pub v25: [u64; 2],
    pub v26: [u64; 2],
    pub v27: [u64; 2],
    pub v28: [u64; 2],
    pub v29: [u64; 2],
    pub v30: [u64; 2],
    pub v31: [u64; 2],
    pub fpcr: u64,
    pub fpsr: u64,
}

impl Context {
    #[inline]
    pub(crate) fn init(&mut self) -> &mut Self {
        self.spsr = 0b0101;
        self
    }

    // We are following C-ABI, since Rust ABI is not stablized.
    // FIXME: rustc miscompiles it if inlined.
    #[inline(never)]
    pub(crate) fn set_return_address(&mut self, lr: usize) -> &mut Self {
        self.elr = lr;
        self
    }

    #[inline]
    pub(crate) fn set_arg(&mut self, index: usize, val: usize) -> &mut Self {
        match index {
            0 => self.x0 = val,
            1 => self.x1 = val,
            2 => self.x2 = val,
            3 => self.x3 = val,
            4 => self.x4 = val,
            5 => self.x5 = val,
            6 => self.x6 = val,
            7 => self.x7 = val,
            _ => {}
        }
        self
    }

    pub(crate) fn set_return_value(&mut self, val: usize) -> &mut Self {
        self.x0 = val;
        self
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Context {{")?;
        write!(f, "x0: {:?}", self.x0)?;
        write!(f, "x1: {:?}", self.x1)?;
        write!(f, "x2: {:?}", self.x2)?;
        write!(f, "x3: {:?}", self.x3)?;
        write!(f, "x4: {:?}", self.x4)?;
        write!(f, "x5: {:?}", self.x5)?;
        write!(f, "x6: {:?}", self.x6)?;
        write!(f, "x7: {:?}", self.x7)?;
        write!(f, "x8: {:?}", self.x8)?;
        write!(f, "x9: {:?}", self.x9)?;
        write!(f, "x10: {:?}", self.x10)?;
        write!(f, "x11: {:?}", self.x11)?;
        write!(f, "x12: {:?}", self.x12)?;
        write!(f, "x13: {:?}", self.x13)?;
        write!(f, "x14: {:?}", self.x14)?;
        write!(f, "x15: {:?}", self.x15)?;
        write!(f, "x16: {:?}", self.x16)?;
        write!(f, "x17: {:?}", self.x17)?;
        write!(f, "x18: {:?}", self.x18)?;
        write!(f, "x19: {:?}", self.x19)?;
        write!(f, "x20: {:?}", self.x20)?;
        write!(f, "x21: {:?}", self.x21)?;
        write!(f, "x22: {:?}", self.x22)?;
        write!(f, "x23: {:?}", self.x23)?;
        write!(f, "x24: {:?}", self.x24)?;
        write!(f, "x25: {:?}", self.x25)?;
        write!(f, "x26: {:?}", self.x26)?;
        write!(f, "x27: {:?}", self.x27)?;
        write!(f, "x28: {:?}", self.x28)?;
        write!(f, "fp: {:?}", self.fp)?;
        write!(f, "lr: {:?}", self.lr)?;
        write!(f, "elr: {:?}", self.elr)?;
        write!(f, "spsr: {:?}", self.spsr)?;
        write!(f, "v0: {:?}", self.v0)?;
        write!(f, "v1: {:?}", self.v1)?;
        write!(f, "v2: {:?}", self.v2)?;
        write!(f, "v3: {:?}", self.v3)?;
        write!(f, "v4: {:?}", self.v4)?;
        write!(f, "v5: {:?}", self.v5)?;
        write!(f, "v6: {:?}", self.v6)?;
        write!(f, "v7: {:?}", self.v7)?;
        write!(f, "v8: {:?}", self.v8)?;
        write!(f, "v9: {:?}", self.v9)?;
        write!(f, "v10: {:?}", self.v10)?;
        write!(f, "v11: {:?}", self.v11)?;
        write!(f, "v12: {:?}", self.v12)?;
        write!(f, "v13: {:?}", self.v13)?;
        write!(f, "v14: {:?}", self.v14)?;
        write!(f, "v15: {:?}", self.v15)?;
        write!(f, "v16: {:?}", self.v16)?;
        write!(f, "v17: {:?}", self.v17)?;
        write!(f, "v18: {:?}", self.v18)?;
        write!(f, "v19: {:?}", self.v19)?;
        write!(f, "v20: {:?}", self.v20)?;
        write!(f, "v21: {:?}", self.v21)?;
        write!(f, "v22: {:?}", self.v22)?;
        write!(f, "v23: {:?}", self.v23)?;
        write!(f, "v24: {:?}", self.v24)?;
        write!(f, "v25: {:?}", self.v25)?;
        write!(f, "v26: {:?}", self.v26)?;
        write!(f, "v27: {:?}", self.v27)?;
        write!(f, "v28: {:?}", self.v28)?;
        write!(f, "v29: {:?}", self.v29)?;
        write!(f, "v30: {:?}", self.v30)?;
        write!(f, "v31: {:?}", self.v31)?;
        write!(f, "fpcr: {:?}", self.fpcr)?;
        write!(f, "fpsr: {:?}", self.fpsr)?;
        write!(f, "}}")
    }
}

// FIXME: Use counter to record ISR level.
pub(crate) extern "C" fn is_in_interrupt() -> bool {
    false
}

#[inline(always)]
#[allow(clippy::empty_loop)]
pub(crate) extern "C" fn restore_context_with_hook(hook: *mut ContextSwitchHookHolder) -> ! {
    switch_context_with_hook(hook);
    loop {}
}

#[inline(never)]
pub(crate) extern "C" fn svc_switch_context_with_hook(hook: *mut ContextSwitchHookHolder) {
    unsafe {
        core::arch::asm!(
            "svc #0",
            in("x0") hook as usize,
            in("x8") NR_SWITCH,
            options(nostack),
        )
    }
}

#[inline]
pub(crate) extern "C" fn switch_context_with_hook(hook: *mut ContextSwitchHookHolder) {
    svc_switch_context_with_hook(hook)
}

#[naked]
pub(crate) extern "C" fn init() -> ! {
    unsafe {
        core::arch::naked_asm!(
            "
                mrs x8, mpidr_el1
                and x8, x8, #0Xff
                lsl x8, x8, #14
                sub sp, x1, x8 
                br x2
            "
        )
    }
}

#[no_mangle]
pub(crate) extern "C" fn start_schedule(cont: extern "C" fn() -> !) {
    let current = crate::scheduler::current_thread_ref();
    current.reset_saved_sp();
    let sp = current.saved_sp();
    unsafe {
        core::arch::asm!(
            "mov lr, #0",
            "mov sp, {sp}",
            "br {cont}",
            sp = in(reg) sp,
            cont = in(reg) cont,
            options(noreturn),
        )
    }
}

#[inline]
pub extern "C" fn disable_local_irq() {
    unsafe { core::arch::asm!("msr daifset, #3", options(nostack, nomem)) }
}

#[inline]
pub extern "C" fn enable_local_irq() {
    unsafe { core::arch::asm!("msr daifclr, #3", options(nostack, nomem)) }
}

#[inline]
pub extern "C" fn current_cpu_id() -> usize {
    (MPIDR_EL1.get() & 0xff) as usize
}

#[inline(always)]
pub(crate) extern "C" fn idle() {
    unsafe { core::arch::asm!("wfi", options(nostack)) };
}

#[inline]
pub extern "C" fn current_sp() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("mov {}, sp", out(reg) x, options(nostack, nomem)) };
    x
}

#[inline]
pub extern "C" fn disable_local_irq_save() -> usize {
    let old: usize;
    unsafe {
        core::arch::asm!(
            concat!(
                "mrs {}, daif",
                disable_interrupt!(),
            ),
            out(reg) old, options(nostack)
        )
    }
    atomic::compiler_fence(Ordering::SeqCst);
    old
}

#[inline]
pub extern "C" fn enable_local_irq_restore(old: usize) {
    atomic::compiler_fence(Ordering::SeqCst);
    unsafe { core::arch::asm!("msr daif, {}", in(reg) old, options(nostack)) }
}

#[inline]
pub extern "C" fn local_irq_enabled() -> bool {
    let x: usize;
    unsafe {
        core::arch::asm!(
            "mrs {}, daif",
            out(reg) x, options(nostack)
        );
    };
    (x & (1 << 7)) == 0
}

#[inline]
pub extern "C" fn pend_switch_context() {}

pub fn secondary_cpu_setup(psci_base: u32) {
    atomic::fence(Ordering::SeqCst);
    for i in 1..blueos_kconfig::CONFIG_NUM_CORES {
        psci::cpu_on(psci_base, i as usize, crate::boot::_start as usize, 0);
    }
}

#[naked]
pub(crate) extern "C" fn switch_stack(
    to_sp: usize,
    cont: extern "C" fn(sp: usize, old_sp: usize),
) -> ! {
    unsafe {
        core::arch::naked_asm!(
            "
            mov x19, x1
            mov x1, sp
            mov sp, x0
            br x19
            "
        )
    }
}
