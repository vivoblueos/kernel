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

pub mod irq;

use core::{
    fmt,
    sync::atomic::{self, Ordering},
};

pub const EXCEPTION_LR: usize = 0xFFFFFFFD;
// See https://developer.arm.com/documentation/100235/0100/The-Cortex-M33-Processor/Programmer-s-model/Core-registers/CONTROL-register.
#[cfg(not(target_abi = "eabihf"))]
pub const CONTROL: usize = 0b10;
#[cfg(target_abi = "eabihf")]
pub const CONTROL: usize = 0b110;
pub const THUMB_MODE: usize = 0x01000000;
pub const NR_SWITCH: usize = !0;
pub const NR_RET_FROM_SYSCALL: usize = NR_SWITCH - 1;
pub const NR_DEBUG_SYSCALL: usize = NR_SWITCH - 2;
pub const DISABLE_LOCAL_IRQ_BASEPRI: u8 = irq::IRQ_PRIORITY_FOR_SCHEDULER;

#[macro_export]
macro_rules! arch_bootstrap {
    ($stack_start:expr, $stack_end:expr, $cont:path) => {
        core::arch::naked_asm!(
            "cpsid i",
            "b {cont}",
            cont = sym $cont,
        )
    };
}

macro_rules! disable_interrupt {
    () => {
        "
        cpsid i
        "
    };
}

macro_rules! enable_interrupt {
    () => {
        "
        cpsie i
        "
    };
}

// FIXME: We need to pass a scratch register to perform saving.
// Use r12 as scratch register now.
#[cfg(not(target_abi = "eabihf"))]
#[macro_export]
macro_rules! store_callee_saved_regs {
    () => {
        "
        mrs r12, psp
        stmdb r12!, {{r4-r11}}
        "
    };
}

#[cfg(not(target_abi = "eabihf"))]
#[macro_export]
macro_rules! load_callee_saved_regs {
    () => {
        "
        ldmia r12!, {{r4-r11}}
        msr psp, r12
        "
    };
}

#[cfg(target_abi = "eabihf")]
#[macro_export]
macro_rules! store_callee_saved_regs {
    () => {
        "
        mrs r12, psp
        vstmdb r12!, {{s16-s31}}
        stmdb r12!, {{r4-r11}}
        "
    };
}

#[cfg(target_abi = "eabihf")]
#[macro_export]
macro_rules! load_callee_saved_regs {
    () => {
        "
        ldmia r12!, {{r4-r11}}
        vldmia r12!, {{s16-s31}}
        msr psp, r12
        "
    };
}

#[cfg(not(target_abi = "eabihf"))]
#[repr(C, align(8))]
#[derive(Default, Debug, Copy, Clone)]
pub struct Context {
    pub r4: usize,
    pub r5: usize,
    pub r6: usize,
    pub r7: usize,
    pub r8: usize,
    pub r9: usize,
    pub r10: usize,
    pub r11: usize,
    // Cortex-m saves R0, R1, R2, R3, R12, LR, PC, xPSR automatically
    // on psp, so they don't appear in the Context. Additionally, sp
    // == R13, lr == R14, pc == R15.
    pub r0: usize,
    pub r1: usize,
    pub r2: usize,
    pub r3: usize,
    pub r12: usize,
    pub lr: usize,
    pub pc: usize,
    pub xpsr: usize,
}

#[cfg(target_abi = "eabihf")]
#[repr(C, align(8))]
#[derive(Default, Debug, Copy, Clone)]
pub struct Context {
    pub r4: usize,
    pub r5: usize,
    pub r6: usize,
    pub r7: usize,
    pub r8: usize,
    pub r9: usize,
    pub r10: usize,
    pub r11: usize,
    pub s16: usize,
    pub s17: usize,
    pub s18: usize,
    pub s19: usize,
    pub s20: usize,
    pub s21: usize,
    pub s22: usize,
    pub s23: usize,
    pub s24: usize,
    pub s25: usize,
    pub s26: usize,
    pub s27: usize,
    pub s28: usize,
    pub s29: usize,
    pub s30: usize,
    pub s31: usize,
    // Cortex-m saves R0, R1, R2, R3, R12, LR, PC, xPSR automatically
    // on psp, so they don't appear in the Context. Additionally, sp
    // == R13, lr == R14, pc == R15.
    pub r0: usize,
    pub r1: usize,
    pub r2: usize,
    pub r3: usize,
    pub r12: usize,
    pub lr: usize,
    pub pc: usize,
    pub xpsr: usize,
    pub s0: usize,
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
    pub s12: usize,
    pub s13: usize,
    pub s14: usize,
    pub s15: usize,
    pub fpscr: usize,
    pub vpr: usize,
}

#[cfg(not(target_abi = "eabihf"))]
#[repr(C, align(8))]
#[derive(Default)]
pub struct IsrContext {
    pub r0: usize,
    pub r1: usize,
    pub r2: usize,
    pub r3: usize,
    pub r12: usize,
    pub lr: usize,
    pub pc: usize,
    pub xpsr: usize,
}

// See https://developer.arm.com/documentation/107706/0100/Exceptions-and-interrupts-overview/Stack-frames.
#[cfg(target_abi = "eabihf")]
#[repr(C, align(8))]
#[derive(Default)]
pub struct IsrContext {
    pub r0: usize,
    pub r1: usize,
    pub r2: usize,
    pub r3: usize,
    pub r12: usize,
    pub lr: usize,
    pub pc: usize,
    pub xpsr: usize,
    pub s0: usize,
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
    pub s12: usize,
    pub s13: usize,
    pub s14: usize,
    pub s15: usize,
    pub fpscr: usize,
    pub vpr: usize,
}

impl fmt::Debug for IsrContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IsrContext {{")?;
        write!(f, "r0: 0x{:x} ", self.r0)?;
        write!(f, "r1: 0x{:x} ", self.r1)?;
        write!(f, "r2: 0x{:x} ", self.r2)?;
        write!(f, "r3: 0x{:x} ", self.r3)?;
        write!(f, "r12: 0x{:x} ", self.r12)?;
        write!(f, "lr: 0x{:x} ", self.lr)?;
        write!(f, "pc: 0x{:x} ", self.pc)?;
        write!(f, "xpsr: 0x{:x} ", self.xpsr)?;
        #[cfg(target_abi = "eabihf")]
        {
            write!(f, "fpscr: 0x{:x} ", self.fpscr)?;
            write!(f, "vpr: 0x{:x} ", self.vpr)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl Context {
    #[inline(never)]
    pub fn set_return_address(&mut self, pc: usize) -> &mut Self {
        self.pc = pc;
        self
    }

    #[inline]
    pub fn get_return_address(&self) -> usize {
        self.pc
    }

    #[inline]
    pub fn set_arg(&mut self, i: usize, val: usize) -> &mut Self {
        match i {
            0 => self.r0 = val,
            1 => self.r1 = val,
            2 => self.r2 = val,
            3 => self.r3 = val,
            _ => panic!("Should be passed by stack"),
        }
        self
    }

    #[cfg(not(target_abi = "eabihf"))]
    #[inline]
    pub fn init(&mut self) -> &mut Self {
        self.xpsr = THUMB_MODE;
        self
    }

    // See https://developer.arm.com/documentation/100235/0004/the-cortex-m33-peripherals/floating-point-unit/floating-point-status-control-register.
    #[cfg(target_abi = "eabihf")]
    #[inline]
    pub fn init(&mut self) -> &mut Self {
        self.xpsr = THUMB_MODE;
        self.fpscr = 1 << 25;
        self.vpr = 0xc0dec0de;
        self
    }
}

#[inline]
pub extern "C" fn enable_local_irq() {
    unsafe {
        core::arch::asm!(
            "msr basepri, {}",
            in(reg) 0,
            options(nostack)
        )
    }
}

#[inline]
pub extern "C" fn disable_local_irq() {
    unsafe {
        core::arch::asm!(
            "msr basepri, {}",
            "isb",
            in(reg) DISABLE_LOCAL_IRQ_BASEPRI,
            options(nostack),
        )
    }
}

#[inline(never)]
pub extern "C" fn disable_local_irq_save() -> usize {
    let old: usize;
    unsafe {
        core::arch::asm!(
            concat!(
                "
                mrs {old}, basepri
                msr basepri, {val}
                isb
                ",
            ),
            old = out(reg) old,
            val = in(reg) DISABLE_LOCAL_IRQ_BASEPRI,
            options(nostack)
        )
    }
    atomic::compiler_fence(Ordering::SeqCst);
    old
}

#[inline(never)]
pub extern "C" fn enable_local_irq_restore(old: usize) {
    atomic::compiler_fence(Ordering::SeqCst);
    unsafe {
        core::arch::asm!(
        "msr basepri, {}",
        in(reg) old,
        options(nostack))
    }
}

#[inline]
pub extern "C" fn idle() {
    unsafe { core::arch::asm!("wfi") }
}

#[inline]
pub extern "C" fn current_sp() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("mov {}, sp", out(reg) x, options(nostack, nomem)) };
    x
}

#[inline]
pub extern "C" fn current_msp() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("mrs {}, msp", out(reg) x, options(nostack, nomem)) };
    x
}

#[inline]
pub extern "C" fn current_psp() -> usize {
    let x: usize;
    unsafe { core::arch::asm!("mrs {}, psp", out(reg) x, options(nostack, nomem)) };
    x
}

#[naked]
pub extern "C" fn switch_stack(
    to_sp: usize,
    cont: extern "C" fn(sp: usize, old_sp: usize),
) -> ! {
    unsafe {
        core::arch::naked_asm!(
            "
            mov r12, r1
            mrs r1, psp
            msr psp, r0
            bx r12
            "
        )
    }
}

#[inline]
pub extern "C" fn current_cpu_id() -> usize {
    0
}

#[inline]
pub extern "C" fn local_irq_enabled() -> bool {
    let x: usize;
    unsafe {
        core::arch::asm!(
            "mrs {}, basepri",
            out(reg) x, options(nostack)
        );
    };
    x == 0
}

pub extern "C" fn send_ipi(_id: usize) {}