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

//! Cortex-M HardFault entry and diagnostic helpers.
//!
//! HardFault handling is architecture-owned: Cortex-M records the active stack
//! frame through the EXC_RETURN value in LR, and the fault reason lives in SCB
//! status registers. This module keeps those mechanics and the default panic
//! diagnostic path in `bluekernel_arch`, so the kernel can re-export the entry
//! points without carrying Cortex-M register decoding logic.
//!
//! Arm references:
//! - HardFault status and configurable fault status registers:
//!   <https://developer.arm.com/documentation/ddi0403/latest/>
//! - Cortex-M exception stack frame selection through EXC_RETURN:
//!   <https://developer.arm.com/documentation/107706/0100/Exceptions-and-interrupts-overview/Stack-frames>

use crate::cortex_m::{disable_local_irq, exception::ExceptionStackFrame, scb, xpsr};
use core::fmt;

/// Snapshot of fault-status registers used when diagnosing a HardFault.
#[derive(Debug, Default, Clone, Copy)]
pub struct HardFaultRegs {
    cfsr: u32,
    hfsr: u32,
    mmfar: u32,
    bfar: u32,
    afsr: u32,
}

impl HardFaultRegs {
    /// Reads the SCB fault-status registers.
    ///
    /// # Safety
    ///
    /// The caller must run on a Cortex-M profile that implements the SCB fault
    /// status registers at the architectural addresses. Reading these
    /// registers is intended for fault handling or low-level diagnostics.
    #[inline(always)]
    pub unsafe fn read() -> Self {
        let fault_status = unsafe { scb::read_fault_status() };

        Self {
            cfsr: fault_status.cfsr,
            hfsr: fault_status.hfsr,
            mmfar: fault_status.mmfar,
            bfar: fault_status.bfar,
            afsr: fault_status.afsr,
        }
    }
}

impl fmt::Display for HardFaultRegs {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "\nHFSR: 0x{:08x}", self.hfsr)?;
        if self.hfsr & (1 << 30) != 0 {
            writeln!(f, "  - Forced Hard Fault")?;
        }
        if self.hfsr & (1 << 31) != 0 {
            writeln!(f, "  - Debug Event")?;
        }
        if self.hfsr & (1 << 1) != 0 {
            writeln!(f, "  - Vector Table Read Fault")?;
        }

        writeln!(f, "CFSR: 0x{:08x}", self.cfsr)?;
        writeln!(f, "Fault Status:")?;

        if self.cfsr & 0xFF != 0 {
            writeln!(f, "  Memory Management Fault:")?;
            if self.cfsr & (1 << 0) != 0 {
                writeln!(f, "    - Instruction access violation")?;
            }
            if self.cfsr & (1 << 1) != 0 {
                writeln!(f, "    - Data access violation")?;
            }
            if self.cfsr & (1 << 3) != 0 {
                writeln!(f, "    - Unstacking error")?;
            }
            if self.cfsr & (1 << 4) != 0 {
                writeln!(f, "    - Stacking error")?;
            }
            if self.cfsr & (1 << 5) != 0 {
                writeln!(f, "    - Lazy floating-point state preservation error")?;
            }
            if self.cfsr & (1 << 7) != 0 {
                writeln!(f, "    - MMFAR valid")?;
                writeln!(f, "      Fault Address: 0x{:08x}", self.mmfar)?;
            }
        }

        if self.cfsr & 0xFF00 != 0 {
            writeln!(f, "  Bus Fault:")?;
            if self.cfsr & (1 << 8) != 0 {
                writeln!(f, "    - Instruction bus error")?;
            }
            if self.cfsr & (1 << 9) != 0 {
                writeln!(f, "    - Precise error")?;
            }
            if self.cfsr & (1 << 10) != 0 {
                writeln!(f, "    - Imprecise error")?;
            }
            if self.cfsr & (1 << 11) != 0 {
                writeln!(f, "    - Unstack error")?;
            }
            if self.cfsr & (1 << 12) != 0 {
                writeln!(f, "    - Stacking error")?;
            }
            if self.cfsr & (1 << 13) != 0 {
                writeln!(f, "    - Lazy state preservation error")?;
            }
            if self.cfsr & (1 << 15) != 0 {
                writeln!(f, "    - BFAR valid")?;
                writeln!(f, "      Fault Address: 0x{:08x}", self.bfar)?;
            }
        }

        if self.cfsr & 0xFFFF0000 != 0 {
            writeln!(f, "  Usage Fault:")?;
            if self.cfsr & (1 << 16) != 0 {
                writeln!(f, "    - Undefined instruction")?;
            }
            if self.cfsr & (1 << 17) != 0 {
                writeln!(f, "    - Invalid state")?;
            }
            if self.cfsr & (1 << 18) != 0 {
                writeln!(f, "    - Invalid PC load")?;
            }
            if self.cfsr & (1 << 19) != 0 {
                writeln!(f, "    - No coprocessor")?;
            }
            #[cfg(armv8m)]
            if self.cfsr & (1 << 20) != 0 {
                writeln!(f, "    - Stack overflow")?;
            }
            if self.cfsr & (1 << 24) != 0 {
                writeln!(f, "    - Unaligned access")?;
            }
            if self.cfsr & (1 << 25) != 0 {
                writeln!(f, "    - Divide by zero")?;
            }
        }

        writeln!(f, "AFSR: 0x{:08x}", self.afsr)?;
        if self.afsr != 0 {
            writeln!(f, "  - Auxiliary Faults detected")?;
        }

        Ok(())
    }
}

/// Default HardFault panic callback.
///
/// This disables local interrupts, snapshots the Cortex-M fault registers and
/// xPSR, then panics with the stacked exception frame. It lives next to
/// [`handle_hardfault`] so the naked entry and the diagnostic register decoding
/// remain in the same architecture crate.
///
/// # Safety
///
/// `ctx` must point to the active Cortex-M exception stack frame selected by
/// the HardFault entry code. The function is intended to be called only from
/// [`handle_hardfault`] or equivalent low-level exception glue.
#[no_mangle]
pub unsafe extern "C" fn panic_on_hardfault(ctx: &ExceptionStackFrame) -> ! {
    disable_local_irq();
    let fault_regs = unsafe { HardFaultRegs::read() };
    let xpsr = unsafe { xpsr::read() };
    panic!(
        "
        ==== HARD FAULT ====
        FRAME: {:?}
        FAULT REGS: {}
        XPSR: {}
        ",
        ctx, fault_regs, xpsr,
    );
}

/// HardFault exception entry.
///
/// The entry code chooses MSP or PSP from EXC_RETURN bit 2 in LR and passes
/// the active hardware exception frame to [`panic_on_hardfault`].
///
/// # Safety
///
/// This function must be installed only as the Cortex-M HardFault handler.
#[naked]
#[no_mangle]
pub unsafe extern "C" fn handle_hardfault() {
    core::arch::naked_asm!(
        "
        mrs r0, msp
        tst lr, #0x04
        beq 1f
        mrs r0, psp
        1:
        bl {panic}
        ",
        panic = sym panic_on_hardfault
    )
}
