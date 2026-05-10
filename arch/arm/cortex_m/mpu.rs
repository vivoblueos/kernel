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

//! Cortex-M Memory Protection Unit (MPU) registers.
//!
//! This register block is based on Arm CMSIS-Core's `MPU_Type` layout:
//! <https://arm-software.github.io/CMSIS_6/main/Core/structMPU__Type.html>
//!
//! CMSIS documents the common MPU type/control/region registers. This module
//! exposes the ARMv8-M RBAR/RLAR path used by the kernel stack-guard setup.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_structs,
    registers::{ReadOnly, ReadWrite},
};

const MPU_BASE: usize = 0xE000_ED90;

#[inline(always)]
fn registers() -> &'static MpuRegisters {
    // Safety: MPU is a core peripheral at a fixed architectural MMIO address.
    unsafe { &*(MPU_BASE as *const MpuRegisters) }
}

/// Reads the MPU Control Register.
///
/// # Safety
///
/// The caller must run on a Cortex-M profile with an MPU at the architectural
/// address.
#[inline(always)]
pub unsafe fn control() -> u32 {
    registers().CTRL.get()
}

/// Writes the MPU Control Register.
///
/// # Safety
///
/// The caller must preserve MPU invariants required by the current memory map.
#[inline(always)]
pub unsafe fn set_control(value: u32) {
    registers().CTRL.set(value);
}

/// Programs an ARMv8-M MPU region through RNR/RBAR/RLAR.
///
/// # Safety
///
/// The caller must pass an architecturally valid region number and encoded
/// RBAR/RLAR values for the target MPU.
#[inline(always)]
pub unsafe fn set_region_v8m(region: u32, rbar: u32, rlar: u32) {
    let regs = registers();
    regs.RNR.set(region);
    regs.RBAR.set(rbar);
    regs.RLAR.set(rlar);
}

register_structs! {
    /// ARMv8-M MPU register block.
    #[allow(non_snake_case)]
    MpuRegisters {
        /// MPU Type Register.
        (0x000 => TYPE: ReadOnly<u32>),
        /// MPU Control Register.
        (0x004 => CTRL: ReadWrite<u32>),
        /// MPU Region Number Register.
        (0x008 => RNR: ReadWrite<u32>),
        /// MPU Region Base Address Register.
        (0x00C => RBAR: ReadWrite<u32>),
        /// MPU Region Limit Address Register.
        (0x010 => RLAR: ReadWrite<u32>),
        /// Alias registers and MAIR are not needed by the current kernel MPU setup.
        (0x014 => @END),
    }
}
