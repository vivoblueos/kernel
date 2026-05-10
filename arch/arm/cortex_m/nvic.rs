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

//! Cortex-M Nested Vectored Interrupt Controller (NVIC) registers.
//!
//! This register block follows Arm CMSIS-Core's `NVIC_Type` layout:
//! <https://arm-software.github.io/CMSIS_6/main/Core/structNVIC__Type.html>
//!
//! The CMSIS layout defines eight 32-bit bitmap registers for interrupt
//! enable/pending/active state, 240 byte-wide priority registers, and the
//! software-trigger register at offset `0xE00`.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_structs,
    registers::{ReadWrite, WriteOnly},
};

/// Memory-mapped base address of the Nested Vectored Interrupt Controller.
const NVIC_BASE: usize = 0xE000_E100;

/// Maximum number of external interrupts described by the CMSIS NVIC register map.
pub const NUM_EXTERNAL_INTERRUPTS: usize = 240;

/// Number of 32-bit interrupt bitmap registers in the CMSIS NVIC register map.
const NUM_INTERRUPT_WORDS: usize = 8;

#[inline(always)]
const fn word_index(interrupt: u16) -> usize {
    interrupt as usize / u32::BITS as usize
}

#[inline(always)]
const fn bit_mask(interrupt: u16) -> u32 {
    1 << (interrupt % u32::BITS as u16)
}

#[inline(always)]
fn registers() -> &'static NvicRegisters {
    // Safety: NVIC is a core peripheral at a fixed architectural MMIO address.
    unsafe { &*(NVIC_BASE as *const NvicRegisters) }
}

/// Enables an external interrupt.
///
/// # Safety
///
/// Enabling an interrupt can break interrupt- or priority-based critical
/// sections if the caller has not installed a valid handler first.
#[inline(always)]
pub unsafe fn enable(interrupt: u16) {
    debug_assert!((interrupt as usize) < NUM_EXTERNAL_INTERRUPTS);

    // Safety: the debug assertion documents the expected architectural range;
    // out-of-range interrupt numbers are caller bugs just like raw NVIC access.
    unsafe {
        registers()
            .ISER
            .get_unchecked(word_index(interrupt))
            .set(bit_mask(interrupt));
    }
}

/// Disables an external interrupt.
///
/// # Safety
///
/// The caller must pass a valid external interrupt number for the target NVIC.
#[inline(always)]
pub unsafe fn disable(interrupt: u16) {
    debug_assert!((interrupt as usize) < NUM_EXTERNAL_INTERRUPTS);

    // Safety: writing ICER is a stateless one-bit command to the NVIC.
    unsafe {
        registers()
            .ICER
            .get_unchecked(word_index(interrupt))
            .set(bit_mask(interrupt));
    }
}

/// Returns whether an external interrupt is enabled.
///
/// # Safety
///
/// The caller must pass a valid external interrupt number for the target NVIC.
#[inline(always)]
pub unsafe fn is_enabled(interrupt: u16) -> bool {
    debug_assert!((interrupt as usize) < NUM_EXTERNAL_INTERRUPTS);

    // Safety: reading ISER has no side effects and uses the validated word index.
    unsafe {
        (registers().ISER.get_unchecked(word_index(interrupt)).get() & bit_mask(interrupt)) != 0
    }
}

/// Returns whether an external interrupt is active or preempted.
///
/// # Safety
///
/// The caller must pass a valid external interrupt number for the target NVIC.
#[inline(always)]
pub unsafe fn is_active(interrupt: u16) -> bool {
    debug_assert!((interrupt as usize) < NUM_EXTERNAL_INTERRUPTS);

    // Safety: reading IABR has no side effects and uses the validated word index.
    unsafe {
        (registers().IABR.get_unchecked(word_index(interrupt)).get() & bit_mask(interrupt)) != 0
    }
}

/// Returns whether an external interrupt is pending.
///
/// # Safety
///
/// The caller must pass a valid external interrupt number for the target NVIC.
#[inline(always)]
pub unsafe fn is_pending(interrupt: u16) -> bool {
    debug_assert!((interrupt as usize) < NUM_EXTERNAL_INTERRUPTS);

    // Safety: reading ISPR has no side effects and uses the validated word index.
    unsafe {
        (registers().ISPR.get_unchecked(word_index(interrupt)).get() & bit_mask(interrupt)) != 0
    }
}

/// Marks an external interrupt as pending.
///
/// # Safety
///
/// The caller must pass a valid external interrupt number for the target NVIC.
#[inline(always)]
pub unsafe fn pend(interrupt: u16) {
    debug_assert!((interrupt as usize) < NUM_EXTERNAL_INTERRUPTS);

    // Safety: writing ISPR is a stateless one-bit command to the NVIC.
    unsafe {
        registers()
            .ISPR
            .get_unchecked(word_index(interrupt))
            .set(bit_mask(interrupt));
    }
}

/// Clears an external interrupt's pending state.
///
/// # Safety
///
/// The caller must pass a valid external interrupt number for the target NVIC.
#[inline(always)]
pub unsafe fn unpend(interrupt: u16) {
    debug_assert!((interrupt as usize) < NUM_EXTERNAL_INTERRUPTS);

    // Safety: writing ICPR is a stateless one-bit command to the NVIC.
    unsafe {
        registers()
            .ICPR
            .get_unchecked(word_index(interrupt))
            .set(bit_mask(interrupt));
    }
}

/// Returns the encoded priority byte for an external interrupt.
///
/// # Safety
///
/// The caller must pass a valid external interrupt number for the target NVIC.
#[inline(always)]
pub unsafe fn get_priority(interrupt: u16) -> u8 {
    debug_assert!((interrupt as usize) < NUM_EXTERNAL_INTERRUPTS);

    // Safety: NVIC priorities are byte-addressable on the supported Cortex-M
    // profiles here, and the interrupt number indexes one priority byte.
    unsafe { registers().IPR.get_unchecked(interrupt as usize).get() }
}

/// Sets the encoded priority byte for an external interrupt.
///
/// Lower numerical values represent higher urgency. The value is written
/// directly because the NVIC stores only the implemented priority bits.
///
/// # Safety
///
/// Changing priorities can invalidate priority-based critical sections if the
/// caller does not preserve the kernel's priority invariants.
#[inline(always)]
pub unsafe fn set_priority(interrupt: u16, priority: u8) {
    debug_assert!((interrupt as usize) < NUM_EXTERNAL_INTERRUPTS);

    // Safety: see the function contract; the unchecked index avoids adding a
    // bounds check on the hot path while preserving the previous raw access.
    unsafe {
        registers()
            .IPR
            .get_unchecked(interrupt as usize)
            .set(priority);
    }
}

/// Requests an external interrupt through the software trigger register.
///
/// # Safety
///
/// The caller must pass a valid external interrupt number for the target NVIC.
#[inline(always)]
pub unsafe fn request(interrupt: u16) {
    debug_assert!((interrupt as usize) < NUM_EXTERNAL_INTERRUPTS);

    registers().STIR.set(u32::from(interrupt));
}

register_structs! {
    /// Cortex-M Nested Vectored Interrupt Controller register block.
    #[allow(non_snake_case)]
    NvicRegisters {
        /// Interrupt Set Enable Registers. Writing 1 enables the corresponding external interrupt.
        (0x000 => ISER: [ReadWrite<u32>; NUM_INTERRUPT_WORDS]),
        /// Reserved gap between the set-enable and clear-enable register banks.
        (0x020 => _reserved0),
        /// Interrupt Clear Enable Registers. Writing 1 disables the corresponding external interrupt.
        (0x080 => ICER: [ReadWrite<u32>; NUM_INTERRUPT_WORDS]),
        /// Reserved gap between the clear-enable and set-pending register banks.
        (0x0A0 => _reserved1),
        /// Interrupt Set Pending Registers. Writing 1 marks the corresponding external interrupt pending.
        (0x100 => ISPR: [ReadWrite<u32>; NUM_INTERRUPT_WORDS]),
        /// Reserved gap between the set-pending and clear-pending register banks.
        (0x120 => _reserved2),
        /// Interrupt Clear Pending Registers. Writing 1 clears the corresponding pending state.
        (0x180 => ICPR: [ReadWrite<u32>; NUM_INTERRUPT_WORDS]),
        /// Reserved gap between the clear-pending and active-bit register banks.
        (0x1A0 => _reserved3),
        /// Interrupt Active Bit Registers. A set bit means the corresponding interrupt is active.
        (0x200 => IABR: [ReadWrite<u32>; NUM_INTERRUPT_WORDS]),
        /// Reserved gap between the active-bit registers and priority byte registers.
        (0x220 => _reserved4),
        /// Interrupt Priority Registers. Each byte stores the priority for one external interrupt.
        (0x300 => IPR: [ReadWrite<u8>; NUM_EXTERNAL_INTERRUPTS]),
        /// Reserved gap between priority registers and the software-trigger register.
        (0x3F0 => _reserved5),
        /// Software Trigger Interrupt Register. Writing an interrupt ID pends that interrupt in software.
        (0xE00 => STIR: WriteOnly<u32>),
        (0xE04 => @END),
    }
}
