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

use blueos_hal::{
    uart::Uart, Configuration, Has8bitDataReg, HasFifo, HasInterruptReg, HasLineStatusReg, PlatPeri,
};
use core::{cell::UnsafeCell, fmt, ptr::NonNull};
use safe_mmio::{
    field,
    fields::{ReadOnly, ReadPure, ReadPureWrite, ReadWrite, WriteOnly},
    UniqueMmioPointer,
};

// Register description
// see: https://uart16550.readthedocs.io/en/latest/uart16550doc.html

// NS16550A resigter map(not complete)
#[repr(C)]
pub struct NS16550ARegisters {
    /// 0x000: Transmit Holding Register
    pub uartthr: WriteOnly<u8>,
    /// 0x001 - 0x004
    reserved_01: [u8; 4],
    /// 0x005: Line Status Register
    pub uartlsr: ReadOnly<u8>,
}

pub struct Ns16550a<'a> {
    pub regs: UnsafeCell<UniqueMmioPointer<'a, NS16550ARegisters>>,
}

impl Ns16550a<'_> {
    pub const fn new(base_addr: usize) -> Self {
        Ns16550a {
            regs: UnsafeCell::new(unsafe {
                UniqueMmioPointer::new(NonNull::new(base_addr as *mut NS16550ARegisters).unwrap())
            }),
        }
    }
}

macro_rules! field_used_by_inner {
    ($mmio_pointer:expr, $field:ident) => {{
        // Make sure $mmio_pointer is the right type.
        let mmio_pointer: &mut UniqueMmioPointer<_> = $mmio_pointer;
        // SAFETY: ptr_mut is guaranteed to return a valid pointer for MMIO, so the pointer to the
        // field must also be valid. MmioPointer::child gives it the same lifetime as the original
        // pointer.
        unsafe {
            let child_pointer =
                core::ptr::NonNull::new(&raw mut (*mmio_pointer.ptr_mut()).$field).unwrap();
            mmio_pointer.child(child_pointer)
        }
    }};
}

impl Configuration<super::UartConfig> for Ns16550a<'static> {
    type Target = ();
    fn configure(&self, _config: &super::UartConfig) -> blueos_hal::err::Result<()> {
        Ok(())
    }
}

impl Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus>
    for Ns16550a<'static>
{
}

impl Has8bitDataReg for Ns16550a<'static> {
    fn write_data8(&self, data: u8) {
        let unsafe_mut_ref = unsafe { &mut *self.regs.get() };
        field_used_by_inner!(unsafe_mut_ref, uartthr).write(data as u8);
    }
}

impl HasLineStatusReg for Ns16550a<'static> {}

impl HasFifo for Ns16550a<'static> {
    fn enable_fifo(&self, num: u8) -> blueos_hal::err::Result<()> {
        todo!()
    }

    fn is_tx_fifo_full(&self) -> bool {
        false
    }

    fn is_rx_fifo_empty(&self) -> bool {
        false
    }
}

impl HasInterruptReg for Ns16550a<'static> {
    type InterruptType = super::InterruptType;
    fn get_interrupt(&self) -> Self::InterruptType {
        Self::InterruptType::Unknown
    }
}

unsafe impl Send for Ns16550a<'static> {}
unsafe impl Sync for Ns16550a<'static> {}

impl PlatPeri for Ns16550a<'static> {}
