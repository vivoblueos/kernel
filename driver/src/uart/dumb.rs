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

use blueos_hal::{
    uart::Uart, Configuration, Has8bitDataReg, HasFifo, HasInterruptReg, HasLineStatusReg, PlatPeri,
};

pub struct DumbUart;

unsafe impl Send for DumbUart {}
unsafe impl Sync for DumbUart {}

impl Configuration<super::UartConfig> for DumbUart {
    type Target = ();
    fn configure(&self, _config: &super::UartConfig) -> blueos_hal::err::Result<()> {
        Ok(())
    }
}

impl Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus> for DumbUart {}

impl Has8bitDataReg for DumbUart {
    fn read_data8(&self) -> blueos_hal::err::Result<u8> {
        Ok(0u8)
    }

    fn write_data8(&self, data: u8) {
        let _ = data;
    }

    fn is_data_ready(&self) -> bool {
        true
    }
}

impl HasLineStatusReg for DumbUart {
    fn is_bus_busy(&self) -> bool {
        false
    }
}

impl HasFifo for DumbUart {
    fn enable_fifo(&self, _num: u8) -> blueos_hal::err::Result<()> {
        Ok(())
    }

    fn is_tx_fifo_full(&self) -> bool {
        false
    }

    fn is_rx_fifo_empty(&self) -> bool {
        false
    }
}

impl HasInterruptReg for DumbUart {
    type InterruptType = super::InterruptType;

    fn enable_interrupt(&self, intr: Self::InterruptType) {
        let _ = intr;
    }

    fn disable_interrupt(&self, intr: Self::InterruptType) {
        let _ = intr;
    }

    fn clear_interrupt(&self, intr: Self::InterruptType) {
        let _ = intr;
    }

    fn get_interrupt(&self) -> Self::InterruptType {
        super::InterruptType::Unknown
    }

    fn set_interrupt_handler(&self, handler: &'static dyn Fn()) {
        let _ = handler;
    }

    fn get_irq_nums(&self) -> &[u32] {
        &[]
    }
}

impl PlatPeri for DumbUart {
    fn enable(&self) {}

    fn disable(&self) {}
}
