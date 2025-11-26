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

use crate::uart::{DataBits, Parity, StopBits};
use blueos_hal::{
    reset::ResetCtrl, uart::Uart, Configuration, Has8bitDataReg, HasFifo, HasInterruptReg,
    HasLineStatusReg, PlatPeri,
};
use core::cell::UnsafeCell;
use gd32e5::gd32e507::usart0;

pub struct Gd32e5xUart {
    // Note: Uart0~2 use the same register layout
    // but the situation may be different for other UART peripherals
    inner: u32,
    clk: u32,
    pub intr_handler: UnsafeCell<Option<&'static dyn Fn()>>,
    reset_id: u32,
    reset: &'static dyn ResetCtrl,
}

unsafe impl Send for Gd32e5xUart {}
unsafe impl Sync for Gd32e5xUart {}

impl Configuration<super::UartConfig> for Gd32e5xUart {
    type Target = ();
    fn configure(&self, param: &super::UartConfig) -> blueos_hal::err::Result<Self::Target> {
        let super::UartConfig {
            baudrate,
            parity,
            stop_bits,
            data_bits,
            flow_ctrl,
        } = param;

        self.reset.toggle(self.reset_id);

        let baudrate_div = self.clk / *baudrate;

        unsafe {
            self.regs()
                .baud()
                .modify(|_, w| unsafe { w.bits(baudrate_div) });

            match parity {
                Parity::None => {
                    self.regs()
                        .ctl0()
                        .modify(|_, w| w.pcen().clear_bit().wl().clear_bit());
                }
                Parity::Even => {
                    self.regs()
                        .ctl0()
                        .modify(|_, w| w.pcen().set_bit().wl().set_bit().pm().clear_bit());
                }
                Parity::Odd => {
                    self.regs()
                        .ctl0()
                        .modify(|_, w| w.pcen().set_bit().wl().set_bit().pm().set_bit());
                }
                _ => {
                    return Err(blueos_hal::err::HalError::InvalidParam);
                }
            }

            match stop_bits {
                StopBits::DataBits0_5 => {
                    self.regs().ctl1().modify(|_, w| w.stb().bits(0b01));
                }
                StopBits::DataBits1 => {
                    self.regs().ctl1().modify(|_, w| w.stb().bits(0b00));
                }
                StopBits::DataBits1_5 => {
                    self.regs().ctl1().modify(|_, w| w.stb().bits(0b11));
                }
                StopBits::DataBits2 => {
                    self.regs().ctl1().modify(|_, w| w.stb().bits(0b10));
                }
            }

            match data_bits {
                DataBits::DataBits8 => {
                    self.regs().ctl0().modify(|_, w| w.wl().clear_bit());
                }
                DataBits::DataBits9 => {
                    self.regs().ctl0().modify(|_, w| w.wl().set_bit());
                }
                _ => {
                    return Err(blueos_hal::err::HalError::InvalidParam);
                }
            }
        }

        Ok(())
    }
}

impl Gd32e5xUart {
    pub const fn new(uart: u32, clk: u32, reset: &'static dyn ResetCtrl, reset_id: u32) -> Self {
        Gd32e5xUart {
            inner: uart,
            clk,
            intr_handler: UnsafeCell::new(None),
            reset_id,
            reset,
        }
    }

    fn regs(&self) -> &usart0::RegisterBlock {
        unsafe { &*(self.inner as *const usart0::RegisterBlock) }
    }
}

impl Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus> for Gd32e5xUart {}

impl Has8bitDataReg for Gd32e5xUart {
    fn read_data8(&self) -> blueos_hal::err::Result<u8> {
        let stat0 = self.regs().stat0().read();
        if stat0.ferr().bit_is_set()
            || stat0.nerr().bit_is_set()
            || stat0.orerr().bit_is_set()
            || stat0.perr().bit_is_set()
        {
            return Err(blueos_hal::err::HalError::IoError);
        }

        Ok(self.regs().data().read().bits() as u8)
    }

    fn write_data8(&self, data: u8) {
        self.regs().data().write(|w| unsafe { w.bits(data as u32) });
    }

    fn is_data_ready(&self) -> bool {
        self.regs().stat0().read().rbne().bit_is_set()
    }
}

impl HasLineStatusReg for Gd32e5xUart {
    fn is_bus_busy(&self) -> bool {
        self.regs().stat1().read().bsy().bit_is_set()
    }
}

impl HasFifo for Gd32e5xUart {
    fn enable_fifo(&self, num: u8) -> blueos_hal::err::Result<()> {
        todo!()
    }

    fn is_tx_fifo_full(&self) -> bool {
        self.regs().stat0().read().tbe().bit_is_clear()
    }

    fn is_rx_fifo_empty(&self) -> bool {
        self.regs().stat0().read().rbne().bit_is_clear()
    }
}

impl HasInterruptReg for Gd32e5xUart {
    type InterruptType = super::InterruptType;

    fn enable_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Rx => {
                self.regs().ctl0().modify(|_, w| w.rbneie().set_bit());
            }
            super::InterruptType::Tx => {
                self.regs().ctl0().modify(|_, w| w.tcie().set_bit());
                self.regs().ctl0().modify(|_, w| w.tbeie().set_bit());
            }
            _ => {}
        }
    }

    fn disable_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Rx => {
                self.regs().ctl0().modify(|_, w| w.rbneie().clear_bit());
            }
            super::InterruptType::Tx => {
                self.regs().ctl0().modify(|_, w| w.tcie().clear_bit());
                self.regs().ctl0().modify(|_, w| w.tbeie().clear_bit());
            }
            _ => {}
        }
    }

    fn clear_interrupt(&self, intr: Self::InterruptType) {
        // Note: GD32E5x UART interrupt flags are cleared automatically
        match intr {
            super::InterruptType::Rx => {}
            super::InterruptType::Tx => {}
            _ => {}
        }
    }

    fn get_interrupt(&self) -> Self::InterruptType {
        if self.regs().ctl0().read().rbneie().bit_is_set()
            && self.regs().stat0().read().rbne().bit_is_set()
        {
            super::InterruptType::Rx
        } else if (self.regs().ctl0().read().tcie().bit_is_set()
            && self.regs().stat0().read().tc().bit_is_set())
            || (self.regs().ctl0().read().tbeie().bit_is_set()
                && self.regs().stat0().read().tbe().bit_is_set())
        {
            super::InterruptType::Tx
        } else {
            super::InterruptType::Unknown
        }
    }

    fn set_interrupt_handler(&self, handler: &'static dyn Fn()) {
        unsafe {
            *self.intr_handler.get() = Some(handler);
        }
    }

    fn get_irq_nums(&self) -> &[u32] {
        &[]
    }
}

impl PlatPeri for Gd32e5xUart {
    fn enable(&self) {
        self.regs()
            .ctl0()
            .modify(|_, w| w.uen().set_bit().ten().set_bit().ren().set_bit());
    }

    fn disable(&self) {
        self.regs()
            .ctl0()
            .modify(|_, w| w.uen().clear_bit().ten().clear_bit().ren().clear_bit());
    }
}
