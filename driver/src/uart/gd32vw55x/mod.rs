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

macro_rules! usart_regidx_bit {
    ($regidx:expr, $bitops:expr) => {
        (($regidx << 6) | $bitops)
    };
}

macro_rules! usart_regidx_bit2 {
    ($regidx:expr, $bitpos:expr, $regidx2:expr, $bitpos2:expr) => {
        ($regidx2 << 22) | (($bitpos2 << 16) as u32) | (($regidx << 6) | ($bitpos as u32))
    };
}

macro_rules! bit {
    ($x:expr) => {
        (1u32 << $x)
    };
}

macro_rules! bits {
    ($start:expr, $end:expr) => {
        (0xFFFFFFFF << $start) & (0xFFFFFFFF >> (31 - $end))
    };
}

macro_rules! ctl0_pm {
    ($reg:expr) => {
        (bits!(9, 10) & (($reg as u32) << 9))
    };
}

macro_rules! ctl0_wl {
    ($reg:expr) => {
        bit!(12) & (($reg as u32) << 12)
    };
}

macro_rules! ctl1_stb {
    ($reg:expr) => {
        (bits!(12, 13) & (($reg as u32) << 12))
    };
}

macro_rules! ctl0_ren {
    ($reg:expr) => {
        bit!(2) & (($reg as u32) << 2)
    };
}

macro_rules! ctl0_ten {
    ($reg:expr) => {
        bit!(3) & (($reg as u32) << 3)
    };
}

const USART_CTL0_REG_OFFSET: u32 = 0x0000_0000;
const USART_CTL1_REG_OFFSET: u32 = 0x0000_0004;
const USART_CTL2_REG_OFFSET: u32 = 0x0000_0008;

const USART_TRANSMIT_ENABLE: u32 = ctl0_ten!(1);
const USART_TRANSMIT_DISABLE: u32 = ctl0_ten!(0);

const USART_RECEIVE_ENABLE: u32 = ctl0_ren!(1);
const USART_RECEIVE_DISABLE: u32 = ctl0_ren!(0);

const USART_WL_8BIT: u32 = ctl0_wl!(0);
const USART_WL_9BIT: u32 = ctl0_wl!(1);

const USART_STB_1BIT: u32 = ctl1_stb!(0);
const USART_STB_0_5BIT: u32 = ctl1_stb!(1);
const USART_STB_2BIT: u32 = ctl1_stb!(2);
const USART_STB_1_5BIT: u32 = ctl1_stb!(3);

const USART_PM_NONE: u32 = ctl0_pm!(0);
const USART_PM_ODD: u32 = ctl0_pm!(2);
const USART_PM_EVEN: u32 = ctl0_pm!(3);

const USART_STAT_REG_OFFSET: u32 = 0x0000_001C;
const USART_CHC_REG_OFFSET: u32 = 0x000000C0;
const USART_RFCS_REG_OFFSET: u32 = 0x000000D0;

#[repr(u32)]
enum UsartFlag {
    REA = usart_regidx_bit!(USART_STAT_REG_OFFSET, 22),
    TEA = usart_regidx_bit!(USART_STAT_REG_OFFSET, 21),
    WU = usart_regidx_bit!(USART_STAT_REG_OFFSET, 20),
    RWU = usart_regidx_bit!(USART_STAT_REG_OFFSET, 19),
    SB = usart_regidx_bit!(USART_STAT_REG_OFFSET, 18),
    AM = usart_regidx_bit!(USART_STAT_REG_OFFSET, 17),
    BSY = usart_regidx_bit!(USART_STAT_REG_OFFSET, 16),
    EB = usart_regidx_bit!(USART_STAT_REG_OFFSET, 12),
    RT = usart_regidx_bit!(USART_STAT_REG_OFFSET, 11),
    CTS = usart_regidx_bit!(USART_STAT_REG_OFFSET, 10),
    CTSF = usart_regidx_bit!(USART_STAT_REG_OFFSET, 9),
    LBD = usart_regidx_bit!(USART_STAT_REG_OFFSET, 8),
    TBE = usart_regidx_bit!(USART_STAT_REG_OFFSET, 7),
    TC = usart_regidx_bit!(USART_STAT_REG_OFFSET, 6),
    RBNE = usart_regidx_bit!(USART_STAT_REG_OFFSET, 5),
    IDLE = usart_regidx_bit!(USART_STAT_REG_OFFSET, 4),
    ORERR = usart_regidx_bit!(USART_STAT_REG_OFFSET, 3),
    NERR = usart_regidx_bit!(USART_STAT_REG_OFFSET, 2),
    FERR = usart_regidx_bit!(USART_STAT_REG_OFFSET, 1),
    PERR = usart_regidx_bit!(USART_STAT_REG_OFFSET, 0),
    EPERR = usart_regidx_bit!(USART_CHC_REG_OFFSET, 8),
    RFFINT = usart_regidx_bit!(USART_RFCS_REG_OFFSET, 15),
    RFF = usart_regidx_bit!(USART_RFCS_REG_OFFSET, 11),
    RFE = usart_regidx_bit!(USART_RFCS_REG_OFFSET, 10),
}

#[allow(non_camel_case_types)]
#[repr(u32)]
enum UsartInterruptFlag {
    EB = usart_regidx_bit2!(USART_CTL0_REG_OFFSET, 27, USART_STAT_REG_OFFSET, 12),
    RT = usart_regidx_bit2!(USART_CTL0_REG_OFFSET, 26, USART_STAT_REG_OFFSET, 11),
    AM = usart_regidx_bit2!(USART_CTL0_REG_OFFSET, 14, USART_STAT_REG_OFFSET, 17),
    PERR = usart_regidx_bit2!(USART_CTL0_REG_OFFSET, 8, USART_STAT_REG_OFFSET, 0),
    TBE = usart_regidx_bit2!(USART_CTL0_REG_OFFSET, 7, USART_STAT_REG_OFFSET, 7),
    TC = usart_regidx_bit2!(USART_CTL0_REG_OFFSET, 6, USART_STAT_REG_OFFSET, 6),
    RBNE = usart_regidx_bit2!(USART_CTL0_REG_OFFSET, 5, USART_STAT_REG_OFFSET, 5),
    RBNE_ORERR = usart_regidx_bit2!(USART_CTL0_REG_OFFSET, 5, USART_STAT_REG_OFFSET, 3),
    IDLE = usart_regidx_bit2!(USART_CTL0_REG_OFFSET, 4, USART_STAT_REG_OFFSET, 4),
    LBD = usart_regidx_bit2!(USART_CTL1_REG_OFFSET, 6, USART_STAT_REG_OFFSET, 8),
    WU = usart_regidx_bit2!(USART_CTL2_REG_OFFSET, 22, USART_STAT_REG_OFFSET, 20),
    CTS = usart_regidx_bit2!(USART_CTL2_REG_OFFSET, 10, USART_STAT_REG_OFFSET, 9),
    ERR_NERR = usart_regidx_bit2!(USART_CTL2_REG_OFFSET, 0, USART_STAT_REG_OFFSET, 2),
    ERR_ORERR = usart_regidx_bit2!(USART_CTL2_REG_OFFSET, 0, USART_STAT_REG_OFFSET, 3),
    ERR_FERR = usart_regidx_bit2!(USART_CTL2_REG_OFFSET, 0, USART_STAT_REG_OFFSET, 1),
    RFF = usart_regidx_bit2!(USART_RFCS_REG_OFFSET, 9, USART_RFCS_REG_OFFSET, 15),
}

unsafe extern "C" {
    fn usart_deinit(usart: u32);
    fn usart_data_transmit(usart: u32, data: u16);
    fn usart_data_receive(usart: u32) -> u16;
    fn usart_flag_get(usart: u32, flag: u32) -> i32;
    fn usart_baudrate_set(usart: u32, baud: u32);
    fn usart_parity_config(usart: u32, parity: u32);
    fn usart_stop_bit_set(usart: u32, stopbits: u32);
    fn usart_word_length_set(usart: u32, length: u32);
    fn usart_enable(usart: u32);
    fn usart_receive_config(usart: u32, enable: u32);
    fn usart_transmit_config(usart: u32, enable: u32);
    fn usart_disable(usart: u32);
    fn usart_interrupt_flag_clear(usart: u32, flag: u32);
}

pub struct Gd32vw55xUart {
    pub base_addr: u32,
}

impl Gd32vw55xUart {
    pub const fn new(base_addr: u32) -> Self {
        Self { base_addr }
    }
}

unsafe impl Send for Gd32vw55xUart {}
unsafe impl Sync for Gd32vw55xUart {}

impl Configuration<super::UartConfig> for Gd32vw55xUart {
    type Target = ();
    fn configure(&self, param: &super::UartConfig) -> blueos_hal::err::Result<Self::Target> {
        let super::UartConfig {
            baudrate,
            parity,
            stop_bits,
            data_bits,
            flow_ctrl,
        } = param;

        unsafe {
            usart_deinit(self.base_addr);
            usart_baudrate_set(self.base_addr, *baudrate);
            match parity {
                super::Parity::None => usart_parity_config(self.base_addr, USART_PM_NONE),
                super::Parity::Odd => usart_parity_config(self.base_addr, USART_PM_ODD),
                super::Parity::Even => usart_parity_config(self.base_addr, USART_PM_EVEN),
                _ => return Err(blueos_hal::err::HalError::NotSupport),
            }
            match stop_bits {
                super::StopBits::DataBits0_5 => {
                    usart_stop_bit_set(self.base_addr, USART_STB_0_5BIT);
                }
                super::StopBits::DataBits1 => {
                    usart_stop_bit_set(self.base_addr, USART_STB_1BIT);
                }
                super::StopBits::DataBits1_5 => {
                    usart_stop_bit_set(self.base_addr, USART_STB_1_5BIT);
                }
                super::StopBits::DataBits2 => {
                    usart_stop_bit_set(self.base_addr, USART_STB_2BIT);
                }
            }
            match data_bits {
                super::DataBits::DataBits8 => {
                    usart_word_length_set(self.base_addr, USART_WL_8BIT);
                }
                super::DataBits::DataBits9 => {
                    usart_word_length_set(self.base_addr, USART_WL_9BIT);
                }
                _ => return Err(blueos_hal::err::HalError::NotSupport),
            }
            match flow_ctrl {
                super::FlowCtrl::None => {}
                _ => return Err(blueos_hal::err::HalError::NotSupport),
            }
        }

        Ok(())
    }
}

impl Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus> for Gd32vw55xUart {}

impl Has8bitDataReg for Gd32vw55xUart {
    fn read_data8(&self) -> blueos_hal::err::Result<u8> {
        if unsafe {
            usart_flag_get(
                self.base_addr,
                UsartFlag::PERR as u32
                    | UsartFlag::FERR as u32
                    | UsartFlag::NERR as u32
                    | UsartFlag::ORERR as u32,
            )
        } == 1
        {
            Err(blueos_hal::err::HalError::IoError)
        } else {
            let d = unsafe { usart_data_receive(self.base_addr) };
            Ok(d as u8)
        }
    }

    fn write_data8(&self, data: u8) {
        unsafe {
            usart_data_transmit(self.base_addr, data as u16);
        }
    }

    fn is_data_ready(&self) -> bool {
        unsafe { usart_flag_get(self.base_addr, UsartFlag::RBNE as u32) == 1 }
    }
}

impl HasLineStatusReg for Gd32vw55xUart {
    fn is_bus_busy(&self) -> bool {
        unsafe { usart_flag_get(self.base_addr, UsartFlag::BSY as u32) == 1 }
    }
}

impl HasFifo for Gd32vw55xUart {
    fn enable_fifo(&self, num: u8) -> blueos_hal::err::Result<()> {
        todo!()
    }

    fn is_tx_fifo_full(&self) -> bool {
        unsafe { usart_flag_get(self.base_addr, UsartFlag::TBE as u32) == 0 }
    }

    fn is_rx_fifo_empty(&self) -> bool {
        unsafe { usart_flag_get(self.base_addr, UsartFlag::RFE as u32) == 1 }
    }
}

impl HasInterruptReg for Gd32vw55xUart {
    type InterruptType = super::InterruptType;

    fn enable_interrupt(&self, intr: Self::InterruptType) {}

    fn disable_interrupt(&self, intr: Self::InterruptType) {}

    fn clear_interrupt(&self, intr: Self::InterruptType) {}

    fn get_interrupt(&self) -> Self::InterruptType {
        super::InterruptType::Unknown
    }

    fn set_interrupt_handler(&self, _handler: &'static dyn Fn()) {}

    fn get_irq_nums(&self) -> &[u32] {
        &[]
    }
}

impl PlatPeri for Gd32vw55xUart {
    fn enable(&self) {
        unsafe {
            usart_receive_config(self.base_addr, USART_RECEIVE_ENABLE);
            usart_transmit_config(self.base_addr, USART_TRANSMIT_ENABLE);
            usart_enable(self.base_addr);
        }
    }

    fn disable(&self) {
        unsafe {
            usart_receive_config(self.base_addr, USART_RECEIVE_DISABLE);
            usart_transmit_config(self.base_addr, USART_TRANSMIT_DISABLE);
            usart_disable(self.base_addr);
        }
    }
}
