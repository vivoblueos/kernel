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
    uart::Uart, Configuration, Has8bitDataReg, HasFifo, HasInterruptReg, HasLineStatusReg,
};
use hal_espressif_rs::uart_hal_context_t;

use crate::uart::{Parity, StopBits};

pub struct Esp32Uart {
    inner: uart_hal_context_t,
}

unsafe impl Send for Esp32Uart {}
unsafe impl Sync for Esp32Uart {}

impl Esp32Uart {
    unsafe fn get_inner_ref_mut(&self) -> &mut uart_hal_context_t {
        &mut *(core::ptr::addr_of!(self.inner) as *mut uart_hal_context_t)
    }

    pub const fn new(base_addr: u32) -> Self {
        unsafe {
            Esp32Uart {
                inner: uart_hal_context_t {
                    dev: base_addr as *mut _,
                },
            }
        }
    }
}

impl Configuration<super::UartConfig> for Esp32Uart {
    type Target = ();
    // This code snippet is modified from
    // https://github.com/zephyrproject-rtos/zephyr/blob/4f3478391a3c5e555dcd629f9e829378c17b0d62/drivers/serial/uart_esp32.c#L277-L377
    fn configure(&self, param: &super::UartConfig) -> blueos_hal::err::Result<Self::Target> {
        let super::UartConfig {
            baudrate,
            parity,
            stop_bits,
            data_bits,
            flow_ctrl,
        } = param;

        unsafe {
            hal_espressif_rs::uart_hal_set_sclk(
                self.get_inner_ref_mut(),
                hal_espressif_rs::soc_periph_uart_clk_src_legacy_t_UART_SCLK_DEFAULT,
            );
            hal_espressif_rs::uart_hal_set_txfifo_empty_thr(self.get_inner_ref_mut(), 0x1);
            hal_espressif_rs::uart_hal_set_rxfifo_full_thr(self.get_inner_ref_mut(), 0x16);
            hal_espressif_rs::uart_hal_rxfifo_rst(self.get_inner_ref_mut());
            hal_espressif_rs::uart_hal_txfifo_rst(self.get_inner_ref_mut());
        }

        match parity {
            Parity::None => unsafe {
                hal_espressif_rs::uart_hal_set_parity(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_parity_t_UART_PARITY_DISABLE,
                );
            },
            Parity::Even => unsafe {
                hal_espressif_rs::uart_hal_set_parity(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_parity_t_UART_PARITY_EVEN,
                );
            },
            Parity::Odd => unsafe {
                hal_espressif_rs::uart_hal_set_parity(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_parity_t_UART_PARITY_ODD,
                );
            },
            _ => {
                return Err(blueos_hal::err::HalError::InvalidParam);
            }
        }

        match data_bits {
            super::DataBits::DataBits5 => unsafe {
                hal_espressif_rs::uart_hal_set_data_bit_num(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_word_length_t_UART_DATA_5_BITS,
                );
            },
            super::DataBits::DataBits6 => unsafe {
                hal_espressif_rs::uart_hal_set_data_bit_num(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_word_length_t_UART_DATA_6_BITS,
                );
            },
            super::DataBits::DataBits7 => unsafe {
                hal_espressif_rs::uart_hal_set_data_bit_num(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_word_length_t_UART_DATA_7_BITS,
                );
            },
            super::DataBits::DataBits8 => unsafe {
                hal_espressif_rs::uart_hal_set_data_bit_num(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_word_length_t_UART_DATA_8_BITS,
                );
            },
            _ => {
                return Err(blueos_hal::err::HalError::InvalidParam);
            }
        }

        match stop_bits {
            StopBits::DataBits1 => unsafe {
                hal_espressif_rs::uart_hal_set_stop_bits(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_stop_bits_t_UART_STOP_BITS_1,
                );
            },
            StopBits::DataBits1_5 => unsafe {
                hal_espressif_rs::uart_hal_set_stop_bits(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_stop_bits_t_UART_STOP_BITS_1_5,
                );
            },
            StopBits::DataBits2 => unsafe {
                hal_espressif_rs::uart_hal_set_stop_bits(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_stop_bits_t_UART_STOP_BITS_2,
                );
            },
            _ => {
                return Err(blueos_hal::err::HalError::InvalidParam);
            }
        }

        unsafe {
            hal_espressif_rs::uart_hal_set_mode(
                self.get_inner_ref_mut(),
                hal_espressif_rs::uart_mode_t_UART_MODE_UART,
            );
        }

        match flow_ctrl {
            super::FlowCtrl::None => unsafe {
                hal_espressif_rs::uart_hal_set_hw_flow_ctrl(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_hw_flowcontrol_t_UART_HW_FLOWCTRL_DISABLE,
                    0,
                );
            },
            super::FlowCtrl::RtsCts => unsafe {
                hal_espressif_rs::uart_hal_set_hw_flow_ctrl(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_hw_flowcontrol_t_UART_HW_FLOWCTRL_CTS_RTS,
                    10,
                );
            },
            super::FlowCtrl::Rs485 => unsafe {
                hal_espressif_rs::uart_hal_set_mode(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_mode_t_UART_MODE_RS485_HALF_DUPLEX,
                );
            },
            _ => {
                return Err(blueos_hal::err::HalError::InvalidParam);
            }
        }

        let src_clk = unsafe {
            let mut src_clk: hal_espressif_rs::uart_sclk_t = 0;
            hal_espressif_rs::uart_hal_get_sclk(self.get_inner_ref_mut(), &mut src_clk);
            if src_clk == 0 {
                return Err(blueos_hal::err::HalError::Fail);
            }
            src_clk
        };

        let sclk_freq = unsafe {
            let mut sclk_freq: u32 = 0;
            hal_espressif_rs::esp_clk_tree_src_get_freq_hz(
                src_clk as hal_espressif_rs::soc_module_clk_t,
                hal_espressif_rs::esp_clk_tree_src_freq_precision_t_ESP_CLK_TREE_SRC_FREQ_PRECISION_CACHED,
                core::ptr::addr_of_mut!(sclk_freq),
            );
            sclk_freq
        };
        unsafe {
            hal_espressif_rs::uart_hal_set_baudrate(self.get_inner_ref_mut(), *baudrate, sclk_freq);
            hal_espressif_rs::uart_hal_set_rx_timeout(self.get_inner_ref_mut(), 0x16);
        }
        Ok(())
    }
}

// impl Uart<super::UartConfig, (), super::InterruptType, super::UartCtrlStatus> for Esp32Uart {}

impl Has8bitDataReg for Esp32Uart {
    fn read_data8(&self) -> blueos_hal::err::Result<u8> {
        let mut len = 1;
        let mut p_char = 0u8;
        unsafe {
            hal_espressif_rs::uart_hal_read_rxfifo(
                self.get_inner_ref_mut(),
                core::ptr::addr_of_mut!(p_char),
                core::ptr::addr_of_mut!(len),
            )
        };
        if len == 0 {
            return Err(blueos_hal::err::HalError::IoError);
        }
        Ok(p_char)
    }

    fn write_data8(&self, data: u8) {
        let mut len = 1;
        unsafe {
            hal_espressif_rs::uart_hal_write_txfifo(
                self.get_inner_ref_mut(),
                core::ptr::addr_of!(data),
                1,
                core::ptr::addr_of_mut!(len),
            )
        };
    }

    fn is_data_ready(&self) -> bool {
        unsafe {
            hal_espressif_rs::rust_helper_uart_hal_get_rxfifo_len(self.get_inner_ref_mut()) > 0
        }
    }
}

impl HasLineStatusReg for Esp32Uart {
    fn is_bus_busy(&self) -> bool {
        unsafe {
            hal_espressif_rs::rust_helper_uart_hal_get_txfifo_len(self.get_inner_ref_mut()) > 0
        }
    }
}

impl HasFifo for Esp32Uart {
    fn enable_fifo(&self, _num: u8) -> blueos_hal::err::Result<()> {
        // FIFO is always enabled in ESP32 UART
        Ok(())
    }

    fn is_tx_fifo_full(&self) -> bool {
        unsafe {
            // FIXME
            hal_espressif_rs::rust_helper_uart_hal_get_txfifo_len(self.get_inner_ref_mut()) != 0
        }
    }

    fn is_rx_fifo_empty(&self) -> bool {
        unsafe {
            hal_espressif_rs::rust_helper_uart_hal_get_rxfifo_len(self.get_inner_ref_mut()) == 0
        }
    }
}

impl HasInterruptReg for Esp32Uart {
    type InterruptType = super::InterruptType;

    fn enable_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Rx => unsafe {
                hal_espressif_rs::rust_helper_uart_clr_intsts_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_RXFIFO_FULL,
                );
                hal_espressif_rs::rust_helper_uart_clr_intsts_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_RXFIFO_TOUT,
                );
                hal_espressif_rs::uart_hal_ena_intr_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_RXFIFO_FULL,
                );
                hal_espressif_rs::uart_hal_ena_intr_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_RXFIFO_TOUT,
                );
            },
            super::InterruptType::Tx => unsafe {
                hal_espressif_rs::rust_helper_uart_clr_intsts_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_TXFIFO_EMPTY,
                );
                hal_espressif_rs::uart_hal_ena_intr_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_TXFIFO_EMPTY,
                );
            },
            _ => {}
        }
    }

    fn disable_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Rx => unsafe {
                hal_espressif_rs::rust_helper_uart_hal_disable_intr_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_RXFIFO_FULL,
                );
                hal_espressif_rs::rust_helper_uart_hal_disable_intr_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_RXFIFO_TOUT,
                );
            },
            super::InterruptType::Tx => unsafe {
                hal_espressif_rs::rust_helper_uart_hal_disable_intr_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_TXFIFO_EMPTY,
                );
            },
            _ => {}
        }
    }

    fn clear_interrupt(&self, intr: Self::InterruptType) {
        match intr {
            super::InterruptType::Rx => unsafe {
                hal_espressif_rs::rust_helper_uart_clr_intsts_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_RXFIFO_FULL,
                );
                hal_espressif_rs::rust_helper_uart_clr_intsts_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_RXFIFO_TOUT,
                );
            },
            super::InterruptType::Tx => unsafe {
                hal_espressif_rs::rust_helper_uart_clr_intsts_mask(
                    self.get_inner_ref_mut(),
                    hal_espressif_rs::uart_intr_t_UART_INTR_TXFIFO_EMPTY,
                );
            },
            _ => unsafe {
                let mask = hal_espressif_rs::rust_helper_uart_hal_get_intsts_mask(
                    self.get_inner_ref_mut(),
                );
                hal_espressif_rs::rust_helper_uart_clr_intsts_mask(self.get_inner_ref_mut(), mask);
            },
        }
    }

    fn get_interrupt(&self) -> Self::InterruptType {
        unsafe {
            let mask =
                hal_espressif_rs::rust_helper_uart_hal_get_intsts_mask(self.get_inner_ref_mut());
            if mask & hal_espressif_rs::uart_intr_t_UART_INTR_RXFIFO_FULL != 0 {
                super::InterruptType::Rx
            } else if mask & hal_espressif_rs::uart_intr_t_UART_INTR_TXFIFO_EMPTY != 0 {
                super::InterruptType::Tx
            } else {
                super::InterruptType::Unknown
            }
        }
    }

    fn set_interrupt_handler(&self, handler: &'static dyn Fn()) {}

    fn get_irq_nums(&self) -> &[u32] {
        &[]
    }
}
