// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// This code is based on [tock](https://github.com/tock/tock/blob/master/chips/rp2040/src/gpio.rs)

// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

use crate::boards::raspberry_pico2_cortexm::rp235x::static_ref::StaticRef;
use embedded_hal::digital::{ErrorType, OutputPin};
use tock_registers::{
    interfaces::{ReadWriteable, Writeable},
    register_bitfields, register_structs,
    registers::{ReadOnly, ReadWrite},
};

#[repr(C)]
struct GpioPinReg {
    status: ReadOnly<u32, GPIOx_STATUS::Register>,
    ctrl: ReadWrite<u32, GPIOx_CTRL::Register>,
}

register_structs! {
    /// GPIO Registers.
    GpioRegisters {
        (0x000 => pin: [GpioPinReg; 48]),

        /// End
        (0x180 => @END),
    },
    /// User Bank Pad Control Registers
    GpioPadRegisters {
        /// Voltage select
        (0x00 => voltage: ReadWrite<u32, VOLTAGE_SELECT::Register>),

        /// Pads control
        (0x04 => gpio_pad: [ReadWrite<u32, GPIO_PAD::Register>; 48]),

        /// End
        (0xc4 => @END),
    }
}

register_bitfields! [u32,
    GPIOx_STATUS [
        /// interrupt to processors, after override is applied
        IRQTOPROC OFFSET(26) NUMBITS(1) [],
        /// input signal from pad, before override is applied
        INFROMPAD OFFSET(17) NUMBITS(1) [],
        /// output enable to pad after register override is applied
        OETOPAD OFFSET(13) NUMBITS(1) [],
        /// output signal to pad after register override is applied
        OUTTOPAD OFFSET(9) NUMBITS(1) [],
    ],
    GPIOx_CTRL [
        /// interrupt override?
        IRQOVER OFFSET(28) NUMBITS(2) [
            NoInvert = 0,
            Invert = 1,
            DriveLow = 2,
            DriveHigh = 3
        ],
        /// input override
        INOVER OFFSET(16) NUMBITS(2) [
            NoInvert = 0,
            Invert = 1,
            DriveLow = 2,
            DriveHigh = 3
        ],
        /// output enable override
        OEOVER OFFSET(14) NUMBITS(2) [
            EnableSignal = 0,
            EnableInverseSignal = 1,
            Disable = 2,
            Enable = 3
        ],
        /// output override
        OUTOVER OFFSET(12) NUMBITS(2) [
            Signal = 0,
            InverseSignal = 1,
            Low = 2,
            High = 3
        ],
        /// Function select
        FUNCSEL OFFSET(0) NUMBITS(5) []
    ],
    VOLTAGE_SELECT[
        VOLTAGE OFFSET(0) NUMBITS(1) [
            Set3V3 = 0,
            Set1V8 = 1
        ]
    ],
    GPIO_PAD [
        ISO OFFSET(8) NUMBITS(1) [],
        OD OFFSET(7) NUMBITS(1) [],
        IE OFFSET(6) NUMBITS(1) [],
        DRIVE OFFSET(4) NUMBITS(2) [],
        PUE OFFSET(3) NUMBITS(1) [],
        PDE OFFSET(2) NUMBITS(1) [],
        SCHMITT OFFSET(1) NUMBITS(1) [],
        SLEWFAST OFFSET(0) NUMBITS(1) []
    ],
];

const GPIO_BASE_ADDRESS: usize = 0x40028000;
const GPIO_BASE: StaticRef<GpioRegisters> =
    unsafe { StaticRef::new(GPIO_BASE_ADDRESS as *const GpioRegisters) };

const GPIO_PAD_BASE_ADDRESS: usize = 0x40038000;
const GPIO_PAD_BASE: StaticRef<GpioPadRegisters> =
    unsafe { StaticRef::new(GPIO_PAD_BASE_ADDRESS as *const GpioPadRegisters) };

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum GpioFunction {
    JTAG_TCK,
    JTAG_TDO,
    JTAG_TDI,
    SPI0_TX,
    SPI0_RX,
    SPI0_SCLK,
    UART0_TX,
    UART0_CTS,
    UART0_RTS,
    UART0_RX,
    I2C0_SDA,
    I2C1_SCL,
    I2C1_SDA,

    PWM_A_0,
    SIO,
    PIO0,
    PIO1,
    PIO2,
    XIP_SS_N_1,

    SPI1_SS_N,
    UART1_RX,
    UART1_TX,

    I2C0_SCL,
    PWM_A_1,
    PWM_A_2,
    PWM_B_1,
    PWM_B_4,
    CLOCKS_GPOU_3,
    CORESIGHT_TRACEDATA_0,
    CORESIGHT_TRACEDATA_1,
    CORESIGHT_TRACEDATA_2,
    USB_MUXING_OVERCURR_DETECT,

    USB_MUXING_VBUS_DETECT,
    USB_MUXING_VBUS_EN,
    NULL,
}

pub struct GpioPin<const PIN: usize>;

impl<const PIN: usize> GpioPin<PIN> {
    pub const fn new() -> Self {
        assert!(PIN < 48, "Invalid GPIO pin number");
        GpioPin {}
    }

    pub fn activate_pads(&self) {
        GPIO_PAD_BASE.gpio_pad[PIN].modify(GPIO_PAD::OD::CLEAR + GPIO_PAD::IE::SET);
    }

    pub fn set(&self) {
        super::sio::set_sio_gpio_out(PIN);
    }

    pub fn clear(&self) {
        super::sio::clear_sio_gpio_out(PIN);
    }

    pub fn toggle(&self) {
        super::sio::toggle_sio_gpio_out(PIN);
    }

    pub fn ctrl_iso(&self, iso: u32) {
        GPIO_PAD_BASE.gpio_pad[PIN].modify(GPIO_PAD::ISO.val(iso as u32));
    }

    pub fn set_pull_down(&self) {
        GPIO_PAD_BASE.gpio_pad[PIN].modify(GPIO_PAD::PDE::SET);
    }
}

trait FunctionIndex<const F: u8> {
    const INDEX: usize;
}

macro_rules! gpio_pin_function_impl {
    ($P:expr, $F:ident, $idx:expr) => {
        impl FunctionIndex<{GpioFunction::$F as u8}> for GpioPin<$P> {
            const INDEX: usize = $idx;
        }
    };

    (@impl $P:expr, $idx:expr, $F:ident) => {
        gpio_pin_function_impl!($P, $F, $idx);
    };

    (@impl $P:expr, $idx:expr, $F:ident, $($rest:ident),+) => {
        gpio_pin_function_impl!($P, $F, $idx);
        gpio_pin_function_impl!(@impl $P, $idx + 1, $($rest),+);
    };

    ($P:expr, $($F:ident),+) => {
        gpio_pin_function_impl!(@impl $P, 0, $($F),+);

        impl GpioPin<$P> {
            pub fn get_function_index(&self, f: GpioFunction) -> usize {
                match f {
                    $(
                        GpioFunction::$F => <GpioPin<$P> as FunctionIndex<{GpioFunction::$F as u8}>>::INDEX,
                    )+

                    _ => panic!("not supported"),
                }
            }

            pub fn set_function(&self, func: GpioFunction) {
                self.activate_pads();
                let func = self.get_function_index(func);
                self.ctrl_iso(0);
                GPIO_BASE.pin[$P].ctrl.set(0);
                GPIO_BASE.pin[$P].ctrl.modify(GPIOx_CTRL::FUNCSEL.val(func as u32));
            }
        }
    };
}

impl<const PIN: usize> ErrorType for GpioPin<PIN> {
    type Error = core::convert::Infallible;
}

impl<const PIN: usize> OutputPin for GpioPin<PIN> {
    fn set_high(&mut self) -> Result<(), Self::Error> {
        self.set();
        Ok(())
    }

    fn set_low(&mut self) -> Result<(), Self::Error> {
        self.clear();
        Ok(())
    }
}

gpio_pin_function_impl!(
    2,
    JTAG_TDI,
    SPI0_SCLK,
    UART0_CTS,
    I2C1_SDA,
    PWM_A_1,
    SIO,
    PIO0,
    PIO1,
    PIO2,
    CORESIGHT_TRACEDATA_0,
    USB_MUXING_VBUS_EN,
    UART0_TX
);
gpio_pin_function_impl!(
    3,
    JTAG_TDO,
    SPI0_TX,
    UART0_RTS,
    I2C1_SCL,
    PWM_B_1,
    SIO,
    PIO0,
    PIO1,
    PIO2,
    CORESIGHT_TRACEDATA_1,
    USB_MUXING_VBUS_DETECT,
    UART0_RX
);
gpio_pin_function_impl!(
    25,
    NULL,
    SPI1_SS_N,
    UART1_RX,
    I2C0_SCL,
    PWM_B_4,
    SIO,
    PIO0,
    PIO1,
    PIO2,
    CLOCKS_GPOU_3,
    USB_MUXING_VBUS_DETECT
);
