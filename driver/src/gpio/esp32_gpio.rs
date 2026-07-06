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

//! ESP32-C3 GPIO output pin driver. Pin mode is configured by
//! `pinctrl::esp32_pinctrl`; this driver only flips the output data latch.

use crate::static_ref::StaticRef;
use tock_registers::{
    interfaces::Writeable, register_bitfields, register_structs, registers::ReadWrite,
};

pub(crate) const GPIO_BASE: StaticRef<GpioRegisters> =
    unsafe { StaticRef::new(0x60004000 as *const GpioRegisters) };

register_bitfields! [
    u32,

    pub GpioOut [
        DATA OFFSET(0) NUMBITS(26) [],
    ],
    pub GpioEnable [
        DATA OFFSET(0) NUMBITS(26) [],
    ],
];

register_structs! {
    pub GpioRegisters {
        (0x000 => pub bt_select: ReadWrite<u32>),
        (0x004 => pub out: ReadWrite<u32, GpioOut::Register>),
        (0x008 => pub out_w1ts: ReadWrite<u32, GpioOut::Register>),
        (0x00C => pub out_w1tc: ReadWrite<u32, GpioOut::Register>),
        (0x010 => _reserved0),
        (0x020 => pub enable: ReadWrite<u32, GpioEnable::Register>),
        (0x024 => pub enable_w1ts: ReadWrite<u32, GpioEnable::Register>),
        (0x028 => pub enable_w1tc: ReadWrite<u32, GpioEnable::Register>),
        (0x02C => @END),
    }
}

/// GPIO output pin for ESP32-C3, e.g. SPI CS via `embedded_hal_bus::spi::ExclusiveDevice`.
pub struct Esp32GpioOutputPin<const PIN: u8>;

impl<const PIN: u8> Esp32GpioOutputPin<PIN> {
    pub const fn new() -> Self {
        Esp32GpioOutputPin
    }
}

impl<const PIN: u8> blueos_hal::PlatPeri for Esp32GpioOutputPin<PIN> {}

impl<const PIN: u8> blueos_hal::gpio::OutputPin for Esp32GpioOutputPin<PIN> {
    fn set_low(&self) -> blueos_hal::err::Result<()> {
        let gpio_regs = &*GPIO_BASE;
        gpio_regs.out_w1tc.write(GpioOut::DATA.val(1 << PIN));
        Ok(())
    }

    fn set_high(&self) -> blueos_hal::err::Result<()> {
        let gpio_regs = &*GPIO_BASE;
        gpio_regs.out_w1ts.write(GpioOut::DATA.val(1 << PIN));
        Ok(())
    }
}
