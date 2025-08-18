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

// This code is based on [tock](https://github.com/tock/tock/blob/master/chips/rp2040/src/resets.rs)

// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

use crate::boards::raspberry_pico2_cortexm::rp235x::static_ref::StaticRef;
use tock_registers::{
    fields::FieldValue,
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::ReadWrite,
};

register_structs! {
    ResetsRegisters {
        /// Reset control. If a bit is set it means the peripheral is in reset. 0 means the
        (0x000 => reset: ReadWrite<u32, RESET::Register>),
        /// Watchdog select. If a bit is set then the watchdog will reset this peripheral wh
        (0x004 => wdsel: ReadWrite<u32, WDSEL::Register>),
        /// Reset done. If a bit is set then a reset done signal has been returned by the pe
        (0x008 => reset_done: ReadWrite<u32, RESET_DONE::Register>),
        (0x00C => @END),
    }
}

register_bitfields![u32,
    RESET [
        usbctrl OFFSET(28) NUMBITS(1) [],

        uart1 OFFSET(27) NUMBITS(1) [],

        uart0 OFFSET(26) NUMBITS(1) [],

        trng OFFSET(25) NUMBITS(1) [],

        timer1 OFFSET(24) NUMBITS(1) [],

        timer0 OFFSET(23) NUMBITS(1) [],

        tbman OFFSET(22) NUMBITS(1) [],

        sysinfo OFFSET(21) NUMBITS(1) [],

        syscfg OFFSET(20) NUMBITS(1) [],

        spi1 OFFSET(19) NUMBITS(1) [],

        spi0 OFFSET(18) NUMBITS(1) [],

        sha256 OFFSET(17) NUMBITS(1) [],

        pwm OFFSET(16) NUMBITS(1) [],

        pll_usb OFFSET(15) NUMBITS(1) [],

        pll_sys OFFSET(14) NUMBITS(1) [],

        pio2 OFFSET(13) NUMBITS(1) [],

        pio1 OFFSET(12) NUMBITS(1) [],

        pio0 OFFSET(11) NUMBITS(1) [],

        pads_qspi OFFSET(10) NUMBITS(1) [],

        pads_bank0 OFFSET(9) NUMBITS(1) [],

        jtag OFFSET(8) NUMBITS(1) [],

        io_qspi OFFSET(7) NUMBITS(1) [],

        io_bank0 OFFSET(6) NUMBITS(1) [],

        i2c1 OFFSET(5) NUMBITS(1) [],

        i2c0 OFFSET(4) NUMBITS(1) [],

        hstx OFFSET(3) NUMBITS(1) [],

        dma OFFSET(2) NUMBITS(1) [],

        busctrl OFFSET(1) NUMBITS(1) [],

        adc OFFSET(0) NUMBITS(1) []
    ],
    WDSEL [
        usbctrl OFFSET(28) NUMBITS(1) [],

        uart1 OFFSET(27) NUMBITS(1) [],

        uart0 OFFSET(26) NUMBITS(1) [],

        trng OFFSET(25) NUMBITS(1) [],

        timer1 OFFSET(24) NUMBITS(1) [],

        timer0 OFFSET(23) NUMBITS(1) [],

        tbman OFFSET(22) NUMBITS(1) [],

        sysinfo OFFSET(21) NUMBITS(1) [],

        syscfg OFFSET(20) NUMBITS(1) [],

        spi1 OFFSET(19) NUMBITS(1) [],

        spi0 OFFSET(18) NUMBITS(1) [],

        sha256 OFFSET(17) NUMBITS(1) [],

        pwm OFFSET(16) NUMBITS(1) [],

        pll_usb OFFSET(15) NUMBITS(1) [],

        pll_sys OFFSET(14) NUMBITS(1) [],

        pio2 OFFSET(13) NUMBITS(1) [],

        pio1 OFFSET(12) NUMBITS(1) [],

        pio0 OFFSET(11) NUMBITS(1) [],

        pads_qspi OFFSET(10) NUMBITS(1) [],

        pads_bank0 OFFSET(9) NUMBITS(1) [],

        jtag OFFSET(8) NUMBITS(1) [],

        io_qspi OFFSET(7) NUMBITS(1) [],

        io_bank0 OFFSET(6) NUMBITS(1) [],

        i2c1 OFFSET(5) NUMBITS(1) [],

        i2c0 OFFSET(4) NUMBITS(1) [],

        hstx OFFSET(3) NUMBITS(1) [],

        dma OFFSET(2) NUMBITS(1) [],

        busctrl OFFSET(1) NUMBITS(1) [],

        adc OFFSET(0) NUMBITS(1) []
    ],
    RESET_DONE [
        usbctrl OFFSET(28) NUMBITS(1) [],

        uart1 OFFSET(27) NUMBITS(1) [],

        uart0 OFFSET(26) NUMBITS(1) [],

        trng OFFSET(25) NUMBITS(1) [],

        timer1 OFFSET(24) NUMBITS(1) [],

        timer0 OFFSET(23) NUMBITS(1) [],

        tbman OFFSET(22) NUMBITS(1) [],

        sysinfo OFFSET(21) NUMBITS(1) [],

        syscfg OFFSET(20) NUMBITS(1) [],

        spi1 OFFSET(19) NUMBITS(1) [],

        spi0 OFFSET(18) NUMBITS(1) [],

        sha256 OFFSET(17) NUMBITS(1) [],

        pwm OFFSET(16) NUMBITS(1) [],

        pll_usb OFFSET(15) NUMBITS(1) [],

        pll_sys OFFSET(14) NUMBITS(1) [],

        pio2 OFFSET(13) NUMBITS(1) [],

        pio1 OFFSET(12) NUMBITS(1) [],

        pio0 OFFSET(11) NUMBITS(1) [],

        pads_qspi OFFSET(10) NUMBITS(1) [],

        pads_bank0 OFFSET(9) NUMBITS(1) [],

        jtag OFFSET(8) NUMBITS(1) [],

        io_qspi OFFSET(7) NUMBITS(1) [],

        io_bank0 OFFSET(6) NUMBITS(1) [],

        i2c1 OFFSET(5) NUMBITS(1) [],

        i2c0 OFFSET(4) NUMBITS(1) [],

        hstx OFFSET(3) NUMBITS(1) [],

        dma OFFSET(2) NUMBITS(1) [],

        busctrl OFFSET(1) NUMBITS(1) [],

        adc OFFSET(0) NUMBITS(1) []
    ]
];
const RESETS_BASE: StaticRef<ResetsRegisters> =
    unsafe { StaticRef::new(0x40020000 as *const ResetsRegisters) };

pub enum Peripheral {
    Adc,
    BusController,
    Dma,
    HSTX,
    I2c0,
    I2c1,
    IOBank0,
    IOQSpi,
    Jtag,
    PadsBank0,
    PadsQSpi,
    Pio0,
    Pio1,
    Pio2,
    PllSys,
    PllUsb,
    Pwm,
    Sha256,
    Spi0,
    Spi1,
    Syscfg,
    SysInfo,
    TBMan,
    Timer0,
    Timer1,
    Trng,
    Uart0,
    Uart1,
    UsbCtrl,
}

impl Peripheral {
    fn get_reset_field_set(&self) -> FieldValue<u32, RESET::Register> {
        match self {
            Peripheral::Adc => RESET::adc::SET,
            Peripheral::BusController => RESET::busctrl::SET,
            Peripheral::Dma => RESET::dma::SET,
            Peripheral::HSTX => RESET::hstx::SET,
            Peripheral::I2c0 => RESET::i2c0::SET,
            Peripheral::I2c1 => RESET::i2c1::SET,
            Peripheral::IOBank0 => RESET::io_bank0::SET,
            Peripheral::IOQSpi => RESET::io_qspi::SET,
            Peripheral::Jtag => RESET::jtag::SET,
            Peripheral::PadsBank0 => RESET::pads_bank0::SET,
            Peripheral::PadsQSpi => RESET::pads_qspi::SET,
            Peripheral::Pio0 => RESET::pio0::SET,
            Peripheral::Pio1 => RESET::pio1::SET,
            Peripheral::Pio2 => RESET::pio2::SET,
            Peripheral::PllSys => RESET::pll_sys::SET,
            Peripheral::PllUsb => RESET::pll_usb::SET,
            Peripheral::Pwm => RESET::pwm::SET,
            Peripheral::Sha256 => RESET::sha256::SET,
            Peripheral::Spi0 => RESET::spi0::SET,
            Peripheral::Spi1 => RESET::spi1::SET,
            Peripheral::Syscfg => RESET::syscfg::SET,
            Peripheral::SysInfo => RESET::sysinfo::SET,
            Peripheral::TBMan => RESET::tbman::SET,
            Peripheral::Timer0 => RESET::timer0::SET,
            Peripheral::Timer1 => RESET::timer1::SET,
            Peripheral::Trng => RESET::trng::SET,
            Peripheral::Uart0 => RESET::uart0::SET,
            Peripheral::Uart1 => RESET::uart1::SET,
            Peripheral::UsbCtrl => RESET::usbctrl::SET,
        }
    }

    fn get_reset_field_clear(&self) -> FieldValue<u32, RESET::Register> {
        match self {
            Peripheral::Adc => RESET::adc::CLEAR,
            Peripheral::BusController => RESET::busctrl::CLEAR,
            Peripheral::Dma => RESET::dma::CLEAR,
            Peripheral::HSTX => RESET::hstx::CLEAR,
            Peripheral::I2c0 => RESET::i2c0::CLEAR,
            Peripheral::I2c1 => RESET::i2c1::CLEAR,
            Peripheral::IOBank0 => RESET::io_bank0::CLEAR,
            Peripheral::IOQSpi => RESET::io_qspi::CLEAR,
            Peripheral::Jtag => RESET::jtag::CLEAR,
            Peripheral::PadsBank0 => RESET::pads_bank0::CLEAR,
            Peripheral::PadsQSpi => RESET::pads_qspi::CLEAR,
            Peripheral::Pio0 => RESET::pio0::CLEAR,
            Peripheral::Pio1 => RESET::pio1::CLEAR,
            Peripheral::Pio2 => RESET::pio2::CLEAR,
            Peripheral::PllSys => RESET::pll_sys::CLEAR,
            Peripheral::PllUsb => RESET::pll_usb::CLEAR,
            Peripheral::Pwm => RESET::pwm::CLEAR,
            Peripheral::Sha256 => RESET::sha256::CLEAR,
            Peripheral::Spi0 => RESET::spi0::CLEAR,
            Peripheral::Spi1 => RESET::spi1::CLEAR,
            Peripheral::Syscfg => RESET::syscfg::CLEAR,
            Peripheral::SysInfo => RESET::sysinfo::CLEAR,
            Peripheral::TBMan => RESET::tbman::CLEAR,
            Peripheral::Timer0 => RESET::timer0::CLEAR,
            Peripheral::Timer1 => RESET::timer1::CLEAR,
            Peripheral::Trng => RESET::trng::CLEAR,
            Peripheral::Uart0 => RESET::uart0::CLEAR,
            Peripheral::Uart1 => RESET::uart1::CLEAR,
            Peripheral::UsbCtrl => RESET::usbctrl::CLEAR,
        }
    }

    fn get_reset_done_field_set(&self) -> FieldValue<u32, RESET_DONE::Register> {
        match self {
            Peripheral::Adc => RESET_DONE::adc::SET,
            Peripheral::BusController => RESET_DONE::busctrl::SET,
            Peripheral::Dma => RESET_DONE::dma::SET,
            Peripheral::HSTX => RESET_DONE::hstx::SET,
            Peripheral::I2c0 => RESET_DONE::i2c0::SET,
            Peripheral::I2c1 => RESET_DONE::i2c1::SET,
            Peripheral::IOBank0 => RESET_DONE::io_bank0::SET,
            Peripheral::IOQSpi => RESET_DONE::io_qspi::SET,
            Peripheral::Jtag => RESET_DONE::jtag::SET,
            Peripheral::PadsBank0 => RESET_DONE::pads_bank0::SET,
            Peripheral::PadsQSpi => RESET_DONE::pads_qspi::SET,
            Peripheral::Pio0 => RESET_DONE::pio0::SET,
            Peripheral::Pio1 => RESET_DONE::pio1::SET,
            Peripheral::Pio2 => RESET_DONE::pio2::SET,
            Peripheral::PllSys => RESET_DONE::pll_sys::SET,
            Peripheral::PllUsb => RESET_DONE::pll_usb::SET,
            Peripheral::Pwm => RESET_DONE::pwm::SET,
            Peripheral::Sha256 => RESET_DONE::sha256::SET,
            Peripheral::Spi0 => RESET_DONE::spi0::SET,
            Peripheral::Spi1 => RESET_DONE::spi1::SET,
            Peripheral::Syscfg => RESET_DONE::syscfg::SET,
            Peripheral::SysInfo => RESET_DONE::sysinfo::SET,
            Peripheral::TBMan => RESET_DONE::tbman::SET,
            Peripheral::Timer0 => RESET_DONE::timer0::SET,
            Peripheral::Timer1 => RESET_DONE::timer1::SET,
            Peripheral::Trng => RESET_DONE::trng::SET,
            Peripheral::Uart0 => RESET_DONE::uart0::SET,
            Peripheral::Uart1 => RESET_DONE::uart1::SET,
            Peripheral::UsbCtrl => RESET_DONE::usbctrl::SET,
        }
    }
}

pub struct Resets {
    registers: StaticRef<ResetsRegisters>,
}

impl Resets {
    pub const fn new() -> Resets {
        Resets {
            registers: RESETS_BASE,
        }
    }

    pub fn reset(&self, peripherals: &'static [Peripheral]) {
        if peripherals.len() > 0 {
            let mut value: FieldValue<u32, RESET::Register> = peripherals[0].get_reset_field_set();
            for peripheral in peripherals {
                value += peripheral.get_reset_field_set();
            }
            self.registers.reset.modify(value);
        }
    }

    pub fn unreset(&self, peripherals: &'static [Peripheral], wait_for: bool) {
        if peripherals.len() > 0 {
            let mut value: FieldValue<u32, RESET::Register> =
                peripherals[0].get_reset_field_clear();
            for peripheral in peripherals {
                value += peripheral.get_reset_field_clear();
            }
            self.registers.reset.modify(value);

            if wait_for {
                let mut value_done: FieldValue<u32, RESET_DONE::Register> =
                    peripherals[0].get_reset_done_field_set();
                for peripheral in peripherals {
                    value_done += peripheral.get_reset_done_field_set();
                }
                while !self.registers.reset_done.matches_all(value_done) {}
            }
        }
    }

    pub fn reset_all_except(&self, peripherals: &'static [Peripheral]) {
        let mut value = 0xFFFFFF;
        for peripheral in peripherals {
            value ^= peripheral.get_reset_field_set().value;
        }
        self.registers.reset.set(value);
    }

    pub fn unreset_all_except(&self, peripherals: &'static [Peripheral], wait_for: bool) {
        let mut value = 0;
        for peripheral in peripherals {
            value |= peripheral.get_reset_field_set().value;
        }

        self.registers.reset.set(value);

        if wait_for {
            value = !value & 0xFFFFF;
            while (self.registers.reset_done.get() & value) != value {}
        }
    }

    pub fn watchdog_reset_all_except(&self, peripherals: &'static [Peripheral]) {
        let mut value = 0xFFFFFF;
        for peripheral in peripherals {
            value ^= peripheral.get_reset_field_set().value;
        }
        self.registers.wdsel.set(value);
    }
}
