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
use tock_registers::{
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::{ReadOnly, ReadWrite},
};

register_structs! {
    /// SIO Control Registers
    SIORegisters {
        /// Not used
        (0x000 => cpuid: ReadOnly<u32, CPUID::Register>),

        /// Input value for GPIO pins
        (0x004 => gpio_in: ReadOnly<u32, GPIO_IN::Register>),

        /// Not used
        (0x008 => _reserved1),

        /// GPIO output value
        (0x010 => gpio_out: ReadWrite<u32, GPIO_OUT::Register>),

        (0x014 => _reserved2),

        /// GPIO output value set
        (0x018 => gpio_out_set: ReadWrite<u32, GPIO_OUT_SET::Register>),

        (0x01c => _reserved3),

        /// GPIO output value clear
        (0x020 => gpio_out_clr: ReadWrite<u32, GPIO_OUT_CLR::Register>),

        (0x024 => _reserved4),

        /// GPIO output value XOR
        (0x028 => gpio_out_xor: ReadWrite<u32, GPIO_OUT_XOR::Register>),

        (0x02c => _reserved5),

        /// GPIO output enable
        (0x030 => gpio_oe: ReadWrite<u32, GPIO_OE::Register>),

        /// Not used
        (0x034 => _reserved6),

        /// GPIO output enable set
        (0x038 => gpio_oe_set: ReadWrite<u32, GPIO_OE_SET::Register>),

        (0x03c => _reserved7),

        /// GPIO output enable clear
        (0x040 => gpio_oe_clr: ReadWrite<u32, GPIO_OE_CLR::Register>),

        /// Not used
        (0x044 => _reserved8),

        /// FIFO status
        (0x050 => fifo_st: ReadWrite<u32, FIFO_ST::Register>),

        /// FIFO write
        (0x054 => fifo_wr: ReadWrite<u32, FIFO_WR::Register>),

        /// FIFO read
        (0x058 => fifo_rd: ReadOnly<u32, FIFO_RD::Register>),

        /// End
        (0x05c => @END),
    }
}

register_bitfields! [u32,
    CPUID [
        VALUE OFFSET(0) NUMBITS (32)
    ],
    GPIO_IN [
        ///Input value for GPIO0..31
        IN OFFSET(0) NUMBITS(32) []
    ],
    GPIO_OUT [
        ///Set output level (1/0 → high/low) for GPIO0...31.
        OUT OFFSET(0) NUMBITS(32) []
    ],
    GPIO_OUT_SET [
        ///Perform an atomic bit-set on GPIO_OUT
        OUT OFFSET(0) NUMBITS(32) []
    ],
    GPIO_OUT_CLR [
        ///Perform an atomic bit-clear on GPIO_OUT
        OUT OFFSET(0) NUMBITS(32) []
    ],
    GPIO_OUT_XOR [
        ///Perform an atomic bitwise XOR on GPIO_OUT
        OUT OFFSET(0) NUMBITS(32) []
    ],
    GPIO_OE [
        ///Set output enable (1/0 → output/input) for GPIO0...31
        OE OFFSET(0) NUMBITS(32) []
    ],
    GPIO_OE_SET [
        ///Perform an atomic bit-set on GPIO_OE
        OE OFFSET(0) NUMBITS(32) []
    ],
    GPIO_OE_CLR [
        ///Perform an atomic bit-clear on GPIO_OE
        OE OFFSET(0) NUMBITS(32) []
    ],
    FIFO_ST [
        /// FIFO read when empy
        ROE OFFSET(3) NUMBITS(1) [],
        /// FIFO written when full
        WOF OFFSET(2) NUMBITS(1) [],
        /// FIFO not full
        RDY OFFSET(1) NUMBITS(1) [],
        /// FIFO not empty
        VLD OFFSET(0) NUMBITS(1) []
    ],
    FIFO_WR [
        /// FIFO Write
        VALUE OFFSET(0) NUMBITS(32)
    ],
    FIFO_RD [
        /// FIFO Read
        VALUE OFFSET(0) NUMBITS(32)
    ],
];

const SIO_BASE_ADDRESS: usize = 0xd0000000;
const SIO_BASE: StaticRef<SIORegisters> =
    unsafe { StaticRef::new(SIO_BASE_ADDRESS as *const SIORegisters) };

pub fn enable_sio_gpio_out(pin: usize) {
    SIO_BASE.gpio_oe_set.set(1 << pin);
}

pub fn set_sio_gpio_out(pin: usize) {
    SIO_BASE.gpio_out_set.set(1 << pin);
}

pub fn set_sio_oe_set(pin: usize) {
    SIO_BASE.gpio_oe_set.set(1 << pin);
}

pub fn clear_sio_gpio_out(pin: usize) {
    SIO_BASE.gpio_out_clr.set(1 << pin);
}

pub fn toggle_sio_gpio_out(pin: usize) {
    SIO_BASE.gpio_out_xor.set(1 << pin);
}
