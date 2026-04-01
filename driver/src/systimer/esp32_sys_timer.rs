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

use blueos_hal::clock::Clock;
use tock_registers::{
    interfaces::{ReadWriteable, Readable, Writeable},
    register_bitfields, register_structs,
    registers::ReadWrite,
};

register_bitfields! [
    u32,

    pub CONF [
        CLK_EN OFFSET(31) NUMBITS(1) [],
        UNIT0_WORK_EN OFFSET(30) NUMBITS(1) [],
        UNIT1_WORK_EN OFFSET(29) NUMBITS(1) [],
        UNIT0_CORE0_STALL_EN OFFSET(28) NUMBITS(1) [],
        UNIT1_CORE0_STALL_EN OFFSET(26) NUMBITS(1) [],
        TARGET0_WORK_EN OFFSET(24) NUMBITS(1) [],
        TARGET1_WORK_EN OFFSET(23) NUMBITS(1) [],
        TARGET2_WORK_EN OFFSET(22) NUMBITS(1) []
    ],

    pub UNIT_OP [
        UPDATE OFFSET(30) NUMBITS(1) [],
        VALUE_VALID OFFSET(29) NUMBITS(1) []
    ],

    pub UNIT_LOAD_HI [
        LOAD_HI OFFSET(0) NUMBITS(20) []
    ],

    pub UNIT_LOAD_LO [
        LOAD_LO OFFSET(0) NUMBITS(32) []
    ],

    pub UNIT_VALUE_HI [
        VALUE_HI OFFSET(0) NUMBITS(20) []
    ],

    pub UNIT_VALUE_LO [
        VALUE_LO OFFSET(0) NUMBITS(32) []
    ],

    pub UNIT_LOAD [
        LOAD OFFSET(0) NUMBITS(1) []
    ],

    pub TARGET_HI [
        HI OFFSET(0) NUMBITS(20) []
    ],

    pub TARGET_LO [
        LO OFFSET(0) NUMBITS(32) []
    ],

    pub TARGET_CONF [
        PERIOD OFFSET(0) NUMBITS(26) [],
        PERIOD_MODE OFFSET(30) NUMBITS(1) [],
        TIMER_UNIT_SEL OFFSET(31) NUMBITS(1) []
    ],

    pub COMP_LOAD [
        LOAD OFFSET(0) NUMBITS(1) []
    ],

    pub INT_ENA [
        TARGET0 OFFSET(0) NUMBITS(1) [],
        TARGET1 OFFSET(1) NUMBITS(1) [],
        TARGET2 OFFSET(2) NUMBITS(1) []
    ],

    pub INT_RAW [
        TARGET0 OFFSET(0) NUMBITS(1) [],
        TARGET1 OFFSET(1) NUMBITS(1) [],
        TARGET2 OFFSET(2) NUMBITS(1) []
    ],

    pub INT_CLR [
        TARGET0 OFFSET(0) NUMBITS(1) [],
        TARGET1 OFFSET(1) NUMBITS(1) [],
        TARGET2 OFFSET(2) NUMBITS(1) []
    ],

    pub INT_ST [
        TARGET0 OFFSET(0) NUMBITS(1) [],
        TARGET1 OFFSET(1) NUMBITS(1) [],
        TARGET2 OFFSET(2) NUMBITS(1) []
    ]
];

register_structs! {

    Registers {
        (0x00 => conf: ReadWrite<u32, CONF::Register>),
        (0x04 => unit0_op: ReadWrite<u32, UNIT_OP::Register>),
        (0x08 => _reserved0),
        (0x0C => unit0_load_hi: ReadWrite<u32, UNIT_LOAD_HI::Register>),
        (0x10 => unit0_load_lo: ReadWrite<u32, UNIT_LOAD_LO::Register>),
        (0x14 => _reserved1),
        (0x1C => target0_hi: ReadWrite<u32, TARGET_HI::Register>),
        (0x20 => target0_lo: ReadWrite<u32, TARGET_LO::Register>),
        (0x24 => _reserved2),
        (0x34 => target0_conf: ReadWrite<u32, TARGET_CONF::Register>),
        (0x38 => _reserved3),
        (0x40 => unit0_value_hi: ReadWrite<u32, UNIT_VALUE_HI::Register>),
        (0x44 => unit0_value_lo: ReadWrite<u32, UNIT_VALUE_LO::Register>),
        (0x48 => _reserved4),
        (0x50 => comp0_load: ReadWrite<u32, COMP_LOAD::Register>),
        (0x54 => _reserved5),
        (0x5C => unit0_load: ReadWrite<u32, UNIT_LOAD::Register>),
        (0x60 => _reserved6),
        (0x64 => int_ena: ReadWrite<u32, INT_ENA::Register>),
        (0x68 => int_raw: ReadWrite<u32, INT_RAW::Register>),
        (0x6C => int_clr: ReadWrite<u32, INT_CLR::Register>),
        (0x70 => int_st: ReadWrite<u32, INT_ST::Register>),
        (0x74 => @END),
    }
}

/// FIXME: Only Supports Timer Unit 0 for now
pub struct Esp32SysTimer<const BASE_ADDR: usize, const HZ: u64>;

impl<const BASE_ADDR: usize, const HZ: u64> Esp32SysTimer<BASE_ADDR, HZ> {
    fn registers() -> &'static Registers {
        unsafe { &*(BASE_ADDR as *const Registers) }
    }

    fn enable_interrupt(enable: bool) {
        Self::registers().int_ena.modify(if enable {
            INT_ENA::TARGET0::SET
        } else {
            INT_ENA::TARGET0::CLEAR
        });
    }

    pub fn init() {
        // enable unit 0
        Self::registers().conf.modify(CONF::CLK_EN::SET);
        Self::registers().conf.modify(CONF::UNIT0_WORK_EN::SET);
        Self::registers().conf.modify(CONF::TARGET0_WORK_EN::CLEAR);
        // select unit 0 vs comparator 0
        Self::set_unit();
        // CLR interrupt
        Self::registers().int_clr.modify(INT_CLR::TARGET0::SET);
        // disable comparator
        Self::set_comparator_enable(false);
        // enable interrupt
        Self::enable_interrupt(true);
        // set TARGET mode
        Self::registers()
            .target0_conf
            .modify(TARGET_CONF::PERIOD_MODE::CLEAR);
    }

    #[inline]
    pub fn clear_interrupt() {
        Self::registers().int_clr.modify(INT_CLR::TARGET0::SET);
    }

    fn set_unit() {
        Self::registers()
            .target0_conf
            .modify(TARGET_CONF::TIMER_UNIT_SEL::CLEAR);
    }

    pub fn set_comparator_enable(enable: bool) {
        Self::registers().conf.modify(if enable {
            CONF::TARGET0_WORK_EN::SET
        } else {
            CONF::TARGET0_WORK_EN::CLEAR
        });
    }
}

impl<const BASE_ADDR: usize, const HZ: u64> Clock for Esp32SysTimer<BASE_ADDR, HZ> {
    // this code is modified from
    // https://github.com/esp-rs/esp-hal/blob/6100b7d90973539cf73d51e72cc20e6e275a98c6/esp-hal/src/timer/systimer.rs#L371-L387
    // This can be a shared reference as long as this type isn't Sync.
    // FIXME: A stress test should be added to verify whether this API is stalled in multi-task.
    fn estimate_current_cycles() -> u64 {
        Self::registers().unit0_op.modify(UNIT_OP::UPDATE::SET);
        while !Self::registers().unit0_op.is_set(UNIT_OP::VALUE_VALID) {
            Self::registers().unit0_op.modify(UNIT_OP::UPDATE::SET);
        }

        let mut lo_prev = Self::registers()
            .unit0_value_lo
            .read(UNIT_VALUE_LO::VALUE_LO);
        loop {
            let lo = lo_prev;
            let hi = Self::registers()
                .unit0_value_hi
                .read(UNIT_VALUE_HI::VALUE_HI);
            lo_prev = Self::registers()
                .unit0_value_lo
                .read(UNIT_VALUE_LO::VALUE_LO);

            if lo == lo_prev {
                return ((hi as u64) << 32) | lo as u64;
            }
        }
    }

    fn hz() -> u64 {
        HZ
    }

    fn interrupt_at(moment: u64) {
        // Fixme: Alarm cannot be triggered on esp32c3 when the target is too old on the qemu.
        // So we need to add a compensation here to make sure the target is always in the future.
        // See https://github.com/espressif/qemu/issues/69
        let moment = {
            let now = Self::estimate_current_cycles();
            let compensation = core::cmp::max(1, HZ / 2_00); // ~5ms
            let moment = if moment < now + compensation {
                now.saturating_add(compensation)
            } else {
                moment
            };
            moment
        };
        Self::set_comparator_enable(false);
        Self::clear_interrupt();
        Self::registers()
            .target0_conf
            .modify(TARGET_CONF::PERIOD_MODE::CLEAR);
        Self::registers()
            .target0_hi
            .write(TARGET_HI::HI.val((moment >> 32) as u32));
        Self::registers()
            .target0_lo
            .write(TARGET_LO::LO.val((moment & 0xFFFF_FFFF) as u32));

        // load comparator
        Self::registers().comp0_load.write(COMP_LOAD::LOAD::SET);
        Self::set_comparator_enable(true);
    }

    fn stop() {
        Self::set_comparator_enable(false);
    }
}
