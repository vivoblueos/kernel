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

// This code is based on [tock](https://github.com/tock/tock/blob/master/chips/rp2040/src/clocks.rs)

// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

use crate::boards::raspberry_pico2_cortexm::rp235x::static_ref::StaticRef;
use tock_registers::{
    interfaces::{ReadWriteable, Readable},
    register_bitfields, register_structs,
    registers::ReadWrite,
};

register_structs! {
    PllRegisters {
        /// Control and Status
        /// GENERAL CONSTRAINTS:
        /// Reference clock frequency min=5MHz, max=800MHz
        /// Feedback divider min=16, max=320
        /// VCO frequency min=400MHz, max=1600MHz
        (0x000 => cs: ReadWrite<u32, CS::Register>),
        /// Controls the PLL power modes.
        (0x004 => pwr: ReadWrite<u32, PWR::Register>),
        /// Feedback divisor
        /// (note: this PLL does not support fractional division)
        (0x008 => fbdiv_int: ReadWrite<u32, FBDIV_INT::Register>),
        /// Controls the PLL post dividers for the primary output
        /// (note: this PLL does not have a secondary output)
        /// the primary output is driven from VCO divided by postdiv1*postdiv2
        (0x00C => prim: ReadWrite<u32, PRIM::Register>),
        (0x010 => @END),
    }
}

register_bitfields![u32,
    CS [
        /// PLL is locked
        LOCK OFFSET(31) NUMBITS(1) [],
        /// PLL is not locked
        LOCK_N OFFSET(30) NUMBITS(1) [],
        /// Passes the reference clock to the output instead of the divided VCO. The VCO con
        BYPASS OFFSET(8) NUMBITS(1) [],
        /// Divides the PLL input reference clock.
        /// Behaviour is undefined for div=0.
        /// PLL output will be unpredictable during refdiv changes, wait for
        REFDIV OFFSET(0) NUMBITS(6) []
    ],
    PWR [
        /// PLL VCO powerdown
        /// To save power set high when PLL output not required or bypass=1.
        VCOPD OFFSET(5) NUMBITS(1) [],
        /// PLL post divider powerdown
        /// To save power set high when PLL output not required or bypass=1.
        POSTDIVPD OFFSET(3) NUMBITS(1) [],
        /// PLL DSM powerdown
        /// Nothing is achieved by setting this low.
        DSMPD OFFSET(2) NUMBITS(1) [],
        /// PLL powerdown
        /// To save power set high when PLL output not required.
        PD OFFSET(0) NUMBITS(1) []
    ],
    FBDIV_INT [
        /// see ctrl reg description for constraints
        FBDIV_INT OFFSET(0) NUMBITS(12) []
    ],
    PRIM [
        /// divide by 1-7
        POSTDIV1 OFFSET(16) NUMBITS(3) [],
        /// divide by 1-7
        POSTDIV2 OFFSET(12) NUMBITS(3) []
    ]
];

const PLL_SYS_BASE: StaticRef<PllRegisters> =
    unsafe { StaticRef::new(0x4005_0000 as *const PllRegisters) };

const PLL_USB_BASE: StaticRef<PllRegisters> =
    unsafe { StaticRef::new(0x4005_8000 as *const PllRegisters) };

pub enum PLL {
    Sys,
    Usb,
}

#[derive(Clone, Copy)]
pub struct PLLConfig {
    pub fbdiv: u32,
    pub refdiv: u32,
    pub postdiv1: u32,
    pub postdiv2: u32,
}

pub fn configure_pll(clock: PLL, xosc_freq: u32, config: &PLLConfig) -> u32 {
    let ref_freq = xosc_freq / config.refdiv;

    let pll_base = match clock {
        PLL::Sys => PLL_SYS_BASE,
        PLL::Usb => PLL_USB_BASE,
    };

    let vco_freq = ref_freq * config.fbdiv;

    pll_base
        .pwr
        .modify(PWR::PD::SET + PWR::DSMPD::SET + PWR::POSTDIVPD::SET + PWR::VCOPD::SET);
    pll_base.fbdiv_int.modify(FBDIV_INT::FBDIV_INT.val(0));

    cortex_m::asm::delay(10);

    pll_base.cs.modify(CS::REFDIV.val(config.refdiv));

    pll_base
        .fbdiv_int
        .modify(FBDIV_INT::FBDIV_INT.val(config.fbdiv));

    pll_base.pwr.modify(PWR::PD::CLEAR + PWR::VCOPD::CLEAR);

    while !pll_base.cs.is_set(CS::LOCK) {}

    pll_base
        .prim
        .modify(PRIM::POSTDIV1.val(config.postdiv1) + PRIM::POSTDIV2.val(config.postdiv2));

    pll_base.pwr.modify(PWR::POSTDIVPD::CLEAR);

    cortex_m::asm::delay(100);

    vco_freq / (config.postdiv1 * config.postdiv2)
}
