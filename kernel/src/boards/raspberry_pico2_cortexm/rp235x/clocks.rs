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

use super::static_ref::StaticRef;
use tock_registers::{
    interfaces::{ReadWriteable, Readable},
    register_bitfields, register_structs,
    registers::{ReadOnly, ReadWrite},
};

register_structs! {
    GpioClockRegisters {
        /// Clock control, can be changed on-the-fly (except for auxsrc)
        (0x000 => ctrl: ReadWrite<u32, CLK_GPOUTx_CTRL::Register>),
        /// Clock divisor, can be changed on-the-fly
        (0x004 => div: ReadWrite<u32, CLK_GPOUTx_DIV::Register>),
        /// Indicates which src is currently selected (one-hot)
        (0x008 => selected: ReadOnly<u32, CLK_GPOUTx_SELECTED::Register>),
        (0x00C => @END),
    },
    ClocksRegisters {
        (0x000 => clk_gpio: [GpioClockRegisters; 4]),
        /// Clock control, can be changed on-the-fly (except for auxsrc)
        (0x030 => clk_ref_ctrl: ReadWrite<u32, CLK_REF_CTRL::Register>),
        /// Clock divisor, can be changed on-the-fly
        (0x034 => clk_ref_div: ReadWrite<u32, CLK_REF_DIV::Register>),
        /// Indicates which src is currently selected (one-hot)
        (0x038 => clk_ref_selected: ReadOnly<u32, CLK_REF_SELECTED::Register>),
        /// Clock control, can be changed on-the-fly (except for auxsrc)
        (0x03C => clk_sys_ctrl: ReadWrite<u32, CLK_SYS_CTRL::Register>),
        /// Clock divisor, can be changed on-the-fly
        (0x040 => clk_sys_div: ReadWrite<u32, CLK_SYS_DIV::Register>),
        /// Indicates which src is currently selected (one-hot)
        (0x044 => clk_sys_selected: ReadOnly<u32, CLK_SYS_SELECTED::Register>),
        /// Clock control, can be changed on-the-fly (except for auxsrc)
        (0x048 => clk_peri_ctrl: ReadWrite<u32, CLK_PERI_CTRL::Register>),
        (0x04c => clk_peri_div: ReadWrite<u32, CLK_PERI_DIV::Register>),
        (0x050 => clk_peri_selected: ReadOnly<u32, CLK_PERI_SELECTED::Register>),
        /// Clock control, can be changed on-the-fly (except for auxsrc)
        (0x054 => clk_hstx_ctrl: ReadWrite<u32, CLK_HSTX_CTRL::Register>),
        /// Clock divisor, can be changed on-the-fly
        (0x058 => clk_hstx_div: ReadWrite<u32, CLK_HSTX_DIV::Register>),
        /// Indicates which src is currently selected (one-hot)
        (0x05C => clk_hstx_selected: ReadOnly<u32, CLK_HSTX_SELECTED::Register>),
        (0x060 => _reserved0),
        (0x084 => clk_sys_resus_ctrl: ReadWrite<u32, CLK_SYS_RESUS_CTRL::Register>),
        (0x088 => clk_sys_resus_status: ReadWrite<u32>),
        (0x08C => @END),
    }
}

register_bitfields![u32,
    CLK_GPOUTx_CTRL [
        /// clock generator is enabled
        ENABLED OFFSET(28) NUMBITS(1) [],
        /// An edge on this signal shifts the phase of the output by 1 cycle of the input cl
        /// This can be done at any time
        NUDGE OFFSET(20) NUMBITS(1) [],
        /// This delays the enable signal by up to 3 cycles of the input clock
        /// This must be set before the clock is enabled to have any effect
        PHASE OFFSET(16) NUMBITS(2) [],
        /// Enables duty cycle correction for odd divisors
        DC50 OFFSET(12) NUMBITS(1) [],
        /// Starts and stops the clock generator cleanly
        ENABLE OFFSET(11) NUMBITS(1) [],
        /// Asynchronously kills the clock generator
        KILL OFFSET(10) NUMBITS(1) [],
        /// Selects the auxiliary clock source, will glitch when switching
        AUXSRC OFFSET(5) NUMBITS(4) [
            CLKSRC_PLL_SYS = 0,
            CLKSRC_GPIN0 = 1,
            CLKSRC_GPIN1 = 2,
            CLKSRC_PLL_USB = 3,
            CLKSRC_PLL_USB_PRIMARY_REF_OPCG = 4,
            ROSC_CLKSRC = 5,
            XOSC_CLKSRC = 6,
            LPOSC_CLKSRC = 7,
            CLK_SYS = 8,
            CLK_USB = 9,
            CLK_ADC = 0xa,
            CLK_REF = 0xb,
            CLK_PERI = 0xc,
            CLK_HSTX = 0xd,
            OTP_CLK2FC = 0xe,
        ]
    ],
    CLK_GPOUTx_DIV [
        /// Integer part of clock divisor, 0 → max+1, can be changed on-the-fly
        INT OFFSET(16) NUMBITS(16) [],
        /// Fractional component of the divisor, can be changed on-the-fly
        FRAC OFFSET(0) NUMBITS(16) []
    ],
    CLK_GPOUTx_SELECTED [
        VALUE OFFSET (0) NUMBITS (1) []
    ],
    CLK_REF_CTRL [
        /// Selects the auxiliary clock source, will glitch when switching
        AUXSRC OFFSET(5) NUMBITS(2) [
            CLKSRC_PLL_USB = 0x0,
            CLKSRC_GPIN0 = 0x1,
            CLKSRC_GPIN1 = 0x2,
            CLKSRC_PLL_USB_PRIMARY_REF_OPCG = 0x3,
        ],
        /// Selects the clock source glitchlessly, can be changed on-the-fly
        SRC OFFSET(0) NUMBITS(2) [
            ROSC_CLKSRC_PH = 0x0,
            CLKSRC_CLK_REF_AUX = 0x1,
            XOSC_CLKSRC = 0x2,
            LPOSC_CLKSRC = 0x3
        ]
    ],
    CLK_REF_DIV [
        /// Integer part of clock divisor, 0 → max+1, can be changed on-the-fly
        INT OFFSET(16) NUMBITS(8) []
    ],
    CLK_REF_SELECTED [
        VALUE OFFSET (0) NUMBITS (4) []
    ],
    CLK_SYS_CTRL [
        /// Selects the auxiliary clock source, will glitch when switching
        AUXSRC OFFSET(5) NUMBITS(3) [

            CLKSRC_PLL_SYS = 0x0,
            CLKSRC_PLL_USB = 0x1,
            ROSC_CLKSRC = 0x2,
            XOSC_CLKSRC = 0x3,
            CLKSRC_GPIN0 = 0x4,
            CLKSRC_GPIN1 = 0x5
        ],
        /// Selects the clock source glitchlessly, can be changed on-the-fly
        SRC OFFSET(0) NUMBITS(1) [
            CLKSRC_CLK_SYS_AUX = 1,
            CLK_REF = 0,
        ]
    ],
    CLK_SYS_DIV [
        /// Integer part of clock divisor, 0 → max+1, can be changed on-the-fly
        INT OFFSET(16) NUMBITS(16) [],
        /// Fractional component of the divisor, can be changed on-the-fly
        FRAC OFFSET(0) NUMBITS(16) []
    ],
    CLK_SYS_SELECTED [
        VALUE OFFSET (0) NUMBITS (2) []
    ],
    CLK_PERI_CTRL [
        ENABLED OFFSET(28) NUMBITS(1) [],
        /// Starts and stops the clock generator cleanly
        ENABLE OFFSET(11) NUMBITS(1) [],
        /// Asynchronously kills the clock generator
        KILL OFFSET(10) NUMBITS(1) [],
        /// Selects the auxiliary clock source, will glitch when switching
        AUXSRC OFFSET(5) NUMBITS(3) [
            CLK_SYS = 0,
            CLKSRC_PLL_SYS = 1,
            CLKSRC_PLL_USB = 2,
            ROSC_CLKSRC_PH = 3,
            XOSC_CLKSRC = 4,
            CLKSRC_GPIN0 = 5,
            CLKSRC_GPIN1 = 6
        ]
    ],
    CLK_PERI_DIV [
        /// Integer part of clock divisor, 0 → max+1, can be changed on-the-fly
        INT OFFSET(16) NUMBITS(2) [],
    ],
    CLK_PERI_SELECTED [
        VALUE OFFSET (0) NUMBITS (1) []
    ],
    CLK_HSTX_CTRL [
        ENABLED OFFSET(28) NUMBITS(1) [],
        NUDGE OFFSET(20) NUMBITS(1) [],
        PHASE OFFSET(16) NUMBITS(2) [],
        ENABLE OFFSET(11) NUMBITS(1) [],
        KILL OFFSET(10) NUMBITS(1) [],
        AUXSRC OFFSET(5) NUMBITS(3) [
            CLK_SYS = 0,
            CLKSRC_PLL_SYS = 1,
            CLKSRC_PLL_USB = 2,
            CLKSRC_GPIN0 = 3,
            CLKSRC_GPIN1 = 4,
        ]
    ],
    CLK_HSTX_DIV [
        INT OFFSET(16) NUMBITS(2) [],
    ],
    CLK_HSTX_SELECTED [
        VALUE OFFSET (0) NUMBITS (1) []
    ],
    CLK_SYS_RESUS_CTRL [
        /// For clearing the resus after the fault that triggered it has been corrected
        CLEAR OFFSET(16) NUMBITS(1) [],
        /// Force a resus, for test purposes only
        FRCE OFFSET(12) NUMBITS(1) [],
        /// Enable resus
        ENABLE OFFSET(8) NUMBITS(1) [],
        /// This is expressed as a number of clk_ref cycles
        /// and must be >= 2x clk_ref_freq/min_clk_tst_freq
        TIMEOUT OFFSET(0) NUMBITS(8) []
    ],
    CLK_SYS_RESUS_STATUS [
        /// Clock has been resuscitated, correct the error then send ctrl_clear=1
        RESUSSED OFFSET(0) NUMBITS(1) []
    ],
];

#[derive(Copy, Clone, PartialEq, Debug)]
#[repr(u8)]
pub enum ReferenceClockSource {
    Rsoc = 0,
    Auxiliary = 1,
    Xosc = 2,
    Lposc = 3,
}

#[derive(Copy, Clone, PartialEq, Debug)]
#[repr(u8)]
pub enum ReferenceAuxiliaryClockSource {
    PllUsb = 0,
    Gpio0 = 1,
    Gpio1 = 2,
    PllUsbPrimaryRefOpcg = 3,
}

#[derive(Copy, Clone, PartialEq, Debug)]
#[repr(u8)]
pub enum SystemClockSource {
    Reference = 0,
    Auxiliary = 1,
}

#[derive(Copy, Clone, PartialEq, Debug)]
#[repr(u8)]
pub enum SystemAuxiliaryClockSource {
    PllSys = 0,
    PllUsb = 1,
    Rsoc = 2,
    Xsoc = 3,
    Gpio0 = 4,
    Gpio1 = 5,
}

#[derive(Copy, Clone, PartialEq, Debug)]
#[repr(u8)]
pub enum PeripheralAuxiliaryClockSource {
    System = 0,
    PllSys = 1,
    PllUsb = 2,
    Rsoc = 3,
    Xsoc = 4,
    Gpio0 = 5,
    Gpio1 = 6,
}

const CLOCKS_BASE: StaticRef<ClocksRegisters> =
    unsafe { StaticRef::new(0x40010000 as *const ClocksRegisters) };

pub fn disable_clk_sys_resus() {
    CLOCKS_BASE
        .clk_sys_resus_ctrl
        .modify(CLK_SYS_RESUS_CTRL::ENABLE::CLEAR);
}

pub fn disable_sys_aux() {
    CLOCKS_BASE.clk_sys_ctrl.modify(CLK_SYS_CTRL::SRC::CLK_REF);
    while !CLOCKS_BASE.clk_sys_selected.is_set(CLK_SYS_SELECTED::VALUE) {}
}

pub fn disable_ref_aux() {
    CLOCKS_BASE
        .clk_ref_ctrl
        .modify(CLK_REF_CTRL::SRC::ROSC_CLKSRC_PH);
    while !CLOCKS_BASE.clk_ref_selected.is_set(CLK_REF_SELECTED::VALUE) {}
}

pub fn configure_system_clock(
    src_clk: SystemClockSource,
    aux_clk: SystemAuxiliaryClockSource,
    div_int: u16,
    div_frac: u16,
) {
    let clk_sys = &CLOCKS_BASE.clk_sys_ctrl;
    let clk_sys_div = &CLOCKS_BASE.clk_sys_div;
    let clk_sys_selected = &CLOCKS_BASE.clk_sys_selected;

    clk_sys.modify(CLK_SYS_CTRL::SRC.val(src_clk as u32));
    clk_sys.modify(CLK_SYS_CTRL::AUXSRC.val(aux_clk as u32));

    clk_sys_div.modify(CLK_SYS_DIV::INT.val(div_int as u32));
    clk_sys_div.modify(CLK_SYS_DIV::FRAC.val(div_frac as u32));

    while !clk_sys_selected.is_set(CLK_SYS_SELECTED::VALUE) {}
}

pub fn configure_reference_clock(
    src_clk: ReferenceClockSource,
    aux_clk: ReferenceAuxiliaryClockSource,
    div: u8,
) {
    let clk_ref = &CLOCKS_BASE.clk_ref_ctrl;
    let clk_ref_div = &CLOCKS_BASE.clk_ref_div;
    let clk_ref_selected = &CLOCKS_BASE.clk_ref_selected;

    clk_ref.modify(CLK_REF_CTRL::SRC.val(src_clk as u32));
    clk_ref.modify(CLK_REF_CTRL::AUXSRC.val(aux_clk as u32));
    clk_ref_div.modify(CLK_REF_DIV::INT.val(div as u32));

    while !clk_ref_selected.is_set(CLK_REF_SELECTED::VALUE) {}
}

pub fn configure_peripheral_clock(aux_clk: PeripheralAuxiliaryClockSource) {
    let clk_peri = &CLOCKS_BASE.clk_peri_ctrl;

    clk_peri.modify(CLK_PERI_CTRL::ENABLE::CLEAR);
    cortex_m::asm::delay(3);

    clk_peri.modify(CLK_PERI_CTRL::AUXSRC.val(aux_clk as u32));

    clk_peri.modify(CLK_PERI_CTRL::ENABLE::SET);
}
