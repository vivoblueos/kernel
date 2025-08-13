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

// This code is based on [tock](https://github.com/tock/tock/blob/master/chips/rp2040/src/xosc.rs)

// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

use super::static_ref::StaticRef;
use tock_registers::{
    interfaces::{ReadWriteable, Readable},
    register_bitfields, register_structs,
    registers::ReadWrite,
};

register_structs! {
    /// Controls the crystal oscillator
    XoscRegisters {
        /// Crystal Oscillator Control
        (0x000 => ctrl: ReadWrite<u32, CTRL::Register>),
        /// Crystal Oscillator Status
        (0x004 => status: ReadWrite<u32, STATUS::Register>),
        /// Crystal Oscillator pause control\n
        /// This is used to save power by pausing the XOSC\n
        /// On power-up this field is initialised to WAKE\n
        /// An invalid write will also select WAKE\n
        /// WARNING: stop the PLLs before selecting dormant mode\n
        /// WARNING: setup the irq before selecting dormant mode
        (0x008 => dormant: ReadWrite<u32, DORMANT::Register>),
        /// Controls the startup delay
        (0x00C => startup: ReadWrite<u32, STARTUP::Register>),
        /// A down counter running at the xosc frequency which counts to zero and stops.\n
        /// To start the counter write a non-zero value.\n
        /// Can be used for short software pauses when setting up time sensitive
        (0x010 => count: ReadWrite<u32>),
        (0x014 => @END),
    }
}

register_bitfields![u32,
    CTRL [
        /// On power-up this field is initialised to DISABLE and the chip runs
        /// from the ROSC. If the chip has subsequently been programmed to run
        /// from the XOSC then setting this field to DISABLE may lock-up the
        /// chip. If this is a concern then run the clk_ref from the ROSC and
        /// enable the clk_sys RESUS feature. The 12-bit code is intended to give
        /// some protection against accidental writes. An invalid setting will
        /// retain the previous value. The actual value being used can be read from
        /// STATUS_ENABLED
        ENABLE OFFSET(12) NUMBITS(12) [
            ENABLE = 0xfab,
            DISABLE = 0xd1e
        ],
        /// The 12-bit code is intended to give some protection against accidental writes.
        /// An invalid setting will retain the previous value. The actual value being used
        /// can be read from STATUS_FREQ_RANGE
        FREQ_RANGE OFFSET(0) NUMBITS(12) [
            _1_15MHZ = 0xaa0,
            _10_30_MHZ = 0xaa1,
            _25_60_MHZ = 0xaa2,
            _40_100_MHZ = 0xaa3
        ]
    ],
    STATUS [
        /// Oscillator is running and stable
        STABLE OFFSET(31) NUMBITS(1) [],
        /// An invalid value has been written to CTRL_ENABLE or CTRL_FREQ_RANGE or DORMANT
        BADWRITE OFFSET(24) NUMBITS(1) [],
        /// Oscillator is enabled but not necessarily running and stable, resets to 0
        ENABLED OFFSET(12) NUMBITS(1) [],
        /// The current frequency range setting, always reads 0
        FREQ_RANGE OFFSET(0) NUMBITS(2) [
            _1_15MHZ = 0,
            _10_30_MHZ = 1,
            _25_60_MHZ = 2,
            _40_100_MHZ = 3
        ]
    ],
    DORMANT [
        VALUE OFFSET (0) NUMBITS (32) [
            DORMANT = 0x636f6d61,
            WAKE = 0x77616b65
        ]
    ],
    STARTUP [
        /// Multiplies the startup_delay by 4, just in case. The reset
        /// value is controlled by a mask-programmable tiecell and is
        /// provided in case we are booting from XOSC and the default
        /// startup delay is insufficient
        X4 OFFSET(20) NUMBITS(1) [],
        ///  in multiples of 256*xtal_period. The reset value of 0xc4 corresponds
        /// to approx 50 000 cycles.
        DELAY OFFSET(0) NUMBITS(14) []
    ],
    COUNT [
        /// A down counter running at the xosc frequency which counts to zero and stops.
        /// Can be used for short software pauses when setting up time sensitive hardware.
        /// To start the counter, write a non-zero value. Reads will return 1 while the count
        /// is running and 0 when it has finished.
        /// Minimum count value is 4. Count values <4 will be treated as count value =4.
        /// Note that synchronisation to the register clock domain costs 2 register clock
        /// cycles and the counter cannot compensate for that.
        COUNT OFFSET(0) NUMBITS(16) []
    ]
];

const XOSC_BASE: StaticRef<XoscRegisters> =
    unsafe { StaticRef::new(0x40048000 as *const XoscRegisters) };

pub enum XoscError {
    InvaldFrequency,
}

pub fn start_xosc(crystal_freq: usize) -> Result<(), XoscError> {
    let freq_range = match crystal_freq {
        1_000_000..=15_000_000 => CTRL::FREQ_RANGE::_1_15MHZ,
        10_000_000..=30_000_000 => CTRL::FREQ_RANGE::_10_30_MHZ,
        25_000_000..=60_000_000 => CTRL::FREQ_RANGE::_25_60_MHZ,
        40_000_000..=100_000_000 => CTRL::FREQ_RANGE::_40_100_MHZ,
        _ => return Err(XoscError::InvaldFrequency),
    };

    let startup_delay = ((crystal_freq / 1000) + 128) / 256;
    XOSC_BASE
        .startup
        .modify(STARTUP::DELAY.val(startup_delay as u32));
    XOSC_BASE.ctrl.modify(CTRL::ENABLE::ENABLE);
    while !XOSC_BASE.status.is_set(STATUS::STABLE) {}

    Ok(())
}
