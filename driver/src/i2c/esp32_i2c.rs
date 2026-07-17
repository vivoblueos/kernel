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

use tock_registers::{register_structs, register_bitfields};

register_structs! {
    I2cRegisters {
        (0x00 => scl_low_period: ReadWrite<u32, SCL_LOW_PERIOD::Register>),
        (0x04 => _reserved0),
        (0x30 => sda_hold: ReadWrite<u32, SDA_HOLD::Register>),
        (0x34 => @END),
    }
}

register_bitfields! [u32,
    SCL_LOW_PERIOD [
        SCL_LOW_PERIOD OFFSET(0) NUMBITS(9) []
    ],
    SDA_HOLD [
        SDA_HOLD_TIME OFFSET(0) NUMBITS(9) []
    ]
]
