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

//! ESP32-C6 hardware random number readout.
//!
//! Comparison with C3:
//! - RNG base: C6 = 0x600B_2800 (C3 is in the SYSTEM domain at 0x6002_60B0).
//!   Source: esp32c6-0.23.0 pac crate lib.rs: `RNG = Periph<rng::RegisterBlock, 0x600b_2800>`.
//! - data register offset: C6 = 0x08 (pac crate rng.rs comment `0x08 - Random number data`).
//!   C3 reads the raw address 0x6002_60B0 directly (equivalent to base+0x00, the DATA register).
//!   Hence C6 reads (0x600B_2800 + 0x08).

const RNG_DATA_REG: usize = 0x600B_2800 + 0x08;

pub struct Esp32c6Rng;

impl Esp32c6Rng {
    pub const fn new() -> Self {
        Self
    }
    pub fn read_one(&self) -> u32 {
        unsafe { core::ptr::read_volatile(RNG_DATA_REG as *const u32) }
    }
}
