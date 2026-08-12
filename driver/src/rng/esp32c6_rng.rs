// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! ESP32-C6 硬件随机数读取。
//!
//! 与 C3 对比:
//! - RNG 基址:C6 = 0x600B_2800(C3 在 SYSTEM 域 0x6002_60B0)。
//!   来源 esp32c6-0.23.0 pac crate lib.rs: `RNG = Periph<rng::RegisterBlock, 0x600b_2800>`。
//! - data 寄存器偏移:C6 = 0x08(pac crate rng.rs 注释 `0x08 - Random number data`)。
//!   C3 是裸地址直接读 0x6002_60B0(等价于 base+0x00 的 DATA 寄存器)。
//!   因此 C6 读 (0x600B_2800 + 0x08)。

/// C6 RNG 数据寄存器地址 = 基址 0x600B_2800 + data 偏移 0x08。
const RNG_DATA_REG: usize = 0x600B_2800 + 0x08;

pub struct Esp32c6Rng;

impl Esp32c6Rng {
    pub const fn new() -> Self {
        Self
    }

    /// 读一个 32 位随机数。读 RNG data 寄存器每次返回一个新随机值。
    pub fn read_one(&self) -> u32 {
        unsafe { core::ptr::read_volatile(RNG_DATA_REG as *const u32) }
    }
}
