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

use crate::boards::raspberry_pico2_cortexm::rp235x::pll::PLLConfig;

pub const XOSC_FREQ: usize = 12_000_000; // 12 MHz
pub const PLL_SYS_150MHZ: PLLConfig = PLLConfig {
    fbdiv: 125,
    refdiv: 1,
    postdiv1: 5,
    postdiv2: 2,
};
pub const PLL_SYS_FREQ: usize = 150_000_000; // 150 MHz

pub const PLL_USB_48MHZ: PLLConfig = PLLConfig {
    fbdiv: 100,
    refdiv: 1,
    postdiv1: 5,
    postdiv2: 5,
};
