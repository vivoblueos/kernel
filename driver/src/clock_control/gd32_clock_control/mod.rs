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

#[cfg(target_chip = "gd32e5x")]
mod rcu;

use blueos_hal::clock_control::ClockControl;
use gd32e5::gd32e507;

pub struct Gd32ClockControl;

cfg_if::cfg_if! {
    if #[cfg(target_chip = "gd32e5x")] {
        use rcu::init_soc;
    } else if #[cfg(target_chip = "gd32vw55x")] {
        unsafe extern "C" {
            fn init_soc();
        }
    }
}

impl ClockControl for Gd32ClockControl {
    fn init() {
        // GD32 specific clock initialization code
        unsafe {
            init_soc();
        }
    }
}
