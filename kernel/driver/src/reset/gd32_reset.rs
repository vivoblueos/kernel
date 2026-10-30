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

use blueos_hal::{reset::ResetCtrl, PlatPeri};

pub struct Gd32Reset {
    inner: usize,
}

impl Gd32Reset {
    pub const fn new(inner: usize) -> Self {
        Gd32Reset { inner }
    }
}

unsafe impl Send for Gd32Reset {}
unsafe impl Sync for Gd32Reset {}

impl PlatPeri for Gd32Reset {}

impl ResetCtrl for Gd32Reset {
    fn clear_reset(&self, id: u32) {
        unsafe {
            let temp = core::ptr::read_volatile(self.inner as *const u32);
            core::ptr::write_volatile(self.inner as *mut u32, temp & !(1u32 << id));
        }
    }

    fn set_reset(&self, id: u32) {
        unsafe {
            let temp = core::ptr::read_volatile(self.inner as *const u32);
            core::ptr::write_volatile(self.inner as *mut u32, temp | (1u32 << id));
        }
    }
}
