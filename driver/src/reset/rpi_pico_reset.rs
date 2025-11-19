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

use blueos_hal::{
    reset::{HasDoneReg, ResetCtrl, ResetCtrlWithDone},
    PlatPeri,
};

pub struct RpiPicoReset {
    inner: usize,
}

impl RpiPicoReset {
    pub const fn new(inner: usize) -> Self {
        RpiPicoReset { inner }
    }

    fn get_done_id(id: u32) -> u32 {
        id
    }

    fn get_reset_id(id: u32) -> u32 {
        id
    }
}

unsafe impl Send for RpiPicoReset {}
unsafe impl Sync for RpiPicoReset {}

impl PlatPeri for RpiPicoReset {}

impl ResetCtrl for RpiPicoReset {
    fn set_reset(&self, id: u32) {
        unsafe {
            let reset_id = RpiPicoReset::get_reset_id(id);
            let temp = core::ptr::read_volatile(self.inner as *const u32);
            core::ptr::write_volatile(self.inner as *mut u32, temp | (1u32 << reset_id));
        }
    }

    fn clear_reset(&self, id: u32) {
        unsafe {
            let reset_id = RpiPicoReset::get_reset_id(id);
            let temp = core::ptr::read_volatile(self.inner as *const u32);
            core::ptr::write_volatile(self.inner as *mut u32, temp & !(1u32 << reset_id));
        }
    }
}

impl HasDoneReg for RpiPicoReset {
    fn is_done(&self, id: u32) -> bool {
        unsafe {
            let done_id = RpiPicoReset::get_done_id(id);
            (core::ptr::read_volatile((self.inner + 0x008) as *const u32) & (1u32 << done_id)) != 0
        }
    }
}

impl ResetCtrlWithDone for RpiPicoReset {}
