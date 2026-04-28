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

use core::arch::asm;

pub const GUEST_CODE_LOAD_ADDR: usize = 0x4100_0000;
pub const GUEST_STACK_SIZE: usize = 32 * 1024;
pub const GUEST_STACK_TOP: usize = 0x4110_0000 - 16;
const GUEST_STACK_TOP_LO: u16 = (GUEST_STACK_TOP & 0xFFFF) as u16;
const GUEST_STACK_TOP_HI: u16 = ((GUEST_STACK_TOP >> 16) & 0xFFFF) as u16;
pub const LINUX_KERNEL_LOAD_ADDR: usize = 0x4400_0000;
pub const LINUX_DTB_ADDR: usize = 0x4E00_0000;

/// Get guest stack top address.
#[inline]
pub fn guest_stack_top() -> usize {
    GUEST_STACK_TOP
}