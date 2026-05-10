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

use core::ptr::addr_of;

core::arch::global_asm!(
    "
.section .text.vector_table
.align 11
.global vector_table
vector_table:
    .align 7
        b el0_not_supported
    .align 7
        b el0_not_supported
    .align 7
        b el0_not_supported
    .align 7
        b el0_not_supported

    .align 7
        b el1_sync
    .align 7
        b el1_irq
    .align 7
        b el1_fiq
    .align 7
        b el1_error

    .align 7
        b lowerel_not_supported
    .align 7
        b lowerel_not_supported
    .align 7
        b lowerel_not_supported
    .align 7
        b lowerel_not_supported

    .align 7
        b lowerel_not_supported
    .align 7
        b lowerel_not_supported
    .align 7
        b lowerel_not_supported
    .align 7
        b lowerel_not_supported
"
);

unsafe extern "C" {
    static vector_table: u8;
}

pub fn init() {
    unsafe {
        let vector = addr_of!(vector_table) as u64;
        core::arch::asm!("msr vbar_el1, {}", in(reg) vector, options(nostack));
    }
}
