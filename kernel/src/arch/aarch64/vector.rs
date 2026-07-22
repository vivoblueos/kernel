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

use crate::arch::registers::vbar_el1::VBAR_EL1;
use core::ptr::addr_of;
use tock_registers::interfaces::Writeable;
// Exception vector table
core::arch::global_asm!(
    "
.section .text.vector_table
// 2048 bytes alignment for vector table
.align 11 
.global vector_table
vector_table:
    // Current EL with SP0
    .align 7
        b el0_not_supported       // Synchronous
    .align 7
        b el0_not_supported       // IRQ
    .align 7
        b el0_not_supported       // FIQ 
    .align 7
        b el0_not_supported       // SError

    // Current EL with SPx
    .align 7
        b el1_sync                // Synchronous
    .align 7
        b el1_irq                 // IRQ
    .align 7
        b el1_fiq                 // FIQ
    .align 7
        b el1_error               // SError

    // Lower EL using AArch64
    .align 7
        b el0_sync                // Synchronous (SVC, Data Abort, etc.)
    .align 7
        b el0_irq                 // IRQ
    .align 7
        b el0_fiq                 // FIQ
    .align 7
        b el0_serror              // SError

    // Lower EL using AArch32
    .align 7
        b lowerel_not_supported    // Synchronous
    .align 7
        b lowerel_not_supported    // IRQ
    .align 7
        b lowerel_not_supported    // FIQ
    .align 7
        b lowerel_not_supported    // SError
"
);

extern "C" {
    static vector_table: u8;
}

pub fn init() {
    unsafe {
        VBAR_EL1.set(addr_of!(vector_table) as u64);
    }
}
