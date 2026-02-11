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

// This code is based on
// https://github.com/esp-rs/esp-hal/blob/main/esp-bootloader-esp-idf/src/lib.rs
// Copyright (c) 2024 - present Microsoft Corporation
// SPDX-License-Identifier: MIT

mod config;
use crate::{
    arch,
    arch::riscv::{local_irq_enabled, trap_entry, Context},
    drivers::ic::plic::Plic,
    scheduler,
    support::SmpStagedInit,
    time,
};
use blueos_hal::Has8bitDataReg;
use core::sync::atomic::Ordering;
pub(crate) static PLIC: Plic = Plic::new(config::PLIC_BASE);
// FIXME: Only support unit0 for now
pub type ClockImpl =
    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer<0x6002_3000, 16_000_000>;

core::arch::global_asm!(
    "
.section .trap
.type _vector_table, @function

.option push
.balign 0x4
.option norelax
.option norvc

_vector_table:
    j trap_entry          // 0: Instruction address misaligned
    j trap_entry          // 1: Instruction access fault
    j trap_entry          // 2: Illegal instruction
    j trap_entry          // 3: Breakpoint
    j trap_entry          // 4: Load address misaligned
    j trap_entry          // 5: Load access fault
    j trap_entry          // 6: Store/AMO address misaligned
    j trap_entry          // 7: Store/AMO access fault
    j trap_entry          // 8: Environment call from U-mode
    j trap_entry          // 9: Environment call from S-mode
    j trap_entry          // 10: Reserved
    j trap_entry          // 11: Environment call from M-mode
    j trap_entry          // 12: Instruction page fault
    j trap_entry          // 13: Load page fault
    j trap_entry          // 14: Reserved
    j trap_entry          // 15: Store/AMO page fault
    j trap_entry          // 16: Reserved
    j trap_entry          // 17: Reserved
    j trap_entry          // 18: Reserved
    j trap_entry          // 19: Reserved
    j trap_entry          // 20: Reserved
    j trap_entry          // 21: Reserved
    j trap_entry          // 22: Reserved
    j trap_entry          // 23: Reserved
    j trap_entry          // 24: Reserved
    j trap_entry          // 25: Reserved
    j trap_entry          // 26: Reserved
    j trap_entry          // 27: Reserved
    j trap_entry          // 28: Reserved
    j trap_entry          // 29: Reserved
    j trap_entry          // 30: Reserved
    j trap_entry          // 31: Reserved
    "
);

#[inline]
fn init_vector_table() {
    unsafe extern "C" {
        static _vector_table: u32;
    }
    let mut v = core::ptr::addr_of!(_vector_table) as usize;
    v |= 0x3; // Set MODE to Vectored
    unsafe {
        core::arch::asm!(
            "csrw mtvec, {0}",
            in(reg) v,
            options(nostack, preserves_flags),
        );
    }
}

pub(crate) fn handle_plic_irq(ctx: &Context, mcause: usize, mtval: usize) {
    let cpu_id = arch::current_cpu_id();
    PLIC.complete(cpu_id, PLIC.claim(cpu_id))
}

static STAGING: SmpStagedInit = SmpStagedInit::new();

const INTR_BASE: usize = 0x600c_2000;
const TARGET0_INT_MAP_REG: usize = INTR_BASE + 0x94;
const INT_ENABLE_REG: usize = INTR_BASE + 0x104;
const INT_THRESH_REG: usize = INTR_BASE + 0x194;
const TARGET0_INT_NUM: usize = 1; // IRQ number 16 in target0
const CLOCK_GATE_REG: usize = INTR_BASE + 0x100;

pub(crate) fn init() {
    assert!(!local_irq_enabled());
    unsafe { hal_espressif_rs::soc_init() };

    unsafe {
        crate::boot::INIT_BSS_DONE = true;
    }
    crate::boot::init_runtime();
    crate::boot::init_heap();
    init_vector_table();

    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer::<0x6002_3000, 16_000_000>::init();
    // map target0 interrupt to 16 interrupt
    unsafe {
        core::ptr::write_volatile(CLOCK_GATE_REG as *mut u32, 1);
        core::ptr::write_volatile(TARGET0_INT_MAP_REG as *mut u32, TARGET0_INT_NUM as u32);
        core::ptr::write_volatile(INT_ENABLE_REG as *mut u32, 0xFFFF_FFFF);
        core::ptr::write_volatile(INT_THRESH_REG as *mut u32, 1);
        // hal_espressif_rs::rust_helper_esp_cpu_inter_enable(1 << TARGET0_INT_NUM);
        // hal_espressif_rs::rust_helper_esp_cpu_intr_set_priority(TARGET0_INT_NUM as i32, 1);
    }
    // From now on, all work will be done by core 0.
    // if arch::current_cpu_id() != 0 {
    //     scheduler::wait_and_then_start_schedule();
    //     unreachable!("Secondary cores should have jumped to the scheduler");
    // }
    // Enable TARGET0 in PLIC.
    // PLIC.enable(
    //     arch::current_cpu_id(),
    //     u32::try_from(16usize).expect("usize(64 bits) converts to u32 failed"),
    // );
    // Set TARGET0 priority in PLIC.
    // PLIC.set_priority(
    //     u32::try_from(16usize).expect("usize(64 bits) converts to u32 failed"),
    //     1,
    // );
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::esp32_usb_serial::Esp32UsbSerial,
     blueos_driver::uart::esp32_usb_serial::Esp32UsbSerial),
}

crate::define_pin_states!(None);

#[inline(always)]
pub(crate) fn send_ipi(_hart: usize) {}

#[inline(always)]
pub(crate) fn clear_ipi(_hart: usize) {}

// #[no_mangle]
// pub unsafe extern "C" fn test_memory() {
//     let mut v: u32 = 0;
//     let addr_reg_0 = 0x3c000004usize as *const u32;
//     let addr_reg_1 = 0x3c010004usize as *const u32;
//     let addr_reg_3 = 0x3c018004usize as *const u32;
//     let addr_reg_4 = 0x3c0182c0usize as *const u32;
//     core::arch::asm!(
//         "lw {out}, 0({addr_reg_0})",
//         "lw {out}, 0({addr_reg_1})",
//         "lw {out}, 0({addr_reg_3})",
//         "lw {out}, 0({addr_reg_4})",
//         out = out(reg) v,
//         addr_reg_0 = in(reg) addr_reg_0,
//         addr_reg_1 = in(reg) addr_reg_1,
//         addr_reg_3 = in(reg) addr_reg_3,
//         addr_reg_4 = in(reg) addr_reg_4,
//         options(nostack, preserves_flags),
//     );
// }
