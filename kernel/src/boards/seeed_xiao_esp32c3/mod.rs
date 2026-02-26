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
use blueos_driver::interrupt_controller::Interrupt;
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
    match mcause & 0xff {
        TARGET0_INT_NUM => {
            ClockImpl::clr_interrupt();
            crate::time::handle_clock_interrupt();
        }
        USB_SERIAL_JTAG_INT_NUM => {
            usb_serial_jtag_interrupt_handler();
        }
        _ => {}
    }
    // PLIC.complete(cpu_id, PLIC.claim(cpu_id))
}

const TARGET0_INT_NUM: usize = 16;

const USB_SERIAL_JTAG_INT_NUM: usize = 15;

const RTC_CNTL_BASE: usize = 0x6000_8000;
const RTC_CNTL_WDTWRITECT_REG: usize = RTC_CNTL_BASE + 0xA8;
const RTC_CNTL_WDTCONFIG0_REG: usize = RTC_CNTL_BASE + 0x90;

const USB_SERIAL_JTAG_IRQ: Interrupt = Interrupt::new(26, 15);
const SYSTIMER_TARGET0_IRQ: Interrupt = Interrupt::new(37, 16);

pub(crate) fn init() {
    assert!(!local_irq_enabled());

    crate::boot::init_runtime();
    crate::boot::init_heap();
    init_vector_table();

    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer::<0x6002_3000, 16_000_000>::init();

    unsafe {
        // disable WDT to avoid unexpected reset
        core::ptr::write_volatile(RTC_CNTL_WDTWRITECT_REG as *mut u32, 0x50D83AA1);
        core::ptr::write_volatile(RTC_CNTL_WDTCONFIG0_REG as *mut u32, 0);
        core::ptr::write_volatile(RTC_CNTL_WDTWRITECT_REG as *mut u32, 0);
    }

    get_device!(intc).alloc_irq(SYSTIMER_TARGET0_IRQ);
    get_device!(intc).alloc_irq(USB_SERIAL_JTAG_IRQ);

    get_device!(intc).set_thresh(1);

    get_device!(intc).set_priority(USB_SERIAL_JTAG_IRQ, 15);
    get_device!(intc).set_priority(SYSTIMER_TARGET0_IRQ, 15);
    get_device!(intc).enable_irq(SYSTIMER_TARGET0_IRQ);
    get_device!(intc).enable_irq(USB_SERIAL_JTAG_IRQ);
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::esp32_usb_serial::Esp32UsbSerial,
     blueos_driver::uart::esp32_usb_serial::Esp32UsbSerial::new()),
    (intc, blueos_driver::interrupt_controller::esp32_intc::Esp32Intc,
     blueos_driver::interrupt_controller::esp32_intc::Esp32Intc::new(0x600c_2000)),
}

crate::define_pin_states!(None);

#[inline(always)]
pub(crate) fn send_ipi(_hart: usize) {}

#[inline(always)]
pub(crate) fn clear_ipi(_hart: usize) {}

pub fn usb_serial_jtag_interrupt_handler() {
    use blueos_hal::HasInterruptReg;
    let uart = get_device!(console_uart);
    let intr = uart.get_interrupt();
    if let Some(handler) = unsafe {
        let intr_handler_cell = &*uart.intr_handler.get();

        intr_handler_cell.as_ref()
    } {
        handler();
    }
    uart.clear_interrupt(intr);
}
