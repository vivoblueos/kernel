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

mod config;
use crate::{
    arch,
    arch::riscv::{local_irq_enabled, trap_entry, Context},
    scheduler, time,
};
use blueos_driver::interrupt_controller::Interrupt;
use blueos_hal::Has8bitDataReg;
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
    j {trap_entry}          // 0: Exception 
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    j {trap_entry}          
    ",
    trap_entry = sym trap_entry,
);

#[inline]
fn init_vector_table() {
    unsafe extern "C" {
        static _vector_table: u32;
    }
    let mut v = core::ptr::addr_of!(_vector_table) as usize;
    // v |= 0x3; // Set MODE to Vectored
    unsafe {
        core::arch::asm!(
            "csrw mtvec, {0}",
            in(reg) v,
            options(nostack, preserves_flags),
        );
    }
}

pub(crate) fn handle_intc_irq(ctx: &Context, mcause: usize, mtval: usize) {
    let cpu_id = arch::current_cpu_id();
    match mcause & 0xff {
        TARGET0_INT_NUM => {
            ClockImpl::clear_interrupt();
            crate::time::handle_clock_interrupt();
        }
        USB_SERIAL_JTAG_INT_NUM => {
            usb_serial_jtag_interrupt_handler();
        }
        _ => {}
    }
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
