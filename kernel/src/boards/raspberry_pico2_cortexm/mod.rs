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

mod block;
mod handler;

use crate::{
    arch::{self, irq::IrqNumber},
    boot,
    boot::INIT_BSS_DONE,
    time,
};
use blueos_hal::clock_control::ClockControl;
use core::ptr::addr_of;
use spin::Once;

#[link_section = ".start_block"]
#[used]
pub static IMAGE_DEF: block::ImageDef = block::ImageDef::secure_exe();

#[repr(C)]
struct CopyTable {
    src: *const u32,
    dest: *mut u32,
    wlen: u32,
}

#[repr(C)]
struct ZeroTable {
    dest: *mut u32,
    wlen: u32,
}

// Copy data from FLASH to RAM.
#[inline(never)]
unsafe fn copy_data() {
    extern "C" {
        static __zero_table_start: ZeroTable;
        static __zero_table_end: ZeroTable;
        static __copy_table_start: CopyTable;
        static __copy_table_end: CopyTable;
    }

    let mut p_table = addr_of!(__copy_table_start);
    while p_table < addr_of!(__copy_table_end) {
        let table = &(*p_table);
        for i in 0..table.wlen {
            core::ptr::write(
                table.dest.add(i as usize),
                core::ptr::read(table.src.add(i as usize)),
            );
        }
        p_table = p_table.offset(1);
    }

    let mut p_table = addr_of!(__zero_table_start);
    while p_table < addr_of!(__zero_table_end) {
        let table = &*p_table;
        for i in 0..table.wlen {
            core::ptr::write(table.dest.add(i as usize), 0);
        }
        p_table = p_table.offset(1);
    }
    INIT_BSS_DONE = true;
}

pub(crate) fn init() {
    unsafe {
        const SCB_CPACR_PTR: *mut u32 = 0xE000_ED88 as *mut u32;
        const SCB_CPACR_FULL_ACCESS: u32 = 0b11;
        let mut temp = SCB_CPACR_PTR.read_volatile();
        temp |= SCB_CPACR_FULL_ACCESS << (4 * 2);
        temp |= 0x00F00000;
        SCB_CPACR_PTR.write_volatile(temp);
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
        copy_data();
    }
    boot::init_runtime();
    blueos_driver::clock_control::rpi_pico::RpiPicoClockControl::init();

    unsafe { boot::init_heap() };
    arch::irq::init();
    arch::irq::enable_irq_with_priority(IrqNumber::new(33), arch::irq::Priority::Normal);
    time::systick_init(150_000_000);
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::arm_pl011::ArmPl011<'static>,
     blueos_driver::uart::arm_pl011::ArmPl011::<'static>::new(
        0x40070000 as _,
        150_000_000,
        Some((get_device!(subsys_reset), 26)),
     )),
    (subsys_reset, blueos_driver::reset::rpi_pico_reset::RpiPicoReset,
    blueos_driver::reset::rpi_pico_reset::RpiPicoReset::new(
        0x40020000
    )),
    (i2c1, blueos_driver::i2c::i2c_dw::I2cDw,
     blueos_driver::i2c::i2c_dw::I2cDw::new(
        0x40090000,
        150_000_000,
        Some((get_device!(subsys_reset), 5)),
     )),
}

crate::define_pin_states!(
    blueos_driver::pinctrl::rpi_pico::RpiPicoPinctrl,
    (2, 11), // GPIO2 as UART0_TX
    (3, 11), // GPIO3 as UART0_RX
    (4, 3),  // GPIO4 as I2C0_SDA
    (5, 3),  // GPIO5 as I2C0_SCL
);

#[no_mangle]
pub unsafe extern "C" fn uart0_handler() {
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
