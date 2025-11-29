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

mod config;
mod handler;

use crate::{arch, arch::irq::IrqNumber, boot, boot::INIT_BSS_DONE, sync::SpinLock, time};
use alloc::sync::Arc;
use blueos_driver::pinctrl::gd32_afio::*;
use blueos_infra::tinyarc::TinyArc;
use core::ptr::addr_of;
use spin::Once;

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
    unsafe { copy_data() };
    boot::init_runtime();
    use blueos_hal::clock_control::ClockControl;
    blueos_driver::clock_control::gd32_clock_control::Gd32ClockControl::init();

    unsafe { boot::init_heap() };
    arch::irq::init();
    arch::irq::enable_irq_with_priority(IrqNumber::new(37), arch::irq::Priority::Normal);
    time::systick_init(config::PLL_SYS_FREQ as u32);
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::gd32e5x_uart::Gd32e5xUart,
    blueos_driver::uart::gd32e5x_uart::Gd32e5xUart::new(
        0x4001_3800,
        config::PLL_SYS_FREQ as u32,
        crate::boards::get_device!(abp2_rst),
        14
    )),
    (abp1_rst, blueos_driver::reset::gd32_reset::Gd32Reset, blueos_driver::reset::gd32_reset::Gd32Reset::new(
        0x4002_1010
    )),
    (abp2_rst, blueos_driver::reset::gd32_reset::Gd32Reset, blueos_driver::reset::gd32_reset::Gd32Reset::new(
        0x4002_100C
    )),
}

crate::define_pin_states! {
    Gd32AlterfuncIO,
    (
        0x4001_0800,
        9,
        GpioMode::AlterFunc(
            OutputType::OpenDrain,
            OutputSpeed::Fast
        )
    ),
    (
        0x4001_0800,
        10,
        GpioMode::Input(
            InputPullMode::None
        )
    )
}

#[no_mangle]
pub unsafe extern "C" fn uart0_handler() {
    use blueos_hal::HasInterruptReg;
    let uart = get_device!(console_uart);
    if let Some(handler) = unsafe {
        let intr_handler_cell = &*uart.intr_handler.get();

        intr_handler_cell.as_ref()
    } {
        handler();
    }
}
