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

pub mod config;
mod handlers;
pub mod uart;
pub(crate) use uart::get_early_uart; // re-export
use uart::{get_serial, uart_init};

use crate::{
    arch, boot,
    devices::{console, tty::n_tty::Tty},
    error::Error,
    time,
};
use alloc::{string::String, sync::Arc};
use boot::INIT_BSS_DONE;
use core::ptr::addr_of;

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
        copy_data();
    }
    boot::init_runtime();
    unsafe { boot::init_heap() };
    arch::irq::init();
    time::systick_init(config::SYSTEM_CORE_CLOCK);
    match uart_init(
        0,
        config::memory_map::UART0_BASE_S,
        config::SYSTEM_CORE_CLOCK,
        config::UART0RX_IRQn,
        config::UART0TX_IRQn,
        String::from("ttyS0"),
    ) {
        Ok(_) => (),
        Err(e) => panic!("Failed to init uart: {}", Error::from(e)),
    }
    match console::init_console(Tty::init(get_serial(0).clone()).clone()) {
        Ok(_) => (),
        Err(e) => panic!("Failed to init console: {}", Error::from(e)),
    }
}

// FIXME: support float
pub(crate) fn get_cycles_to_duration(cycles: u64) -> core::time::Duration {
    return core::time::Duration::from_nanos(
        (cycles as u128 * 1_000_000_000 as u128 / config::SYSTEM_CORE_CLOCK as u128) as u64,
    );
}

pub(crate) fn get_cycles_to_ms(cycles: u64) -> u64 {
    return (cycles as u128 * 1_000 as u128 / config::SYSTEM_CORE_CLOCK as u128) as u64;
}
