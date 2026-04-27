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
use crate::{
    arch,
    boards::config::{
        memory_map, UART0RX_IRQn, UART0TX_IRQn, SYSTEM_CORE_CLOCK, UART0RX_IRQ_N, UART0TX_IRQ_N,
    },
    boot,
    devices::clock::systick,
};
use blueos_driver::uart::cmsdk::{CmsdkRxIsr, CmsdkTxIsr};
use blueos_hal::clock::Clock;
use boot::INIT_BSS_DONE;
use core::ptr::{addr_of, NonNull};

#[repr(C)]
struct CopyTable {
    src: *const u32,
    dst: *mut u32,
    size: u32,
}

#[repr(C)]
struct ZeroTable {
    dst: *mut u32,
    size: u32,
}

// Copy data from FLASH to RAM.
unsafe fn copy_data() {
    extern "C" {
        static __zero_table_start: ZeroTable;
        static __zero_table_end: ZeroTable;
        static __copy_table_start: CopyTable;
        static __copy_table_end: CopyTable;
    }

    let mut p_table = &__copy_table_start as *const CopyTable;
    while p_table < &__copy_table_end as *const CopyTable {
        let table = &(*p_table);
        for i in 0..table.size {
            core::ptr::write(
                table.dst.add(i as usize),
                core::ptr::read(table.src.add(i as usize)),
            );
        }
        p_table = p_table.add(1);
    }

    let mut p_table = &__zero_table_start as *const ZeroTable;
    while p_table < &__zero_table_end as *const ZeroTable {
        let table = &*p_table;
        for i in 0..table.size {
            core::ptr::write(table.dst.add(i as usize), 0);
        }
        p_table = p_table.add(1);
    }
    INIT_BSS_DONE = true;
}

const TICKS_PS: usize = blueos_kconfig::CONFIG_TICKS_PER_SECOND as usize;
const HZ: usize = SYSTEM_CORE_CLOCK as usize;
pub type ClockImpl = systick::SysTickClock<TICKS_PS, HZ>;

pub(crate) fn init() {
    unsafe {
        copy_data();
        arch::irq::init_interrupt_registry();
    }
    boot::init_runtime();
    unsafe { boot::init_heap() };
    arch::irq::init();
    ClockImpl::init();

    arch::irq::enable_irq_with_priority(UART0RX_IRQn, arch::irq::Priority::Normal);
    arch::irq::enable_irq_with_priority(UART0TX_IRQn, arch::irq::Priority::Normal);
}

crate::define_pin_states!(None);

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::cmsdk::Cmsdk,
     unsafe {blueos_driver::uart::cmsdk::Cmsdk::new(
         memory_map::UART0_BASE as _,
         SYSTEM_CORE_CLOCK,
            UART0TX_IRQ_N,
            UART0RX_IRQ_N
     )}),
}

#[blueos_macro::interrupt(no = 0)]
static CMSDK_RX_ISR: CmsdkRxIsr<
    { memory_map::UART0_BASE as usize },
    crate::drivers::serial::Serial,
> = CmsdkRxIsr::<{ memory_map::UART0_BASE as usize }, _> {
    data: &crate::drivers::serial::TTY_SERIAL,
    handler: Some(crate::drivers::serial::Serial::recvchars),
};

#[blueos_macro::interrupt(no = 1)]
pub static CMSDK_TX_ISR: CmsdkTxIsr<
    { memory_map::UART0_BASE as usize },
    crate::drivers::serial::Serial,
> = CmsdkTxIsr::<{ memory_map::UART0_BASE as usize }, _> {
    data: &crate::drivers::serial::TTY_SERIAL,
    handler: Some(crate::drivers::serial::Serial::xmitchars),
};
