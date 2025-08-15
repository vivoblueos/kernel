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
mod led;
mod rp235x;

use crate::{
    arch::{self, irq::IrqNumber},
    boards::raspberry_pico2_cortexm::{
        config::{PLL_SYS_150MHZ, PLL_USB_48MHZ},
        led::Led,
        rp235x::{
            block,
            clocks::{
                PeripheralAuxiliaryClockSource, ReferenceAuxiliaryClockSource,
                ReferenceClockSource, SystemAuxiliaryClockSource, SystemClockSource,
            },
            gpio::{GpioFunction, GpioPin},
            pll,
            reset::{Peripheral, Resets},
            uart::Uart,
            xosc,
        },
    },
    boot,
    boot::INIT_BSS_DONE,
    devices::{
        console,
        tty::{
            n_tty::Tty,
            serial::{Serial, UartOps},
            termios::Termios,
        },
    },
    kprintln,
    sync::SpinLock,
    time,
};
use alloc::sync::Arc;
use core::ptr::addr_of;
use spin::Once;

#[link_section = ".start_block"]
#[used]
pub static IMAGE_DEF: rp235x::block::ImageDef = rp235x::block::ImageDef::secure_exe();

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

    let _ = rp235x::xosc::start_xosc(config::XOSC_FREQ);

    rp235x::clocks::disable_clk_sys_resus();
    rp235x::clocks::disable_sys_aux();
    rp235x::clocks::disable_ref_aux();

    let reset = Resets::new();

    reset.reset_all_except(&[
        Peripheral::IOQSpi,
        Peripheral::PadsBank0,
        Peripheral::PllUsb,
        Peripheral::PllUsb,
    ]);

    reset.unreset_all_except(
        &[
            Peripheral::Adc,
            Peripheral::Sha256,
            Peripheral::HSTX,
            Peripheral::Spi0,
            Peripheral::Spi1,
            Peripheral::Uart0,
            Peripheral::Uart1,
            Peripheral::UsbCtrl,
        ],
        true,
    );

    reset.reset(&[Peripheral::PllSys, Peripheral::PllUsb]);
    reset.unreset(&[Peripheral::PllSys, Peripheral::PllUsb], true);

    let pll_sys_freq = rp235x::pll::configure_pll(
        rp235x::pll::PLL::Sys,
        config::XOSC_FREQ as u32,
        &PLL_SYS_150MHZ,
    );
    let pll_usb_freq = rp235x::pll::configure_pll(
        rp235x::pll::PLL::Usb,
        config::XOSC_FREQ as u32,
        &PLL_USB_48MHZ,
    );

    rp235x::clocks::configure_reference_clock(
        ReferenceClockSource::Xosc,
        ReferenceAuxiliaryClockSource::PllUsb,
        1,
    );

    rp235x::clocks::configure_system_clock(
        SystemClockSource::Auxiliary,
        SystemAuxiliaryClockSource::PllSys,
        1,
        0,
    );

    rp235x::clocks::configure_peripheral_clock(PeripheralAuxiliaryClockSource::PllSys);

    time::systick_init(pll_sys_freq);

    let pin25 = GpioPin::<25>::new();
    pin25.set_function(GpioFunction::SIO);
    pin25.activate_pads();

    rp235x::sio::set_sio_oe_set(25);
    rp235x::sio::enable_sio_gpio_out(25);

    let pin2 = GpioPin::<2>::new();
    pin2.set_function(GpioFunction::UART0_TX);
    let pin3 = GpioPin::<3>::new();
    pin3.set_function(GpioFunction::UART0_RX);

    reset.reset(&[Peripheral::Uart0]);
    reset.unreset(&[Peripheral::Uart0], true);

    let mut u = Uart::new();
    u.enable(115200);

    match console::init_console(Tty::init(get_serial0(u).clone()).clone()) {
        Ok(_) => (),
        Err(e) => panic!("Failed to init console"),
    }

    let led0 = Led::new(0, pin25);
    let led0 = Arc::new(led0);
    match led::led_init(led0) {
        Ok(_) => kprintln!("LED initialized successfully"),
        Err(e) => panic!("Failed to initialize LED: {:?}", e),
    }
}

// FIXME: support float
pub(crate) fn get_cycles_to_duration(cycles: u64) -> core::time::Duration {
    return core::time::Duration::from_nanos(
        (cycles as u128 * 1_000_000_000 as u128 / config::PLL_SYS_FREQ as u128) as u64,
    );
}

pub(crate) fn get_cycles_to_ms(cycles: u64) -> u64 {
    return (cycles as u128 * 1_000 as u128 / config::PLL_SYS_FREQ as u128) as u64;
}

pub fn get_early_uart() -> &'static SpinLock<dyn UartOps> {
    todo!()
}

pub(crate) static SERIAL0: Once<Arc<Serial>> = Once::new();
pub fn get_serial0(u: Uart) -> &'static Arc<Serial> {
    SERIAL0.call_once(|| {
        Arc::new(Serial::new(
            0,
            Termios::default(),
            Arc::new(SpinLock::new(u)),
        ))
    })
}
