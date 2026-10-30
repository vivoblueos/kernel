//! `cortex-m-rt` based program with a function run before RAM is initialized.

#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m_rt as rt;
extern crate panic_halt;

use rt::{entry, pre_init};

#[pre_init]
unsafe fn disable_watchdog() {
    // Do what you need to disable the watchdog.
}

#[entry]
fn main() -> ! {
    loop {}
}
