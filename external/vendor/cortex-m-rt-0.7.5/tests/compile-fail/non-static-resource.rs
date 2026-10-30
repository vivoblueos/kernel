//! Tests that no `&'static mut` to static mutable resources can be obtained, which would be
//! unsound.
//!
//! Regression test for https://github.com/rust-embedded/cortex-m-rt/issues/212

#![no_std]
#![no_main]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, exception, interrupt, ExceptionFrame};

#[allow(non_camel_case_types)]
enum interrupt {
    UART0,
}

#[exception]
fn SVCall() {
    static mut STAT: u8 = 0;

    let _stat: &'static mut u8 = STAT;
    //~^ ERROR lifetime may not live long enough
}

#[interrupt]
fn UART0() {
    static mut STAT: u8 = 0;

    let _stat: &'static mut u8 = STAT;
    //~^ ERROR lifetime may not live long enough
}

#[entry]
fn you_died_of_dis_entry() -> ! {
    static mut STAT: u8 = 0;

    // Allowed. This is sound for the entry point since it is only ever called once, and it makes
    // resources far more useful.
    let _stat: &'static mut u8 = STAT;

    loop {}
}
