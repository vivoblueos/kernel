//! Makes sure that the expansion of the attributes doesn't put the resource initializer in an
//! implicit `unsafe` block.

#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, exception, interrupt};

#[allow(non_camel_case_types)]
enum interrupt {
    UART0,
}

const unsafe fn init() -> u32 { 0 }

#[entry]
fn foo() -> ! {
    static mut X: u32 = init();  //~ ERROR requires unsafe

    loop {}
}

#[exception]
fn SVCall() {
    static mut X: u32 = init();  //~ ERROR requires unsafe
}

#[exception]
unsafe fn DefaultHandler(_irq: i16) {
    static mut X: u32 = init();  //~ ERROR requires unsafe
}

#[exception]
unsafe fn HardFault(_frame: &cortex_m_rt::ExceptionFrame) -> ! {
    static mut X: u32 = init();  //~ ERROR requires unsafe
    loop {}
}

#[interrupt]
fn UART0() {
    static mut X: u32 = init();  //~ ERROR requires unsafe
}
