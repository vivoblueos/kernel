#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, exception, interrupt};

#[allow(non_camel_case_types)]
enum interrupt {
    UART0,
}

#[entry]
fn foo() -> ! {
    static mut X: u32 = 0;
    static mut X: i32 = 0; //~ ERROR the name `X` is defined multiple times

    loop {}
}

#[exception]
fn SVCall() {
    static mut X: u32 = 0;
    static mut X: i32 = 0; //~ ERROR the name `X` is defined multiple times
}

#[interrupt]
fn UART0() {
    static mut X: u32 = 0;
    static mut X: i32 = 0; //~ ERROR the name `X` is defined multiple times
}
