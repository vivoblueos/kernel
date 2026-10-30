#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, interrupt};

#[entry]
fn foo() -> ! {
    loop {}
}

#[allow(non_camel_case_types)]
enum interrupt {
    USART1,
}

#[interrupt]
fn USART1(undef: i32) {}
//~^ ERROR `#[interrupt]` handlers must have signature `[unsafe] fn() [-> !]`
