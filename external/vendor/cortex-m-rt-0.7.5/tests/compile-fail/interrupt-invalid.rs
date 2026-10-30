#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, interrupt};

#[entry]
fn entry() -> ! {
    loop {}
}

#[allow(non_camel_case_types)]
enum interrupt {
    USART1,
}

// NOTE this looks a bit better when using a device crate:
// "no variant named `foo` found for type `stm32f30x::Interrupt` in the current scope"
#[interrupt]
fn foo() {} //~ ERROR no variant or associated item named `foo` found for enum `interrupt` in the current scope [E0599]
