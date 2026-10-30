#![allow(non_camel_case_types)]
#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, interrupt};

#[entry]
fn foo() -> ! {
    loop {}
}

enum interrupt {
    USART1,
}

#[interrupt]
fn USART1() {}

pub mod reachable {
    use cortex_m_rt::interrupt;

    enum interrupt {
        USART1,
    }

    #[interrupt] //~ ERROR symbol `USART1` is already defined
    fn USART1() {}
}
