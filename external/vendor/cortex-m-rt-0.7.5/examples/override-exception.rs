//! How to override the hard fault exception handler and the default exception handler

#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m;
extern crate cortex_m_rt as rt;
extern crate panic_halt;

use cortex_m::asm;
use rt::{entry, exception, ExceptionFrame};

#[entry]
fn main() -> ! {
    loop {}
}

#[exception]
unsafe fn DefaultHandler(_irqn: i16) {
    asm::bkpt();
}

#[exception]
unsafe fn HardFault(_ef: &ExceptionFrame) -> ! {
    asm::bkpt();

    loop {}
}
