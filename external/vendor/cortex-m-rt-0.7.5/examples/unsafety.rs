//! Checks that the declared unsafety is respected by the attributes

#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, exception, ExceptionFrame};

#[entry]
unsafe fn main() -> ! {
    foo();

    loop {}
}

#[exception]
unsafe fn DefaultHandler(_irqn: i16) {
    foo();
}

#[exception]
unsafe fn HardFault(_ef: &ExceptionFrame) -> ! {
    foo();

    loop {}
}

#[exception]
unsafe fn SysTick() {
    foo();
}

unsafe fn foo() {}
