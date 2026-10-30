#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, exception, ExceptionFrame};

#[entry]
fn foo() -> ! {
    loop {}
}

#[exception(trampoline = true)]
unsafe fn HardFault() -> ! {
    //~^ ERROR `HardFault` handler must have signature `unsafe fn(&ExceptionFrame) -> !`
    loop {}
}
