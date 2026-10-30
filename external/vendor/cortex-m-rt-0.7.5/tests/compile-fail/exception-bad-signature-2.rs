#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, exception};

#[entry]
fn foo() -> ! {
    loop {}
}

#[exception]
fn SysTick() -> u32 {
    //~^ ERROR `#[exception]` handlers other than `DefaultHandler` and `HardFault` must have signature `[unsafe] fn() [-> !]`
    0
}
