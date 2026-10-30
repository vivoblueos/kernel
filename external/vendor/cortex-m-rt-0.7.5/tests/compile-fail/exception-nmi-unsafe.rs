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
fn DefaultHandler(_irq: i16) {}
//~^ ERROR defining a `DefaultHandler` is unsafe and requires an `unsafe fn`

#[exception]
fn HardFault() {}
//~^ ERROR defining a `HardFault` handler is unsafe and requires an `unsafe fn`

#[exception]
fn NonMaskableInt() {}
//~^ ERROR defining a `NonMaskableInt` handler is unsafe and requires an `unsafe fn`
