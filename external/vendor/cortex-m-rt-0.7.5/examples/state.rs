//! Preserving state across executions of an exception handler

#![deny(unsafe_code)]
#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m_rt as rt;
extern crate panic_halt;

use rt::{entry, exception};

#[entry]
fn main() -> ! {
    loop {}
}

// exception handler with state
#[exception]
fn SysTick() {
    static mut STATE: u32 = 0;

    *STATE += 1;
}
