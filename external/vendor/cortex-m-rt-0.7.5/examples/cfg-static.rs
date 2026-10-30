//! using `#[cfg]` on `static` shouldn't cause compile errors

#![deny(unsafe_code)]
#![deny(warnings)]
#![no_main]
#![no_std]
// This example uses an undefined cfg, `cfg(never)`
#![allow(unexpected_cfgs)]

extern crate cortex_m_rt as rt;
extern crate panic_halt;

use rt::{entry, exception};

#[entry]
fn main() -> ! {
    #[cfg(never)]
    static mut COUNT: u32 = 0;

    loop {}
}

#[exception]
fn SysTick() {
    #[cfg(never)]
    static mut FOO: u32 = 0;
}
