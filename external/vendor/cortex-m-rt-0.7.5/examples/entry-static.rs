//! `static mut` variables local to the entry point are safe to use

#![deny(unsafe_code)]
#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m_rt as rt;
extern crate panic_halt;

use rt::entry;

#[entry]
fn main() -> ! {
    static mut COUNT: u32 = 0;

    loop {
        *COUNT += 1;
    }
}
