#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::entry;

#[entry]
unsafe fn foo() -> ! {
    loop {}
}
