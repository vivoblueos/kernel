#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::entry;

#[entry(foo)] //~ ERROR This attribute accepts no arguments
fn foo() -> ! {
    loop {}
}
