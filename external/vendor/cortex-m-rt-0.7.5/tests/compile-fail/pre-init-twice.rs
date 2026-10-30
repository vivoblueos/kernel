#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, pre_init};

#[pre_init]
unsafe fn foo() {}

#[pre_init] //~ ERROR symbol `__pre_init` is already defined
unsafe fn bar() {}

#[entry]
fn baz() -> ! {
    loop {}
}
