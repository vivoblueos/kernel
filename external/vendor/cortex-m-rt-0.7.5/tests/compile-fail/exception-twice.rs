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
fn SysTick() {}

pub mod reachable {
    use cortex_m_rt::exception;

    #[exception] //~ ERROR symbol `SysTick` is already defined
    fn SysTick() {}
}
