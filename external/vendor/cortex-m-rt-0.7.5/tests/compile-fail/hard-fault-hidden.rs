// ignore-test :sadface: it's not possible to prevent this user error at compile time
// see rust-lang/rust#53975 for details

#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, exception, ExceptionFrame};

#[entry]
fn foo() -> ! {
    loop {}
}

mod hidden {
    use cortex_m_rt::{exception, ExceptionFrame};

    #[exception]
    fn HardFault(_ef: &ExceptionFrame) -> ! {
        loop {}
    }
}
