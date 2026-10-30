#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, exception, ExceptionFrame};

#[entry]
fn foo() -> ! {
    loop {}
}

#[exception(trampoline = false)]
unsafe fn HardFault() -> ! {
    loop {}
}

pub mod reachable {
    use cortex_m_rt::{exception, ExceptionFrame};

    #[exception] //~ ERROR symbol `_HardFault` is already defined
    unsafe fn HardFault(_ef: &ExceptionFrame) -> ! {
        loop {}
    }
}
