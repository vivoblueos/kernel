#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, exception};

#[entry]
fn foo() -> ! {
    static mut COUNT: u64 = 0;

    loop {
        if *COUNT % 2 == 0 {
            *COUNT += 1;
        } else {
            *COUNT *= 2;
        }
    }
}

#[exception]
fn SysTick() {
    // If this was allowed it would lead to a data race as `SysTick` can preempt `foo`
    foo(); //~ ERROR cannot find function `foo` in this scope
}
