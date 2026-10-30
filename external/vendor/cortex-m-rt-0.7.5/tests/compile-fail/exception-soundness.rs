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
fn SysTick() {
    static mut COUNT: u64 = 0;

    if *COUNT % 2 == 0 {
        *COUNT += 1;
    } else {
        *COUNT *= 2;
    }
}

#[exception]
fn SVCall() {
    // If this was allowed it would lead to a data race as `SVCall` could preempt `SysTick`
    SysTick(); //~ ERROR cannot find function, tuple struct or tuple variant `SysTick` in this scope [E0425]
}
