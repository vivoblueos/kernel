#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use cortex_m_rt::{entry, interrupt};

#[entry]
fn foo() -> ! {
    loop {}
}

#[allow(non_camel_case_types)]
enum interrupt {
    USART1,
    USART2,
}

#[interrupt]
fn USART1() {
    static mut COUNT: u64 = 0;

    if *COUNT % 2 == 0 {
        *COUNT += 1;
    } else {
        *COUNT *= 2;
    }
}

#[interrupt]
fn USART2() {
    USART1(); //~ ERROR cannot find function, tuple struct or tuple variant `USART1` in this scope [E0425]
}
