//! This is not an example; this is a linker test that ensures
//! that the jump from HardFault to _HardFault doesn't exceed
//! the 2kB limit of the branch instruction.

#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

use core::arch::asm;
use cortex_m_rt::{entry, exception, ExceptionFrame};

// This defines both `HardFault` and `_HardFault`. Both should have
// link_section attributes placing them at the end of the .text section,
// close to each other. If one of them is missing that attribute, they
// will end up separated by `foo`, which will make the linker fail.
#[exception(trampoline = true)]
unsafe fn HardFault(_ef: &ExceptionFrame) -> ! {
    loop {}
}

#[entry]
fn foo() -> ! {
    unsafe {
        // 2kB of NOP instructions to make the function artificially larger
        asm!(".fill 1024,2,0xbf00",);
    }
    loop {}
}
