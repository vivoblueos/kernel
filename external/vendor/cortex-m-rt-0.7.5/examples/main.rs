//! Directly plug a `main` symbol instead of using `#[entry]`

#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m_rt as rt;
extern crate panic_halt;

#[no_mangle]
pub unsafe extern "C" fn main() -> ! {
    loop {}
}
