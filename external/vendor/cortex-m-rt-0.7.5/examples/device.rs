//! Manually create the interrupts portion of the vector table

#![deny(unsafe_code)]
#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m_rt as rt;
extern crate panic_halt;

use rt::entry;

#[entry]
fn main() -> ! {
    loop {}
}

// interrupts portion of the vector table
#[repr(C)]
pub union Vector {
    handler: unsafe extern "C" fn(),
    reserved: usize,
}

extern "C" {
    fn WWDG();
    fn PVD();
}

#[allow(unsafe_code)]
#[link_section = ".vector_table.interrupts"]
#[no_mangle]
pub static __INTERRUPTS: [Vector; 3] = [
    Vector { handler: WWDG },
    Vector { reserved: 0 },
    Vector { handler: PVD },
];
