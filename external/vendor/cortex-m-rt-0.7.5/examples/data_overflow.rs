//! This is not an example; this is a linker overflow detection test
//! which should fail to link due to .data overflowing FLASH.

#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m_rt as rt;
extern crate panic_halt;

use core::ptr;
use rt::entry;

// This large static array uses most of .rodata
const RODATA_SIZE: usize = 250 * 1024;
static RODATA: [u8; RODATA_SIZE] = [1u8; RODATA_SIZE];

// This large mutable array causes .data to use the rest of FLASH
// without also overflowing RAM.
const DATA_SIZE: usize = 8 * 1024;
static mut DATA: [u8; DATA_SIZE] = [1u8; DATA_SIZE];

#[entry]
fn main() -> ! {
    unsafe {
        let _bigdata: u8 = ptr::read_volatile(ptr::addr_of!(RODATA) as *const u8);
        let _bigdata: u8 = ptr::read_volatile(ptr::addr_of!(DATA) as *const u8);
    }

    loop {}
}
