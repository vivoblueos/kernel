//! This is not an example; this is a link-pass test

#![deny(warnings)]
#![no_main]
#![no_std]

extern crate cortex_m_rt as rt;
extern crate panic_halt;

use core::ptr;

use rt::entry;

static mut BSS1: u16 = 0;
static mut BSS2: u8 = 0;
static mut DATA1: u8 = 1;
static mut DATA2: u16 = 1;
static RODATA1: &[u8; 3] = b"012";
static RODATA2: &[u8; 2] = b"34";

#[entry]
fn main() -> ! {
    unsafe {
        let _bss1 = ptr::read_volatile(ptr::addr_of!(BSS1));
        let _bss2 = ptr::read_volatile(ptr::addr_of!(BSS2));
        let _data1 = ptr::read_volatile(ptr::addr_of!(DATA1));
        let _data2 = ptr::read_volatile(ptr::addr_of!(DATA2));
        let _rodata1 = ptr::read_volatile(ptr::addr_of!(RODATA1));
        let _rodata2 = ptr::read_volatile(ptr::addr_of!(RODATA2));
    }

    loop {}
}
