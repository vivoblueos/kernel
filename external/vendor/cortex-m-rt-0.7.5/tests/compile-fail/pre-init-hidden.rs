// ignore-test :sadface: it's not possible to prevent this user error at compile time
// see rust-lang/rust#53975 for details

#![no_main]
#![no_std]

extern crate cortex_m_rt;
extern crate panic_halt;

mod hidden {
    use cortex_m_rt::pre_init;

    // this function needs to be "reachable" (all modules between it and the crate root must be
    // `pub`) or the function will be ignored
    #[entry]
    unsafe fn pre_init() {} //~ ERROR function is never used
}

#[entry]
fn foo() -> ! {
    //~ ERROR function is never used
    loop {}
}
