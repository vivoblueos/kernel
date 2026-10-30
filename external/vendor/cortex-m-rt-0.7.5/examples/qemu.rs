#![no_main]
#![no_std]

use core::{
    fmt::Write,
    sync::atomic::{AtomicU32, Ordering},
};

static DATA_VAL: AtomicU32 = AtomicU32::new(1234);

static BSS_VAL: AtomicU32 = AtomicU32::new(0);

#[cortex_m_rt::entry]
fn main() -> ! {
    let x = 42;

    loop {
        let mut hstdout = cortex_m_semihosting::hio::hstdout().unwrap();
        // check that .data and .bss were initialised OK
        if DATA_VAL.load(Ordering::Relaxed) == 1234 && BSS_VAL.load(Ordering::Relaxed) == 0 {
            _ = writeln!(hstdout, "x = {}", x);
        }
        cortex_m_semihosting::debug::exit(cortex_m_semihosting::debug::EXIT_SUCCESS);
    }
}

// Define a panic handler that uses semihosting to exit immediately,
// so that any panics cause qemu to quit instead of hang.
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {
        cortex_m_semihosting::debug::exit(cortex_m_semihosting::debug::EXIT_FAILURE);
    }
}
