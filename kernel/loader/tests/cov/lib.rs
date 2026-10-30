// NEWLINE-TIMEOUT: 15
// ASSERT-SUCC: coverage test end.
// ASSERT-FAIL: Backtrace in Panic.*

#![no_std]
extern crate alloc;
use minicov::capture_coverage;
use semihosting::{c, fs, println};

pub fn write_coverage_data() {
    let mut cov_data = alloc::vec![];
    unsafe {
        // Note that this function is not thread-safe! Use a lock if needed.
        capture_coverage(&mut cov_data).unwrap();
    }
    fs::write(c!("output.profraw"), cov_data).unwrap();
    println!("coverage test end.");
}
