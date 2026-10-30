//! This crate provides code coverage and profile-guided optimization (PGO) support
//! for `no_std` and embedded programs.
//!
//! This is done through a modified version of the LLVM profiling runtime (normally
//! part of compiler-rt) from which all dependencies on libc have been removed.
//!
//! All types of instrumentation using the LLVM profiling runtime are supported:
//! - Rust code coverage with `-Cinstrument-coverage`.
//! - Rust profile-guided optimization with `-Cprofile-generate`.
//! - Clang code coverage with `-fprofile-instr-generate -fcoverage-mapping`.
//! - Clang profile-guided optimization with `-fprofile-instr-generate`.
//! - Clang LLVM IR profile-guided optimization with `-fprofile-generate`.
//!
//! Note that to profile both C and Rust code at the same time you must use Clang
//! with the same LLVM version as the LLVM used by rustc. You can pass these flags
//! to C code compiled with the `cc` crates using [environment variables].
//!
//! [environment variables]: https://github.com/rust-lang/cc-rs#external-configuration-via-environment-variables
//!
//! ## Usage
//!
//! Note: This crate requires a recent nightly compiler.
//!
//! 1. Ensure that the following environment variables are set up:
//!
//! ```sh
//! export RUSTFLAGS="-Cinstrument-coverage -Zno-profiler-runtime"
//! ```
//!
//! Note that these flags also apply to build-dependencies and proc
//! macros by default. This can be worked around by explicitly
//! specifying a target when invoking cargo:
//!
//! ```sh
//! # Applies RUSTFLAGS to everything
//! cargo build
//!
//! # Doesn't apply RUSTFLAGS to build dependencies and proc macros
//! cargo build --target x86_64-unknown-linux-gnu
//! ```
//!
//! 2. Add the `minicov` crate as a dependency to your program:
//!
//! ```toml
//! [dependencies]
//! minicov = "0.3"
//! ```
//!
//! 3. Before your program exits, call `minicov::capture_coverage` with a sink (such
//!    as `Vec<u8>`) and then dump its contents to a file with the `.profraw` extension:
//!
//! ```ignore
//! fn main() {
//!     // ...
//!
//!     let mut coverage = vec![];
//!     unsafe {
//!         // Note that this function is not thread-safe! Use a lock if needed.
//!         minicov::capture_coverage(&mut coverage).unwrap();
//!     }
//!     std::fs::write("output.profraw", coverage).unwrap();
//! }
//! ```
//!
//! If your program is running on a different system than your build system then
//! you will need to transfer this file back to your build system.
//!
//! Sinks must implement the `CoverageWriter` trait. If the default `alloc` feature
//! is enabled then an implementation is provided for `Vec<u8>`.
//!
//! 4. Use a tool such as [grcov] or llvm-cov to generate a human-readable coverage
//!    report:
//!
//! ```sh
//! grcov output.profraw -b ./target/debug/my_program -s . -t html -o cov_report
//! ```
//!
//! [grcov]: https://github.com/mozilla/grcov
//!
//! ## Profile-guided optimization
//!
//! The steps for profile-guided optimzation are similar. The only difference is the
//! flags passed in `RUSTFLAGS`:
//!
//! ```sh
//! # First run to generate profiling information.
//! export RUSTFLAGS="-Cprofile-generate -Zno-profiler-runtime"
//! cargo run --target x86_64-unknown-linux-gnu --release
//!
//! # Post-process the profiling information.
//! # The rust-profdata tool comes from cargo-binutils.
//! rust-profdata merge -o output.profdata output.profraw
//!
//! # Optimized build using PGO. minicov is not needed in this step.
//! export RUSTFLAGS="-Cprofile-use=output.profdata"
//! cargo build --target x86_64-unknown-linux-gnu --release
//! ```

#![no_std]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;
#[cfg(feature = "alloc")]
use core::alloc::Layout;
use core::{fmt, slice};

#[allow(non_snake_case)]
#[repr(C)]
struct ProfDataIOVec {
    Data: *mut u8,
    ElmSize: usize,
    NumElm: usize,
    UseZeroPadding: i32,
}

#[allow(non_snake_case)]
#[repr(C)]
struct ProfDataWriter {
    Write:
        unsafe extern "C" fn(This: *mut ProfDataWriter, *mut ProfDataIOVec, NumIOVecs: u32) -> u32,
    WriterCtx: *mut u8,
}

// Opaque type for our purposes.
enum VPDataReaderType {}

extern "C" {
    fn __llvm_profile_reset_counters();
    fn __llvm_profile_merge_from_buffer(profile: *const u8, size: u64) -> i32;
    fn __llvm_profile_check_compatibility(profile: *const u8, size: u64) -> i32;
    fn __llvm_profile_get_version() -> u64;
    fn lprofWriteData(
        Writer: *mut ProfDataWriter,
        VPDataReader: *mut VPDataReaderType,
        SkipNameDataWrite: i32,
    ) -> i32;
    fn lprofGetVPDataReader() -> *mut VPDataReaderType;
}

const INSTR_PROF_RAW_VERSION: u64 = 10;
const VARIANT_MASKS_ALL: u64 = 0xffffffff00000000;

// On some target rustc will insert an artificial dependency on the
// __llvm_profile_runtime symbol to ensure the static initializer from LLVM's
// profiling runtime is pulled in by the linker. We don't need any runtime
// initialization so we just provide the symbol here.
#[no_mangle]
static __llvm_profile_runtime: u8 = 0;

// Memory allocation functions used by value profiling. If the "alloc" feature
// is disabled then value profiling will also be disabled.
#[cfg(feature = "alloc")]
#[no_mangle]
unsafe fn minicov_alloc_zeroed(size: usize, align: usize) -> *mut u8 {
    alloc::alloc::alloc_zeroed(Layout::from_size_align(size, align).unwrap())
}
#[cfg(feature = "alloc")]
#[no_mangle]
unsafe extern "C" fn minicov_dealloc(ptr: *mut u8, size: usize, align: usize) {
    alloc::alloc::dealloc(ptr, Layout::from_size_align(size, align).unwrap())
}
#[cfg(not(feature = "alloc"))]
#[no_mangle]
unsafe fn minicov_alloc_zeroed(_size: usize, _align: usize) -> *mut u8 {
    core::ptr::null_mut()
}
#[cfg(not(feature = "alloc"))]
#[no_mangle]
unsafe extern "C" fn minicov_dealloc(_ptr: *mut u8, _size: usize, _align: usize) {}

/// Sink into which coverage data can be written.
///
/// A default implementation for `Vec<u8>` is provided,
pub trait CoverageWriter {
    /// Writes the given bytes to the sink.
    ///
    /// This method should return an error if all bytes could not be written to
    /// the sink.
    fn write(&mut self, data: &[u8]) -> Result<(), CoverageWriteError>;
}

#[cfg(feature = "alloc")]
impl CoverageWriter for Vec<u8> {
    fn write(&mut self, data: &[u8]) -> Result<(), CoverageWriteError> {
        self.extend_from_slice(data);
        Ok(())
    }
}

/// Callback function passed to `lprofWriteData`.
unsafe extern "C" fn write_callback<Writer: CoverageWriter>(
    this: *mut ProfDataWriter,
    iovecs: *mut ProfDataIOVec,
    num_iovecs: u32,
) -> u32 {
    let writer = &mut *((*this).WriterCtx as *mut Writer);
    for iov in slice::from_raw_parts(iovecs, num_iovecs as usize) {
        let len = iov.ElmSize * iov.NumElm;
        if iov.Data.is_null() {
            // Pad with zero bytes.
            let zero = [0; 16];
            let mut remaining = len;
            while remaining != 0 {
                let data = &zero[..usize::min(zero.len(), remaining)];
                if writer.write(data).is_err() {
                    return 1;
                }
                remaining -= data.len();
            }
        } else {
            let data = slice::from_raw_parts(iov.Data, len);
            if writer.write(data).is_err() {
                return 1;
            }
        }
    }
    0
}

/// Checks that the instrumented binary uses the same profiling data format as
/// the LLVM profiling runtime.
fn check_version() {
    let version = unsafe { __llvm_profile_get_version() & !VARIANT_MASKS_ALL };
    assert_eq!(
        version, INSTR_PROF_RAW_VERSION,
        "Runtime and instrumentation version mismatch"
    );
}

/// Captures the coverage data for the current program and writes it into the
/// given sink.
///
/// The data should be saved to a file with the `.profraw` extension, which can
/// then be processed using the `llvm-profdata` and `llvm-cov` tools.
///
/// You should call `reset_coverage` afterwards if you intend to continue
/// running the program so that future coverage can be merged with the returned
/// captured coverage.
///
/// # Safety
///
/// This function is not thread-safe and should not be concurrently called from
/// multiple threads.
pub unsafe fn capture_coverage<Writer: CoverageWriter>(
    writer: &mut Writer,
) -> Result<(), CoverageWriteError> {
    check_version();

    let mut prof_writer = ProfDataWriter {
        Write: write_callback::<Writer>,
        WriterCtx: writer as *mut Writer as *mut u8,
    };
    let res = lprofWriteData(&mut prof_writer, lprofGetVPDataReader(), 0);
    if res == 0 {
        Ok(())
    } else {
        Err(CoverageWriteError)
    }
}

/// Error type returned when trying to merge incompatible coverage data.
///
/// This typically happens if the coverage data comes from a different binary.
#[derive(Copy, Clone, Debug)]
pub struct IncompatibleCoverageData;
impl fmt::Display for IncompatibleCoverageData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("incompatible coverage data")
    }
}

/// Error while trying to write coverage data.
///
/// This only happens if the `CoverageWriter` implementation returns an error.
#[derive(Copy, Clone, Debug)]
pub struct CoverageWriteError;
impl fmt::Display for CoverageWriteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("error while writing coverage data")
    }
}

/// Merges previously dumped coverage data into the coverage counters.
///
/// This should be called prior to dumping if coverage data from a previous run
/// already exists and should be merged with instead of overwritten.
///
/// # Safety
///
/// This function is not thread-safe and should not be concurrently called from
/// multiple threads.
pub unsafe fn merge_coverage(data: &[u8]) -> Result<(), IncompatibleCoverageData> {
    check_version();

    if __llvm_profile_check_compatibility(data.as_ptr(), data.len() as u64) == 0
        && __llvm_profile_merge_from_buffer(data.as_ptr(), data.len() as u64) == 0
    {
        Ok(())
    } else {
        Err(IncompatibleCoverageData)
    }
}

/// Resets all coverage counters in the program to zero.
///
/// This function should be called after a process forks to avoid recording
/// coverage data for the parent process twice.
///
/// You should also call this after calling `capture_coverage` if you intend to
/// continue running with the intention of merging with the captured coverage
/// later.
pub fn reset_coverage() {
    check_version();

    unsafe {
        __llvm_profile_reset_counters();
    }
}
