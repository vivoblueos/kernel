//! A test harness for embedded devices.
//!
//! This crate has a single API: the `#[tests]` macro. This macro is documented in the project
//! README which can be found at:
//!
//! - <https://crates.io/crates/defmt-test> (crates.io version)
//! - <https://github.com/knurling-rs/defmt/tree/main/firmware/defmt-test> (git version)

#![doc(html_logo_url = "https://knurling.ferrous-systems.com/knurling_logo_light_text.svg")]
#![no_std]

use defmt::Format;
pub use defmt_test_macros::tests;

/// Private implementation details used by the proc macro.
#[doc(hidden)]
pub mod export;

mod sealed {
    pub trait Sealed {}
    impl Sealed for () {}
    impl<T, E> Sealed for Result<T, E> {}
}

/// Indicates whether a test succeeded or failed.
///
/// This is comparable to the `Termination` trait in libstd, except stable and tailored towards the
/// needs of defmt-test. It is implemented for `()`, which always indicates success, and `Result`,
/// where `Ok` indicates success.
pub trait TestOutcome: Format + sealed::Sealed {
    fn is_success(&self) -> bool;
}

impl TestOutcome for () {
    fn is_success(&self) -> bool {
        true
    }
}

impl<T: Format, E: Format> TestOutcome for Result<T, E> {
    fn is_success(&self) -> bool {
        self.is_ok()
    }
}
