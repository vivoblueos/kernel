// SPDX-License-Identifier: Apache-2.0 OR MIT

// Provide safe abstraction (c! macro) for creating static C strings without runtime checks.
// (c"..." requires Rust 1.77)

/// [`CStr`] literal macro.
///
/// **Note:** Since Rust 1.77, this macro is soft-deprecated in favor of C string literals (`c"..."`).
///
/// [`Path`] is not available in `core`, so this crate uses [`CStr`] instead in the API where
/// `std` uses [`Path`]. This macro makes it safe and zero-cost to create a [`CStr`] from a literal.
///
/// ```no_run
/// use semihosting::{c, fs};
///
/// fs::write(c!("a.txt"), "abc")?;
/// // concat! in c! is also supported
/// fs::write(c!(concat!("b", ".txt")), "def")?;
/// # Ok::<(), semihosting::io::Error>(())
/// ```
///
/// This macro guarantees the correctness of the input by compile-time validation.
/// Incorrect input will cause compile-time errors.
///
/// ```compile_fail,E0080
/// use semihosting::c;
///
/// let s = c!("ab\0c"); // CStr must not contain any interior nul bytes.
/// ```
///
/// ```text
/// error[E0080]: evaluation of constant value failed
///   --> semihosting/src/c_str.rs:48:9
///    |
/// 48 |         assert!(byte != 0, "input contained interior nul");
///    |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ the evaluated program panicked at 'input contained interior nul', semihosting/src/c_str.rs:48:9
///    |
/// note: inside `const_c_str_check`
///   --> semihosting/src/c_str.rs:48:9
///    |
/// 48 |         assert!(byte != 0, "input contained interior nul");
///    |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
/// note: inside `_`
///   --> src/c_str.rs:18:9
///    |
/// 5  | let s = c!("ab\0c"); // CStr must not contain any interior nul bytes.
///    |         ^^^^^^^^^^^
/// ```
///
/// [`CStr`]: core::ffi::CStr
/// [`Path`]: https://doc.rust-lang.org/std/path/struct.Path.html
#[macro_export]
macro_rules! c {
    ($s:expr) => {{
        const BYTES: &[u8] = concat!($s, "\0").as_bytes();
        const _: () = $crate::__private::const_c_str_check(BYTES);
        #[allow(unused_unsafe)]
        // SAFETY: we've checked `BYTES` is a valid C string
        unsafe {
            $crate::__private::CStr::from_bytes_with_nul_unchecked(BYTES)
        }
    }};
}

// Based on https://github.com/rust-lang/rust/blob/1.84.0/library/core/src/ffi/c_str.rs#L417
// - bytes must be nul-terminated.
// - bytes must not contain any interior nul bytes.
#[doc(hidden)]
pub const fn const_c_str_check(bytes: &[u8]) {
    // Saturating so that an empty slice panics in the assert with a good
    // message, not here due to underflow.
    let mut i = bytes.len().saturating_sub(1);
    assert!(!bytes.is_empty() && bytes[i] == 0, "input was not nul-terminated");

    // Ending null byte exists, skip to the rest.
    while i != 0 {
        i -= 1;
        let byte = bytes[i];
        assert!(byte != 0, "input contained interior nul");
    }
}

#[allow(
    clippy::alloc_instead_of_core,
    clippy::std_instead_of_alloc,
    clippy::std_instead_of_core,
    clippy::undocumented_unsafe_blocks,
    clippy::wildcard_imports
)]
#[cfg(test)]
mod tests {
    use core::ffi::CStr;

    #[test]
    fn test_c_macro() {
        #[track_caller]
        fn t(s: &CStr, raw: &[u8]) {
            assert_eq!(s.to_bytes_with_nul(), raw);
        }
        t(c!(""), b"\0");
        t(c!("a"), b"a\0");
        t(c!("abc"), b"abc\0");
        t(c!(concat!("abc", "d")), b"abcd\0");
    }

    #[test]
    fn test_is_c_str() {
        #[track_caller]
        fn t(bytes: &[u8]) {
            assert_eq!(
                std::panic::catch_unwind(|| super::const_c_str_check(bytes)).is_ok(),
                CStr::from_bytes_with_nul(bytes).is_ok()
            );
        }
        t(b"\0");
        t(b"a\0");
        t(b"abc\0");
        t(b"");
        t(b"a");
        t(b"abc");
        t(b"\0a");
        t(b"\0a\0");
        t(b"ab\0c\0");
        t(b"\0\0");
    }
}
