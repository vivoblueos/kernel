// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use core::{
    ffi::{c_char, c_int, c_size_t, c_void},
    marker::PhantomData,
    ptr::NonNull,
};

/// A minimal alternative to the `Zero` trait from num-traits, for use in
/// `NulTerminated`.
///
/// May be replaced with the one from num-traits at a later time if so
/// desired.
pub unsafe trait Zero {
    fn is_zero(&self) -> bool;
}

unsafe impl Zero for c_char {
    fn is_zero(&self) -> bool {
        self == &0
    }
}

/// An iterator over a nul-terminated buffer.
///
/// This is intended to allow safe, ergonomic iteration over C-style byte and
/// wide strings without first having to read through the string and construct
/// a slice. Assuming the safety requirements are upheld when constructing the
/// iterator, it allows for string iteration in safe Rust.
pub struct NulTerminated<'a, T: Zero> {
    ptr: NonNull<T>,
    phantom: PhantomData<&'a T>,
}

impl<'a, T: Zero> Iterator for NulTerminated<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: the caller is required to ensure a valid pointer to a
        // 0-terminated buffer is provided, and the zero-check below ensures
        // that iteration and pointer increments will stop in time.
        let val_ref = unsafe { self.ptr.as_ref() };
        if val_ref.is_zero() {
            None
        } else {
            // SAFETY: the caller is required to provide a 0-terminated
            // buffer, and this point will only be reached if the next element
            // is at most the terminating 0.
            self.ptr = unsafe { self.ptr.add(1) };
            Some(val_ref)
        }
    }
}

impl<T: Zero> NulTerminated<'_, T> {
    /// Constructs a new iterator, starting at `ptr`, yielding elements of
    /// type `&T` up to (but not including) the terminating nul.
    ///
    /// The iterator returns `None` after the terminating nul has been
    /// encountered.
    ///
    /// # Safety
    /// The provided pointer must be a valid pointer to a buffer of contiguous
    /// elements of type `T`, and the value 0 must be present within the
    /// buffer at or after `ptr` (not necessarily at the end). The buffer must
    /// not be written to for the lifetime of the iterator.
    pub unsafe fn new(ptr: *const T) -> Self {
        NulTerminated {
            // NonNull can only wrap only *mut pointers...
            ptr: NonNull::new(ptr.cast_mut()).unwrap(),
            phantom: PhantomData,
        }
    }
}

// used by core/src/slice/cmp.rs
/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/memcmp.html>.
#[cfg_attr(not(miri), linkage = "weak")]
#[cfg_attr(not(miri), no_mangle)]
pub unsafe extern "C" fn memcmp(s1: *const c_void, s2: *const c_void, n: c_size_t) -> c_int {
    let mut a = s1 as *const u8;
    let mut b = s2 as *const u8;
    for _ in 0..n {
        if *a != *b {
            return *a as c_int - *b as c_int;
        }
        a = a.add(1);
        b = b.add(1);
    }
    0
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/memcpy.html>.
#[cfg_attr(not(miri), linkage = "weak")]
#[cfg_attr(not(miri), no_mangle)]
pub unsafe extern "C" fn memcpy(s1: *mut c_void, s2: *const c_void, n: c_size_t) -> *mut c_void {
    let mut i = 0;
    while i < n {
        *(s1 as *mut u8).add(i) = *(s2 as *const u8).add(i);
        i += 1;
    }
    s1
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/memmove.html>.
#[cfg_attr(not(miri), linkage = "weak")]
#[cfg_attr(not(miri), no_mangle)]
pub unsafe extern "C" fn memmove(s1: *mut c_void, s2: *const c_void, n: c_size_t) -> *mut c_void {
    let s1_bytes = s1 as *mut u8;
    let s2_bytes = s2 as *mut u8;
    if s1_bytes <= s2_bytes || s1_bytes >= s2_bytes.add(n) {
        for i in 0..n {
            *s1_bytes.add(i) = *s2_bytes.add(i);
        }
    } else {
        let mut i = n;
        while i > 0 {
            i -= 1;
            *s1_bytes.add(i) = *s2_bytes.add(i);
        }
    }
    s1
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/memset.html>.
#[cfg_attr(not(miri), linkage = "weak")]
#[cfg_attr(not(miri), no_mangle)]
pub unsafe extern "C" fn memset(s: *mut c_void, c: c_int, n: c_size_t) -> *mut c_void {
    for i in 0..n {
        *(s as *mut u8).add(i) = c as u8;
    }
    s
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/strncpy.html>.
#[cfg_attr(not(miri), linkage = "weak")]
#[cfg_attr(not(miri), no_mangle)]
pub unsafe extern "C" fn stpncpy(
    mut s1: *mut c_char,
    mut s2: *const c_char,
    mut n: c_size_t,
) -> *mut c_char {
    while n > 0 {
        *s1 = *s2;

        if *s1 == 0 {
            break;
        }

        n -= 1;
        s1 = s1.add(1);
        s2 = s2.add(1);
    }

    memset(s1.cast(), 0, n);

    s1
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/strncpy.html>.
#[cfg_attr(not(miri), linkage = "weak")]
#[cfg_attr(not(miri), no_mangle)]
pub unsafe extern "C" fn strncpy(s1: *mut c_char, s2: *const c_char, n: c_size_t) -> *mut c_char {
    stpncpy(s1, s2, n);
    s1
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/strlen.html>.
#[cfg_attr(not(miri), linkage = "weak")]
#[cfg_attr(not(miri), no_mangle)]
pub unsafe extern "C" fn strlen(s: *const c_char) -> c_size_t {
    unsafe { NulTerminated::new(s) }.count()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/strlen.html>.
#[cfg_attr(not(miri), linkage = "weak")]
#[cfg_attr(not(miri), no_mangle)]
pub unsafe extern "C" fn strnlen(s: *const c_char, size: c_size_t) -> c_size_t {
    unsafe { NulTerminated::new(s) }.take(size).count()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/abort.html>.
#[cfg_attr(not(miri), linkage = "weak")]
#[cfg_attr(not(miri), no_mangle)]
pub unsafe extern "C" fn abort() -> ! {
    core::intrinsics::abort();
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::ffi::c_char;

    #[test]
    fn test_memcpy() {
        let src: [u8; 5] = [1, 2, 3, 4, 5];
        let mut dst: [u8; 5] = [0; 5];

        unsafe {
            memcpy(
                dst.as_mut_ptr() as *mut core::ffi::c_void,
                src.as_ptr() as *const core::ffi::c_void,
                5,
            );
        }

        assert_eq!(dst, [1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_memset() {
        let mut buf: [u8; 5] = [1, 2, 3, 4, 5];

        unsafe {
            memset(buf.as_mut_ptr() as *mut core::ffi::c_void, 0, 5);
        }

        assert_eq!(buf, [0, 0, 0, 0, 0]);
    }

    #[test]
    fn test_memcmp() {
        let a: [u8; 5] = [1, 2, 3, 4, 5];
        let b: [u8; 5] = [1, 2, 3, 4, 5];
        let c: [u8; 5] = [1, 2, 3, 4, 6];

        unsafe {
            assert_eq!(
                memcmp(
                    a.as_ptr() as *const core::ffi::c_void,
                    b.as_ptr() as *const core::ffi::c_void,
                    5,
                ),
                0
            );

            assert_eq!(
                memcmp(
                    a.as_ptr() as *const core::ffi::c_void,
                    c.as_ptr() as *const core::ffi::c_void,
                    5,
                ),
                -1
            );

            assert_eq!(
                memcmp(
                    c.as_ptr() as *const core::ffi::c_void,
                    a.as_ptr() as *const core::ffi::c_void,
                    5,
                ),
                1
            );
        }
    }

    #[test]
    fn test_memmove() {
        let mut data = vec![1u8, 2, 3, 4, 5];
        let ptr = data.as_mut_ptr();
        unsafe {
            memmove(ptr.add(1) as *mut c_void, ptr as *const c_void, 4);
        }
        assert_eq!(data, [1, 1, 2, 3, 4]);
    }

    #[test]
    fn test_strncpy() {
        let src = c"hello";
        let mut dst = [0 as c_char; 10];

        unsafe {
            strncpy(dst.as_mut_ptr(), src.as_ptr() as *const c_char, 3);

            assert_eq!(dst[0], b'h' as c_char);
            assert_eq!(dst[1], b'e' as c_char);
            assert_eq!(dst[2], b'l' as c_char);
            assert_eq!(dst[3], 0);
        }
    }

    #[test]
    fn test_strlen() {
        let s = c"hello";

        unsafe {
            assert_eq!(strlen(s.as_ptr() as *const c_char), 5);

            assert_eq!(strlen(c"".as_ptr() as *const c_char), 0);
        }
    }

    #[test]
    fn test_strnlen() {
        let s = c"hello";

        unsafe {
            assert_eq!(strnlen(s.as_ptr() as *const c_char, 10), 5);

            assert_eq!(strnlen(s.as_ptr() as *const c_char, 3), 3);

            assert_eq!(strnlen(c"".as_ptr() as *const c_char, 10), 0);
        }
    }
}
