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
//
// This code is based on relibc (original license follows):
// https://github.com/redox-os/relibc/blob/master/LICENSE
// standard MIT license

//! `string.h` implementation.
//!
//! See <https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/string.h.html>.

use crate::{
    errno::STR_ERROR,
    iter::{NullTerminated, NullTerminatedInclusive},
    stdio::StringWriter,
};
use core::{
    cmp::Ordering,
    ffi::{c_char, c_int, c_long, c_longlong, c_size_t, c_void},
    fmt::Write,
    ptr, slice,
};
use libc::ERANGE;

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/memccpy.html>.
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn memccpy(
    dest: *mut c_void,
    src: *const c_void,
    c: c_int,
    n: c_size_t,
) -> *mut c_void {
    let to = memchr(src, c, n);
    if to.is_null() {
        return to;
    }
    let dist = (to as usize) - (src as usize);
    if memcpy(dest, src, dist).is_null() {
        return ptr::null_mut();
    }
    (dest as *mut u8).add(dist + 1) as *mut c_void
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/memchr.html>.
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn memchr(
    haystack: *const c_void,
    needle: c_int,
    len: c_size_t,
) -> *mut c_void {
    let haystack = slice::from_raw_parts(haystack as *const u8, len);

    match core::slice::memchr::memchr(needle as u8, haystack) {
        Some(index) => haystack[index..].as_ptr() as *mut c_void,
        None => ptr::null_mut(),
    }
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/memcpy.html>.
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn memcpy(s1: *mut c_void, s2: *const c_void, n: c_size_t) -> *mut c_void {
    let mut i = 0;
    while i < n {
        *(s1 as *mut u8).add(i) = *(s2 as *const u8).add(i);
        i += 1;
    }
    s1
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/memmove.html>.
#[linkage = "weak"]
#[no_mangle]
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
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn memset(s: *mut c_void, c: c_int, n: c_size_t) -> *mut c_void {
    for i in 0..n {
        *(s as *mut u8).add(i) = c as u8;
    }
    s
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/memcmp.html>.
#[linkage = "weak"]
#[no_mangle]
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

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/strlen.html>.
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn strlen(s: *const c_char) -> c_size_t {
    unsafe { NullTerminated::new(s) }.count()
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/strerror.html>.
/// posix don't need this thread safe, simple using raw operator diable warning
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn strerror(errnum: c_int) -> *mut c_char {
    static mut STRERROR_BUF: [u8; 256] = [0; 256];
    let buf = &raw mut STRERROR_BUF;

    let mut w = StringWriter(buf.as_mut_ptr(), 256);

    if errnum >= 0 && errnum < STR_ERROR.len() as c_int {
        let _ = w.write_str(STR_ERROR[errnum as usize]);
    } else {
        let _ = w.write_str("Unknown error {}");
    }

    buf.as_mut_ptr() as *mut c_char
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/strerror.html>.
#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn strerror_r(errnum: c_int, buf: *mut c_char, buflen: c_size_t) -> c_int {
    let msg = strerror(errnum);
    let len = strlen(msg);

    if len >= buflen {
        if buflen != 0 {
            memcpy(buf as *mut c_void, msg as *const c_void, buflen - 1);
            *buf.add(buflen - 1) = 0;
        }
        return ERANGE as c_int;
    }
    memcpy(buf as *mut c_void, msg as *const c_void, len + 1);

    0
}

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn __xpg_strerror_r(
    errnum: c_int,
    buf: *mut c_char,
    buflen: c_size_t,
) -> c_int {
    strerror_r(errnum, buf, buflen)
}

#[deprecated]
#[no_mangle]
pub unsafe extern "C" fn bcmp(first: *const c_void, second: *const c_void, n: c_size_t) -> c_int {
    unsafe { memcmp(first, second, n) }
}

#[deprecated]
#[no_mangle]
pub unsafe extern "C" fn bcopy(src: *const c_void, dst: *mut c_void, n: c_size_t) {
    unsafe {
        ptr::copy(src as *const u8, dst as *mut u8, n);
    }
}

#[deprecated]
#[no_mangle]
pub unsafe extern "C" fn bzero(dst: *mut c_void, n: c_size_t) {
    unsafe {
        ptr::write_bytes(dst as *mut u8, 0, n);
    }
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/bsearch.html
#[no_mangle]
pub unsafe extern "C" fn bsearch(
    key: *const c_void,
    base: *const c_void,
    nmemb: c_size_t,
    size: c_size_t,
    compare: Option<unsafe extern "C" fn(*const c_void, *const c_void) -> c_int>,
) -> *mut c_void {
    let mut low = 0;
    let mut high = nmemb as isize - 1;
    let ptr = base as *const u8;
    while low <= high {
        let mid = low + (high - low) / 2;
        let cmp = compare.unwrap()(key, ptr.offset(mid * size as isize) as *const c_void);
        match cmp.cmp(&0) {
            Ordering::Equal => return ptr.offset(mid * size as isize) as *mut c_void,
            Ordering::Less => high = mid - 1,
            Ordering::Greater => low = mid + 1,
        }
    }
    ptr::null_mut()
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/ffs.html
#[no_mangle]
pub extern "C" fn ffs(i: c_int) -> c_int {
    if i == 0 {
        return 0;
    }
    1 + i.trailing_zeros() as c_int
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/ffsl.html
#[no_mangle]
pub extern "C" fn ffsl(i: c_long) -> c_int {
    if i == 0 {
        return 0;
    }
    1 + i.trailing_zeros() as c_int
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/ffsll.html
#[no_mangle]
pub extern "C" fn ffsll(i: c_longlong) -> c_int {
    if i == 0 {
        return 0;
    }
    1 + i.trailing_zeros() as c_int
}

#[deprecated]
#[no_mangle]
pub unsafe extern "C" fn index(s: *const c_char, c: c_int) -> *mut c_char {
    unsafe { strchr(s, c) }
}

#[deprecated]
#[no_mangle]
pub unsafe extern "C" fn rindex(s: *const c_char, c: c_int) -> *mut c_char {
    unsafe { strrchr(s, c) }
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strchr.html
#[no_mangle]
pub unsafe extern "C" fn strchr(s: *const c_char, c: c_int) -> *mut c_char {
    let c_as_c_char = c as c_char;

    // We iterate over non-mut references and thus need to coerce the
    // resulting reference via a *const pointer before we can get our *mut.
    // SAFETY: the caller is required to ensure that s points to a valid
    // nul-terminated buffer.
    let ptr: *const c_char =
        match unsafe { NullTerminatedInclusive::new(s) }.find(|&&sc| sc == c_as_c_char) {
            Some(sc_ref) => sc_ref,
            None => ptr::null(),
        };
    ptr.cast_mut()
}

#[no_mangle]
pub unsafe extern "C" fn strchrnul(s: *const c_char, c: c_int) -> *mut c_char {
    let mut s = s.cast_mut();
    loop {
        if *s == c as _ {
            break;
        }
        if *s == 0 {
            break;
        }
        s = s.add(1);
    }
    s
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strcspn.html
#[no_mangle]
pub unsafe extern "C" fn strcspn(s1: *const c_char, s2: *const c_char) -> c_size_t {
    let s1 = slice::from_raw_parts(s1 as *const u8, strlen(s1) as usize);
    let s2 = slice::from_raw_parts(s2 as *const u8, strlen(s2) as usize);

    for (i, &c) in s1.iter().enumerate() {
        if s2.iter().any(|&x| x == c) {
            return i as c_size_t;
        }
    }

    s1.len() as c_size_t
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strpbrk.html
#[no_mangle]
pub unsafe extern "C" fn strpbrk(s1: *const c_char, s2: *const c_char) -> *mut c_char {
    let p = s1.add(strcspn(s1, s2));
    if *p != 0 {
        p as *mut c_char
    } else {
        ptr::null_mut()
    }
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strtok.html
#[no_mangle]
pub unsafe extern "C" fn strtok(s1: *mut c_char, delimiter: *const c_char) -> *mut c_char {
    static mut HAYSTACK: *mut c_char = ptr::null_mut();
    strtok_r(s1, delimiter, &raw mut HAYSTACK)
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strtok_r.html
#[no_mangle]
pub unsafe extern "C" fn strtok_r(
    s: *mut c_char,
    delimiter: *const c_char,
    lasts: *mut *mut c_char,
) -> *mut c_char {
    // Loosely based on GLIBC implementation
    let mut haystack = s;
    if haystack.is_null() {
        if (*lasts).is_null() {
            return ptr::null_mut();
        }
        haystack = *lasts;
    }

    // Skip past any extra delimiter left over from previous call
    haystack = haystack.add(strspn(haystack, delimiter));
    if *haystack == 0 {
        *lasts = ptr::null_mut();
        return ptr::null_mut();
    }

    // Build token by injecting null byte into delimiter
    let token = haystack;
    haystack = strpbrk(token, delimiter);
    if !haystack.is_null() {
        haystack.write(0);
        haystack = haystack.add(1);
        *lasts = haystack;
    } else {
        *lasts = ptr::null_mut();
    }

    token
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strspn.html
#[no_mangle]
pub unsafe extern "C" fn strspn(s1: *const c_char, s2: *const c_char) -> c_size_t {
    let s1 = slice::from_raw_parts(s1 as *const u8, strlen(s1) as usize);
    let s2 = slice::from_raw_parts(s2 as *const u8, strlen(s2) as usize);

    for (i, &c) in s1.iter().enumerate() {
        if !s2.iter().any(|&x| x == c) {
            return i as c_size_t;
        }
    }

    s1.len() as c_size_t
}

/// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strrchr.html
#[no_mangle]
pub unsafe extern "C" fn strrchr(s: *const c_char, c: c_int) -> *mut c_char {
    let len = strlen(s) as isize;
    let c = c as i8;
    let mut i = len - 1;
    while i >= 0 {
        if *s.offset(i) == c {
            return s.offset(i) as *mut c_char;
        }
        i -= 1;
    }
    ptr::null_mut()
}
#[cfg(dedup)]
mod dup {
    use super::super::*;
    /// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strncmp.html
    #[no_mangle]
    pub unsafe extern "C" fn strncmp(s1: *const c_char, s2: *const c_char, n: c_size_t) -> c_int {
        let s1 = slice::from_raw_parts(s1 as *const c_uchar, n);
        let s2 = slice::from_raw_parts(s2 as *const c_uchar, n);

        for (&a, &b) in s1.iter().zip(s2.iter()) {
            let val = (a as c_int) - (b as c_int);
            if a != b || a == 0 {
                return val;
            }
        }

        0
    }

    /// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strcmp.html
    #[no_mangle]
    pub unsafe extern "C" fn strcmp(s1: *const c_char, s2: *const c_char) -> c_int {
        strncmp(s1, s2, usize::MAX)
    }
    /// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strcoll.html
    #[no_mangle]
    pub unsafe extern "C" fn strcoll(s1: *const c_char, s2: *const c_char) -> c_int {
        strcmp(s1, s2)
    }

    /// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strxfrm.html
    #[no_mangle]
    pub unsafe extern "C" fn strxfrm(s1: *mut c_char, s2: *const c_char, n: c_size_t) -> c_size_t {
        let len = strlen(s2);
        if len < n {
            strcpy(s1, s2);
        }
        len
    }

    /// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strcpy.html
    #[no_mangle]
    pub unsafe extern "C" fn strcpy(dst: *mut c_char, src: *const c_char) -> *mut c_char {
        let src_iter = unsafe { NullTerminated::new(src) };
        let src_dest_iter = unsafe { SrcDstPtrIter::new(src_iter.chain(once(&0)), dst) };
        for (src_item, dst_item) in src_dest_iter {
            dst_item.write(*src_item);
        }

        dst
    }

    /// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strdup.html
    #[no_mangle]
    pub unsafe extern "C" fn strdup(s1: *const c_char) -> *mut c_char {
        strndup(s1, usize::MAX)
    }

    /// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strndup.html
    #[no_mangle]
    pub unsafe extern "C" fn strndup(s1: *const c_char, size: c_size_t) -> *mut c_char {
        let len = strnlen(s1, size);

        // the "+ 1" is to account for the NUL byte
        let buffer = malloc(len + 1) as *mut c_char;
        if buffer.is_null() {
            ERRNO.set(ENOMEM as c_int);
        } else {
            //memcpy(buffer, s1, len)
            for i in 0..len {
                *buffer.add(i) = *s1.add(i);
            }
            *buffer.add(len) = 0;
        }

        buffer
    }

    /// https://pubs.opengroup.org/onlinepubs/9799919799/functions/strnlen.html
    #[no_mangle]
    pub unsafe extern "C" fn strnlen(s: *const c_char, size: c_size_t) -> c_size_t {
        unsafe { NullTerminated::new(s) }.take(size).count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::println;
    use blueos_test_macro::test;

    #[test]
    fn check_ffs() {
        assert_eq!(ffs(0), 0);
        assert_eq!(ffs(1), 1);
        assert_eq!(ffs(16), 5);
    }

    #[test]
    fn check_ffsl() {
        assert_eq!(ffsl(0), 0);
        assert_eq!(ffsl(1), 1);
        assert_eq!(ffsl(1024), 11);
    }

    #[test]
    fn check_ffsll() {
        assert_eq!(ffsll(0), 0);
        assert_eq!(ffsll(1), 1);
        assert_eq!(ffsll(2048), 12);
    }

    #[test]
    fn check_strchr() {
        let s = b"hello world\0";
        let c = b'l' as c_int;
        let p = unsafe { strchr(s.as_ptr() as *const c_char, c) };
        assert_eq!(p, unsafe { s.as_ptr().add(2) } as *mut c_char);
    }

    #[test]
    fn check_strchrnul() {
        let s = b"hello world\0";
        let c = b'l' as c_int;
        let p = unsafe { strchrnul(s.as_ptr() as *const c_char, c) };
        assert_eq!(p, unsafe { s.as_ptr().add(2) } as *mut c_char);
    }

    #[test]
    fn check_strcspn() {
        let s1 = b"hello world\0";
        let s2 = b"aeiou\0";
        let n = unsafe { strcspn(s1.as_ptr() as *const c_char, s2.as_ptr() as *const c_char) };
        assert_eq!(n, 1);
    }

    #[test]
    fn check_strspn() {
        let s1 = b"hello world\0";
        let s2 = b"hello\0";
        let n = unsafe { strspn(s1.as_ptr() as *const c_char, s2.as_ptr() as *const c_char) };
        assert_eq!(n, 5);
    }

    #[test]
    fn check_strpbrk() {
        let s1 = b"hello world\0";
        let s2 = b"aeiou\0";
        let p = unsafe { strpbrk(s1.as_ptr() as *const c_char, s2.as_ptr() as *const c_char) };
        assert_eq!(p, unsafe { s1.as_ptr().add(1) } as *mut c_char);
    }

    #[test]
    fn check_strrchr() {
        let s = b"hello world\0";
        let c = b'l' as c_int;
        let p = unsafe { strrchr(s.as_ptr() as *const c_char, c) };
        assert_eq!(p, unsafe { s.as_ptr().add(9) } as *mut c_char);
    }

    #[test]
    fn check_memcpy() {
        // check the failed case source is 32 byte array
        let src = b"hellowor".repeat(4);
        let mut dst = [0u8; 32];
        unsafe {
            memcpy(
                dst.as_mut_ptr() as *mut c_void,
                src.as_ptr() as *const c_void,
                32,
            )
        };
        assert_eq!(dst, *src);
    }

    #[test]
    fn check_memcpy2() {
        // check the not aligned case
        let src = b"helloworld\0";
        let mut dst = [0u8; 11];
        unsafe {
            memcpy(
                dst.as_mut_ptr() as *mut c_void,
                src.as_ptr() as *const c_void,
                11,
            )
        };
        assert_eq!(dst, *src);
    }

    #[test]
    fn check_memmove() {
        let mut data = [1u8, 2, 3, 4, 5];
        let ptr = data.as_mut_ptr();
        unsafe {
            memmove(ptr.add(1) as *mut c_void, ptr as *const c_void, 4);
        }
        assert_eq!(data, [1, 1, 2, 3, 4]);
    }
}
