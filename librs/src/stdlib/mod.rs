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

// ffi CStr is unstable yet,
pub mod malloc;
use crate::{c_str::CStr, ctype, errno::ERRNO, types::c_int};
use core::{
    ffi::{c_char, c_double, c_float, c_long, c_longlong, c_uint, c_ulong, c_ulonglong},
    ptr,
};
use libc::{EINVAL, ERANGE};

#[linkage = "weak"]
#[no_mangle]
pub unsafe extern "C" fn getenv(_key: *const i8) -> *mut i8 {
    core::ptr::null_mut()
}

#[macro_export]
macro_rules! strto_float_impl {
    ($type:ident, $s:expr, $endptr:expr) => {{
        let mut s = $s;
        let endptr = $endptr;

        while ctype::isspace(*s as c_int) != 0 {
            s = s.offset(1);
        }

        let mut result: $type = 0.0;
        let mut exponent: Option<$type> = None;
        let mut radix = 10;

        let result_sign = match *s as u8 {
            b'-' => {
                s = s.offset(1);
                -1.0
            }
            b'+' => {
                s = s.offset(1);
                1.0
            }
            _ => 1.0,
        };

        let rust_s = CStr::from_ptr(s).to_string_lossy();

        // detect NaN, Inf
        if rust_s.to_lowercase().starts_with("inf") {
            result = $type::INFINITY;
            s = s.offset(3);
        } else if rust_s.to_lowercase().starts_with("nan") {
            // we cannot signal negative NaN in LLVM backed languages
            // https://github.com/rust-lang/rust/issues/73328 , https://github.com/rust-lang/rust/issues/81261
            result = $type::NAN;
            s = s.offset(3);
        } else {
            if *s as u8 == b'0' && *s.offset(1) as u8 == b'x' {
                s = s.offset(2);
                radix = 16;
            }

            while let Some(digit) = (*s as u8 as char).to_digit(radix) {
                result *= radix as $type;
                result += digit as $type;
                s = s.offset(1);
            }

            if *s as u8 == b'.' {
                s = s.offset(1);

                let mut i = 1.0;
                while let Some(digit) = (*s as u8 as char).to_digit(radix) {
                    i *= radix as $type;
                    result += digit as $type / i;
                    s = s.offset(1);
                }
            }

            let s_before_exponent = s;

            exponent = match (*s as u8, radix) {
                (b'e' | b'E', 10) | (b'p' | b'P', 16) => {
                    s = s.offset(1);

                    let is_exponent_positive = match *s as u8 {
                        b'-' => {
                            s = s.offset(1);
                            false
                        }
                        b'+' => {
                            s = s.offset(1);
                            true
                        }
                        _ => true,
                    };

                    // Exponent digits are always in base 10.
                    if (*s as u8 as char).is_digit(10) {
                        let mut exponent_value = 0;

                        while let Some(digit) = (*s as u8 as char).to_digit(10) {
                            exponent_value *= 10;
                            exponent_value += digit;
                            s = s.offset(1);
                        }

                        let exponent_base = match radix {
                            10 => 10u128,
                            16 => 2u128,
                            _ => unreachable!(),
                        };

                        if is_exponent_positive {
                            Some(exponent_base.pow(exponent_value) as $type)
                        } else {
                            Some(1.0 / (exponent_base.pow(exponent_value) as $type))
                        }
                    } else {
                        // Exponent had no valid digits after 'e'/'p' and '+'/'-', rollback
                        s = s_before_exponent;
                        None
                    }
                }
                _ => None,
            };
        }

        if !endptr.is_null() {
            // This is stupid, but apparently strto* functions want
            // const input but mut output, yet the man page says
            // "stores the address of the first invalid character in *endptr"
            // so obviously it doesn't want us to clone it.
            *endptr = s as *mut _;
        }

        if let Some(exponent) = exponent {
            result_sign * result * exponent
        } else {
            result_sign * result
        }
    }};
}

#[macro_export]
macro_rules! primitive_to_ascii {
    ($type:ty, $n:expr,$s:expr, $radix:expr) => {
        #[allow(unused_comparisons)]
        {
            let mut n: $type = $n;
            let mut i = 0;
            let mut is_negative = false;
            let s = $s;
            if n < 0 {
                is_negative = true;
                n = 0 - n;
            }

            let mut buffer = [0 as c_char; 33];
            loop {
                let rem = n % ($radix as $type);
                buffer[i] = if rem < 10 {
                    (rem + b'0' as $type) as c_char
                } else {
                    (rem - 10 + b'a' as $type) as c_char
                };
                i += 1;
                n /= $radix as $type;
                if n == 0 {
                    break;
                }
            }

            if is_negative {
                buffer[i] = b'-' as c_char;
                i += 1;
            }

            for j in 0..i {
                *s.add(j) = buffer[i - 1 - j];
            }

            *s.add(i) = 0;
            s
        }
    };
}

#[macro_export]
macro_rules! strto_impl {
    (
        $rettype:ty, $signed:expr, $maxval:expr, $minval:expr, $s:ident, $endptr:ident, $base:ident
    ) => {{
        // ensure these are constants
        const CHECK_SIGN: bool = $signed;
        const MAX_VAL: $rettype = $maxval;
        const MIN_VAL: $rettype = $minval;

        let set_endptr = |idx: isize| {
            if !$endptr.is_null() {
                // This is stupid, but apparently strto* functions want
                // const input but mut output, yet the man page says
                // "stores the address of the first invalid character in *endptr"
                // so obviously it doesn't want us to clone it.
                *$endptr = $s.offset(idx) as *mut _;
            }
        };

        let invalid_input = || {
            ERRNO.set(EINVAL);
            set_endptr(0);
        };

        // only valid bases are 2 through 36
        if $base != 0 && !(2..=36).contains(&$base) {
            invalid_input();
            return 0;
        }

        let mut idx = 0;

        // skip any whitespace at the beginning of the string
        while ctype::isspace(*$s.offset(idx) as c_int) != 0 {
            idx += 1;
        }

        // check for +/-
        let positive = match is_positive(*$s.offset(idx)) {
            Some((pos, i)) => {
                idx += i;
                pos
            }
            None => {
                invalid_input();
                return 0;
            }
        };

        // convert the string to a number
        let num_str = $s.offset(idx);
        let res = match $base {
            0 => detect_base(num_str)
                .and_then(|($base, i)| convert_integer(num_str.offset(i), $base)),
            8 => convert_octal(num_str),
            16 => convert_hex(num_str),
            _ => convert_integer(num_str, $base),
        };

        // check for error parsing octal/hex prefix
        // also check to ensure a number was indeed parsed
        let (num, i, overflow) = match res {
            Some(res) => res,
            None => {
                invalid_input();
                return 0;
            }
        };
        idx += i;

        let overflow = if CHECK_SIGN {
            overflow || (num as c_long).is_negative()
        } else {
            overflow
        };
        // account for the sign
        let num = num as $rettype;
        let num = if overflow {
            ERRNO.set(ERANGE);
            if CHECK_SIGN {
                if positive {
                    MAX_VAL
                } else {
                    MIN_VAL
                }
            } else {
                MAX_VAL
            }
        } else {
            if positive {
                num
            } else {
                // not using -num to keep the compiler happy
                num.overflowing_neg().0
            }
        };

        set_endptr(idx);

        num
    }};
}

macro_rules! dec_num_from_ascii {
    ($s:expr, $t:ty) => {{
        let mut s = $s;
        // Iterate past whitespace
        while ctype::isspace(*s as c_int) != 0 {
            s = s.offset(1);
        }

        // Find out if there is a - sign
        let neg_sign = match *s {
            0x2d => {
                s = s.offset(1);
                true
            }
            // '+' increment s and continue parsing
            0x2b => {
                s = s.offset(1);
                false
            }
            _ => false,
        };

        let mut n: $t = 0;
        while ctype::isdigit(*s as c_int) != 0 {
            n = 10 * n - (*s as $t - 0x30);
            s = s.offset(1);
        }

        if neg_sign {
            n
        } else {
            -n
        }
    }};
}

#[no_mangle]
pub extern "C" fn abs(i: c_int) -> c_int {
    i.abs()
}

#[no_mangle]
pub unsafe extern "C" fn atof(s: *const c_char) -> c_double {
    strtod(s, ptr::null_mut())
}

#[no_mangle]
pub unsafe extern "C" fn atoi(s: *const c_char) -> c_int {
    dec_num_from_ascii!(s, c_int)
}
#[no_mangle]
pub unsafe extern "C" fn atol(s: *const c_char) -> c_long {
    dec_num_from_ascii!(s, c_long)
}
#[no_mangle]
pub unsafe extern "C" fn atoll(s: *const c_char) -> c_longlong {
    dec_num_from_ascii!(s, c_longlong)
}

#[no_mangle]
pub unsafe extern "C" fn strtod(s: *const c_char, endptr: *mut *mut c_char) -> c_double {
    strto_float_impl!(c_double, s, endptr)
}

#[no_mangle]
pub unsafe extern "C" fn strtof(s: *const c_char, endptr: *mut *mut c_char) -> c_float {
    strto_float_impl!(c_float, s, endptr)
}

#[no_mangle]
pub unsafe extern "C" fn strtol(s: *const c_char, endptr: *mut *mut c_char, base: c_int) -> c_long {
    strto_impl!(c_long, true, c_long::MAX, c_long::MIN, s, endptr, base)
}

#[no_mangle]
pub unsafe extern "C" fn strtold(_s: *const c_char, _endptr: *mut *mut c_char) -> ! {
    todo!("c_longdouble is not stable in llvm  yet!")
}

#[no_mangle]
pub unsafe extern "C" fn strtoll(
    s: *const c_char,
    endptr: *mut *mut c_char,
    base: c_int,
) -> c_longlong {
    strto_impl!(
        c_longlong,
        true,
        c_longlong::MAX,
        c_longlong::MIN,
        s,
        endptr,
        base
    )
}

#[no_mangle]
pub unsafe extern "C" fn strtoul(
    s: *const c_char,
    endptr: *mut *mut c_char,
    base: c_int,
) -> c_ulong {
    strto_impl!(c_ulong, false, c_ulong::MAX, c_ulong::MIN, s, endptr, base)
}

#[no_mangle]
pub unsafe extern "C" fn strtoull(
    s: *const c_char,
    endptr: *mut *mut c_char,
    base: c_int,
) -> c_ulonglong {
    strto_impl!(
        c_ulonglong,
        false,
        c_ulonglong::MAX,
        c_ulonglong::MIN,
        s,
        endptr,
        base
    )
}

#[no_mangle]
pub unsafe extern "C" fn itoa(n: c_int, s: *mut c_char, radix: c_int) -> *mut c_char {
    primitive_to_ascii!(c_int, n, s, radix)
}

#[no_mangle]
pub unsafe extern "C" fn ultoa(n: c_ulong, s: *mut c_char, radix: c_int) -> *mut c_char {
    primitive_to_ascii!(c_ulong, n, s, radix)
}

#[no_mangle]
pub unsafe extern "C" fn ulltoa(n: c_ulonglong, s: *mut c_char, radix: c_int) -> *mut c_char {
    primitive_to_ascii!(c_ulonglong, n, s, radix)
}

#[no_mangle]
pub unsafe extern "C" fn utoa(n: c_uint, s: *mut c_char, radix: c_int) -> *mut c_char {
    primitive_to_ascii!(c_uint, n, s, radix)
}

// todo: implement the rest of the functions
#[no_mangle]
pub unsafe extern "C" fn ltoa(n: c_long, s: *mut c_char, radix: c_int) -> *mut c_char {
    primitive_to_ascii!(c_long, n, s, radix)
}

// todo: implement the rest of the functions
#[no_mangle]
pub unsafe extern "C" fn lltoa(n: c_longlong, s: *mut c_char, radix: c_int) -> *mut c_char {
    primitive_to_ascii!(c_longlong, n, s, radix)
}

#[repr(C)]
#[allow(non_camel_case_types)]
pub struct lldiv_t {
    quot: c_longlong,
    rem: c_longlong,
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/ldiv.html>.
#[no_mangle]
pub extern "C" fn lldiv(numer: c_longlong, denom: c_longlong) -> lldiv_t {
    lldiv_t {
        quot: numer / denom,
        rem: numer % denom,
    }
}

#[repr(C)]
#[allow(non_camel_case_types)]
pub struct ldiv_t {
    quot: c_long,
    rem: c_long,
}

/// See <https://pubs.opengroup.org/onlinepubs/9799919799/functions/ldiv.html>.
#[no_mangle]
pub extern "C" fn ldiv(numer: c_long, denom: c_long) -> ldiv_t {
    ldiv_t {
        quot: numer / denom,
        rem: numer % denom,
    }
}

#[no_mangle]
pub extern "C" fn labs(i: c_long) -> c_long {
    i.abs()
}

#[no_mangle]
pub extern "C" fn llabs(i: c_longlong) -> c_longlong {
    i.abs()
}

#[repr(C)]
#[allow(non_camel_case_types)]
pub struct div_t {
    quot: c_int,
    rem: c_int,
}

#[no_mangle]
pub extern "C" fn div(numer: c_int, denom: c_int) -> div_t {
    div_t {
        quot: numer / denom,
        rem: numer % denom,
    }
}

pub unsafe fn detect_base(s: *const c_char) -> Option<(c_int, isize)> {
    let first = *s as u8;
    match first {
        0 => None,
        b'0' => {
            let second = *s.offset(1) as u8;
            if second == b'X' || second == b'x' {
                Some((16, 2))
            } else if (b'0'..=b'7').contains(&second) {
                Some((8, 1))
            } else {
                // in this case, the prefix (0) is going to be the number
                Some((8, 0))
            }
        }
        _ => Some((10, 0)),
    }
}

pub unsafe fn convert_octal(s: *const c_char) -> Option<(c_ulong, isize, bool)> {
    if *s != 0 && *s == b'0' as c_char {
        if let Some((val, idx, overflow)) = convert_integer(s.offset(1), 8) {
            Some((val, idx + 1, overflow))
        } else {
            // in case the prefix is not actually a prefix
            Some((0, 1, false))
        }
    } else {
        None
    }
}

pub unsafe fn convert_hex(s: *const c_char) -> Option<(c_ulong, isize, bool)> {
    if (*s != 0 && *s == b'0' as c_char)
        && (*s.offset(1) != 0 && (*s.offset(1) == b'x' as c_char || *s.offset(1) == b'X' as c_char))
    {
        convert_integer(s.offset(2), 16).map(|(val, idx, overflow)| (val, idx + 2, overflow))
    } else {
        convert_integer(s, 16)
    }
}

pub unsafe fn convert_integer(s: *const c_char, base: c_int) -> Option<(c_ulong, isize, bool)> {
    // -1 means the character is invalid
    #[rustfmt::skip]
    const LOOKUP_TABLE: [c_long; 256] = [
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
         0,  1,  2,  3,  4,  5,  6,  7,  8,  9, -1, -1, -1, -1, -1, -1,
        -1, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, -1, -1, -1, -1, -1,
        -1, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
        -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    ];

    let mut num: c_ulong = 0;
    let mut idx = 0;
    let mut overflowed = false;

    loop {
        // `-1 as usize` is usize::MAX
        // `-1 as u8 as usize` is u8::MAX
        // It extends by the sign bit unless we cast it to unsigned first.
        let val = LOOKUP_TABLE[*s.offset(idx) as u8 as usize];
        if val == -1 || val as c_int >= base {
            break;
        } else {
            if let Some(res) = num
                .checked_mul(base as c_ulong)
                .and_then(|num| num.checked_add(val as c_ulong))
            {
                num = res;
            } else {
                ERRNO.set(ERANGE);
                num = c_ulong::MAX;
                overflowed = true;
            }

            idx += 1;
        }
    }

    if idx > 0 {
        Some((num, idx, overflowed))
    } else {
        None
    }
}

pub fn is_positive(ch: c_char) -> Option<(bool, isize)> {
    match ch {
        0 => None,
        ch if ch == b'+' as c_char => Some((true, 1)),
        ch if ch == b'-' as c_char => Some((false, 1)),
        _ => Some((true, 0)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::println;
    use blueos_test_macro::test;
    //  NOTE: the following  two case will import 0x15444 - 0xff05 = 0x553f almost 20k bytes data
    //  in  .rodata section, just comment them now
    // Section Headers:
    // [Nr] Name              Type            Addr     Off    Size   ES Flg Lk Inf Al
    // [ 0]                   NULL            00000000 000000 000000 00      0   0  0
    // [ 1] .vector_table     PROGBITS        00000000 001000 000400 00   A  0   0  4
    // [ 2] .text             PROGBITS        00000400 001400 063770 00  AX  0   0  4
    // [ 3] .rodata           PROGBITS        00063b70 064b70 00ff05 00   A  0   0  8
    // [ 4] .ARM.exidx        ARM_EXIDX       00073a78 074a78 000018 00  AL  2   0  4
    // [ 5] .copy.table       PROGBITS        00073a90 074a90 00000c 00  WA  0   0  1
    // [ 6] .zero.table       PROGBITS        00073a9c 074a9c 000008 00  WA  0   0  1
    // [ 7] .data             PROGBITS        20000000 075000 003d80 00  WA  0   0 16
    // [ 8] .bss              NOBITS          20003d80 078d80 000050 00  WA  0   0  4

    // FIXME: use https://docs.rs/float-cmp/latest/float_cmp/
    #[cfg(not(target_os = "blueos"))]
    #[test]
    fn check_strtof() {
        let s = b"3.14\0";
        let endptr = ptr::null_mut();
        let result = unsafe { strtof(s.as_ptr() as *const c_char, endptr) };
        assert!((result - 3.14).abs() <= f32::EPSILON);
    }

    // FIXME: use https://docs.rs/float-cmp/latest/float_cmp/
    #[cfg(not(target_os = "blueos"))]
    #[test]
    fn check_strtod() {
        let s = b"3.14\0";
        let endptr = ptr::null_mut();
        let result = unsafe { strtod(s.as_ptr() as *const c_char, endptr) };
        assert!((result - 3.14).abs() <= f64::EPSILON);
    }

    // FIXME: use https://docs.rs/float-cmp/latest/float_cmp/
    #[cfg(not(target_os = "blueos"))]
    #[test]
    fn check_strtol() {
        let s = b"123\0";
        let endptr = ptr::null_mut();
        let result = unsafe { strtol(s.as_ptr() as *const c_char, endptr, 10) };
        assert_eq!(result, 123);
    }

    #[test]
    fn check_llabs() {
        let result = llabs(-9223372036854775807);
        assert_eq!(result, 9223372036854775807);
    }

    #[test]
    fn check_llabs_positive() {
        let result = llabs(9223372036854775807);
        assert_eq!(result, 9223372036854775807);
    }

    #[test]
    fn check_labs() {
        let result = labs(-2147483647);
        assert_eq!(result, 2147483647);
    }

    #[test]
    fn check_labs_positive() {
        let result = labs(2147483647);
        assert_eq!(result, 2147483647);
    }

    #[test]
    fn check_lldiv() {
        let result = lldiv(10, 3);
        assert_eq!(result.quot, 3);
        assert_eq!(result.rem, 1);
    }

    #[test]
    fn check_div() {
        let result = div(10, 3);
        assert_eq!(result.quot, 3);
        assert_eq!(result.rem, 1);
    }

    #[test]
    fn check_div_negative() {
        let result = div(-10, 3);
        assert_eq!(result.quot, -3);
        assert_eq!(result.rem, -1);
    }

    #[test]
    fn check_lldiv_negative() {
        let result = lldiv(-10, 3);
        assert_eq!(result.quot, -3);
        assert_eq!(result.rem, -1);
    }

    #[test]
    fn check_atoi() {
        let s = b"123\0";
        let result = unsafe { atoi(s.as_ptr() as *const c_char) };
        assert_eq!(result, 123);
    }

    #[test]
    fn check_atol() {
        let s = b"123\0";
        let result = unsafe { atol(s.as_ptr() as *const c_char) };
        assert_eq!(result, 123);
    }

    #[test]
    fn check_ultoa() {
        let mut buffer = [0 as c_char; 33];
        let result = unsafe { ultoa(4294967295, buffer.as_mut_ptr(), 10) };
        unsafe { assert_eq!(*result, *(c"4294967295".as_ptr() as *mut c_char)) };
    }

    #[test]
    fn check_lltoa() {
        let mut buffer = [0 as c_char; 33];
        let result = unsafe { lltoa(9223372036854775807, buffer.as_mut_ptr(), 10) };
        unsafe { assert_eq!(*result, *(c"9223372036854775807".as_ptr() as *mut c_char)) };
    }
}
