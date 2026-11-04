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

use super::lookaheadreader::LookAheadReader;
use alloc::{string::String, vec::Vec};
use core::ffi::VaList as va_list;
use libc::{
    c_char, c_double, c_float, c_int, c_long, c_longlong, c_short, c_uchar, c_uint, c_ulong,
    c_ulonglong, c_ushort, c_void, intmax_t, ptrdiff_t, size_t, ssize_t, uintmax_t,
};
#[derive(PartialEq, Eq)]
enum IntKind {
    Byte,
    Short,
    Int,
    Long,
    LongLong,
    IntMax,
    PtrDiff,
    Size,
}

/// Helper function for progressing a C string
unsafe fn next_byte(string: &mut *const c_char) -> Result<u8, c_int> {
    let c = **string as u8;
    *string = string.offset(1);
    if c == 0 {
        Err(-1)
    } else {
        Ok(c)
    }
}

unsafe fn inner_scanf(
    mut r: LookAheadReader,
    mut format: *const c_char,
    mut ap: va_list,
) -> Result<c_int, c_int> {
    let mut matched = 0;
    let mut byte = 0;
    let mut skip_read = false;
    let mut count = 0;

    macro_rules! read {
        () => {{
            match r.lookahead1() {
                Ok(None) => false,
                Ok(Some(b)) => {
                    byte = b;
                    count += 1;
                    true
                }
                Err(x) => return Err(x),
            }
        }};
    }

    macro_rules! maybe_read {
        () => {
            maybe_read!(inner false);
        };
        (noreset) => {
            maybe_read!(inner);
        };
        (inner $($placeholder:expr)*) => {
            if !skip_read && !read!() {
                match matched {
                    0 => return Ok(-1),
                    a => return Ok(a),
                }
            }
            $(else {
                // Hacky way of having this optional
                skip_read = $placeholder;
            })*
        }
    }

    while *format != 0 {
        let mut c = next_byte(&mut format)?;

        if c == b' ' {
            maybe_read!(noreset);

            while (byte as char).is_whitespace() {
                if !read!() {
                    return Ok(matched);
                }
            }

            skip_read = true;
        } else if c != b'%' {
            maybe_read!();
            if c != byte {
                return Ok(matched);
            }
            r.commit();
        } else {
            c = next_byte(&mut format)?;

            let mut ignore = false;
            if c == b'*' {
                ignore = true;
                c = next_byte(&mut format)?;
            }

            let mut width = String::new();
            while c.is_ascii_digit() {
                width.push(c as char);
                c = next_byte(&mut format)?;
            }
            let mut width = if width.is_empty() {
                None
            } else {
                match width.parse::<usize>() {
                    Ok(n) => Some(n),
                    Err(_) => return Err(-1),
                }
            };

            // When an EOF occurs, eof is set, stuff is marked matched
            // as usual, and finally it is returned
            let mut eof = false;

            let mut kind = IntKind::Int;
            loop {
                kind = match c {
                    b'h' => {
                        if kind == IntKind::Short || kind == IntKind::Byte {
                            IntKind::Byte
                        } else {
                            IntKind::Short
                        }
                    }
                    b'j' => IntKind::IntMax,
                    b'l' => {
                        if kind == IntKind::Long || kind == IntKind::LongLong {
                            IntKind::LongLong
                        } else {
                            IntKind::Long
                        }
                    }
                    b'q' | b'L' => IntKind::LongLong,
                    b't' => IntKind::PtrDiff,
                    b'z' => IntKind::Size,
                    _ => break,
                };

                c = next_byte(&mut format)?;
            }

            if c != b'n' {
                maybe_read!(noreset);
            }
            match c {
                b'%' => {
                    while (byte as char).is_whitespace() {
                        if !read!() {
                            return Ok(matched);
                        }
                    }

                    if byte != b'%' {
                        return Err(matched);
                    } else if !read!() {
                        return Ok(matched);
                    }
                }
                b'd' | b'i' | b'o' | b'u' | b'x' | b'X' | b'f' | b'e' | b'g' | b'E' | b'a'
                | b'p' => {
                    while (byte as char).is_whitespace() {
                        if !read!() {
                            return Ok(matched);
                        }
                    }

                    let pointer = c == b'p';
                    // Pointers aren't automatic, but we do want to parse "0x"
                    let auto = c == b'i' || pointer;
                    let float = c == b'f' || c == b'e' || c == b'g' || c == b'E' || c == b'a';

                    let mut radix = match c {
                        b'o' => 8,
                        b'x' | b'X' | b'p' => 16,
                        _ => 10,
                    };

                    let mut n = String::new();
                    let mut dot = false;

                    while width.map(|w| w > 0).unwrap_or(true)
                        && ((b'0'..=b'7').contains(&byte)
                            || (radix >= 10 && (b'8'..=b'9').contains(&byte))
                            || (float && !dot && byte == b'.')
                            || (radix == 16
                                && ((b'a'..=b'f').contains(&byte)
                                    || (b'A'..=b'F').contains(&byte))))
                    {
                        if auto
                            && n.is_empty()
                            && byte == b'0'
                            && width.map(|w| w > 0).unwrap_or(true)
                        {
                            if !pointer {
                                radix = 8;
                            }
                            width = width.map(|w| w - 1);
                            if !read!() {
                                return Ok(matched);
                            }
                            if width.map(|w| w > 0).unwrap_or(true)
                                && (byte == b'x' || byte == b'X')
                            {
                                radix = 16;
                                width = width.map(|w| w - 1);
                                if width.map(|w| w > 0).unwrap_or(true) && !read!() {
                                    return Ok(matched);
                                }
                            }
                            continue;
                        }
                        if byte == b'.' {
                            // Don't allow another dot
                            dot = true;
                        }
                        n.push(byte as char);
                        r.commit();
                        width = width.map(|w| w - 1);
                        if width.map(|w| w > 0).unwrap_or(true) && !read!() {
                            break;
                        }
                    }

                    macro_rules! parse_type {
                        (noformat $type:ident) => {{
                            let n = if n.is_empty() {
                                0 as $type
                            } else {
                                n.parse::<$type>().map_err(|_| 0)?
                            };
                            if !ignore {
                                *ap.arg::<*mut $type>() = n;
                                matched += 1;
                            }
                        }};
                        (c_double) => {
                            parse_type!(noformat c_double)
                        };
                        (c_float) => {
                            parse_type!(noformat c_float)
                        };
                        ($type:ident) => {
                            parse_type!($type, $type)
                        };
                        ($type:ident, $final:ty) => {{
                            let n = if n.is_empty() {
                                0 as $type
                            } else {
                                $type::from_str_radix(&n, radix).map_err(|_| 0)?
                            };
                            if !ignore {
                                *ap.arg::<*mut $final>() = n as $final;
                                matched += 1;
                            }
                        }};
                    }

                    if float {
                        if kind == IntKind::Long || kind == IntKind::LongLong {
                            parse_type!(c_double);
                        } else {
                            parse_type!(c_float);
                        }
                    } else if c == b'p' {
                        parse_type!(size_t, *mut c_void);
                    } else {
                        let unsigned = c == b'o' || c == b'u' || c == b'x' || c == b'X';

                        match kind {
                            IntKind::Byte => {
                                if unsigned {
                                    parse_type!(c_uchar);
                                } else {
                                    parse_type!(c_char);
                                }
                            }
                            IntKind::Short => {
                                if unsigned {
                                    parse_type!(c_ushort)
                                } else {
                                    parse_type!(c_short)
                                }
                            }
                            IntKind::Int => {
                                if unsigned {
                                    parse_type!(c_uint)
                                } else {
                                    parse_type!(c_int)
                                }
                            }
                            IntKind::Long => {
                                if unsigned {
                                    parse_type!(c_ulong)
                                } else {
                                    parse_type!(c_long)
                                }
                            }
                            IntKind::LongLong => {
                                if unsigned {
                                    parse_type!(c_ulonglong)
                                } else {
                                    parse_type!(c_longlong)
                                }
                            }
                            IntKind::IntMax => {
                                if unsigned {
                                    parse_type!(uintmax_t)
                                } else {
                                    parse_type!(intmax_t)
                                }
                            }
                            IntKind::PtrDiff => parse_type!(ptrdiff_t),
                            IntKind::Size => {
                                if unsigned {
                                    parse_type!(size_t)
                                } else {
                                    parse_type!(ssize_t)
                                }
                            }
                        }
                    }
                }
                b's' => {
                    while (byte as char).is_whitespace() {
                        if !read!() {
                            return Ok(matched);
                        }
                    }

                    let mut ptr: Option<*mut c_char> = if ignore { None } else { Some(ap.arg()) };

                    while width.map(|w| w > 0).unwrap_or(true) && !(byte as char).is_whitespace() {
                        if let Some(ref mut ptr) = ptr {
                            **ptr = byte as c_char;
                            *ptr = ptr.offset(1);
                        }
                        width = width.map(|w| w - 1);
                        if width.map(|w| w > 0).unwrap_or(true) && !read!() {
                            eof = true;
                            break;
                        }
                    }

                    if let Some(ptr) = ptr {
                        *ptr = 0;
                        matched += 1;
                        r.commit();
                    }
                }
                b'c' => {
                    let ptr: Option<*mut c_char> = if ignore { None } else { Some(ap.arg()) };

                    for i in 0..width.unwrap_or(1) {
                        if let Some(ptr) = ptr {
                            *ptr.add(i) = byte as c_char;
                        }
                        width = width.map(|w| w - 1);
                        if width.map(|w| w > 0).unwrap_or(true) && !read!() {
                            eof = true;
                            break;
                        }
                    }

                    if ptr.is_some() {
                        matched += 1;
                        r.commit();
                    }
                }
                b'[' => {
                    c = next_byte(&mut format)?;

                    let mut matches = Vec::new();
                    let invert = if c == b'^' {
                        c = next_byte(&mut format)?;
                        true
                    } else {
                        false
                    };

                    let mut prev;
                    loop {
                        matches.push(c);
                        prev = c;
                        c = next_byte(&mut format)?;
                        if c == b'-' {
                            if prev == b']' {
                                continue;
                            }
                            c = next_byte(&mut format)?;
                            if c == b']' {
                                matches.push(b'-');
                                break;
                            }
                            prev += 1;
                            while prev < c {
                                matches.push(prev);
                                prev += 1;
                            }
                        } else if c == b']' {
                            break;
                        }
                    }

                    let mut ptr: Option<*mut c_char> = if ignore { None } else { Some(ap.arg()) };

                    // While we haven't used up all the width, and it matches
                    let mut data_stored = false;
                    while width.map(|w| w > 0).unwrap_or(true) && invert != matches.contains(&byte)
                    {
                        if let Some(ref mut ptr) = ptr {
                            **ptr = byte as c_char;
                            *ptr = ptr.offset(1);
                            data_stored = true;
                        }
                        r.commit();
                        // Decrease the width, and read a new character unless the width is 0
                        width = width.map(|w| w - 1);
                        if width.map(|w| w > 0).unwrap_or(true) && !read!() {
                            // Reading a new character has failed, return after
                            // actually marking this as matched
                            eof = true;
                            break;
                        }
                    }

                    if data_stored {
                        *ptr.unwrap() = 0;
                        matched += 1;
                    }
                }
                b'n' => {
                    if !ignore {
                        *ap.arg::<*mut c_int>() = count as c_int;
                    }
                }
                _ => return Err(-1),
            }

            if eof {
                return Ok(matched);
            }

            if width != Some(0) && c != b'n' {
                // It didn't hit the width, so an extra character was read and matched.
                // But this character did not match so let's reuse it.
                skip_read = true;
            }
        }
    }
    Ok(matched)
}

pub unsafe fn scanf(r: LookAheadReader, format: *const c_char, ap: va_list) -> c_int {
    match inner_scanf(r, format, ap) {
        Ok(n) => n,
        Err(n) => n,
    }
}
