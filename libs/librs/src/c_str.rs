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

//! Nul-terminated byte strings.

use core::{ffi::c_char, marker::PhantomData, ptr::NonNull, str::Utf8Error};

use alloc::{borrow::Cow, string::String};

use crate::string::strlen;
/// C string wrapper, guaranteed to be
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct CStr<'a> {
    ptr: NonNull<c_char>,
    _marker: PhantomData<&'a [u8]>,
}

impl<'a> CStr<'a> {
    /// Safety
    ///
    /// The ptr must be valid up to and including the first NUL byte from the base ptr.
    pub const unsafe fn from_ptr(ptr: *const c_char) -> Self {
        Self {
            ptr: NonNull::new_unchecked(ptr as *mut c_char),
            _marker: PhantomData,
        }
    }
    pub unsafe fn from_nullable_ptr(ptr: *const c_char) -> Option<Self> {
        if ptr.is_null() {
            None
        } else {
            Some(Self::from_ptr(ptr))
        }
    }
    pub fn to_bytes_with_nul(self) -> &'a [u8] {
        // SAFETY: The string must be valid at least until (and including) the NUL byte.
        unsafe {
            let len = strlen(self.ptr.as_ptr());
            core::slice::from_raw_parts(self.ptr.as_ptr().cast(), len + 1)
        }
    }
    pub fn to_bytes(self) -> &'a [u8] {
        let s = self.to_bytes_with_nul();
        &s[..s.len() - 1]
    }
    pub fn to_str(self) -> Result<&'a str, Utf8Error> {
        core::str::from_utf8(self.to_bytes())
    }
    pub fn to_string_lossy(self) -> Cow<'a, str> {
        String::from_utf8_lossy(self.to_bytes())
    }
    pub const fn as_ptr(self) -> *const c_char {
        self.ptr.as_ptr()
    }
    pub const unsafe fn from_bytes_with_nul_unchecked(bytes: &'a [u8]) -> Self {
        Self::from_ptr(bytes.as_ptr().cast())
    }
    pub fn from_bytes_with_nul(bytes: &'a [u8]) -> Result<Self, FromBytesWithNulError> {
        if bytes.last() != Some(&b'\0') || bytes[..bytes.len() - 1].contains(&b'\0') {
            return Err(FromBytesWithNulError);
        }

        Ok(unsafe { Self::from_bytes_with_nul_unchecked(bytes) })
    }
    pub fn from_bytes_until_nul(bytes: &'a [u8]) -> Result<Self, FromBytesUntilNulError> {
        if !bytes.contains(&b'\0') {
            return Err(FromBytesUntilNulError);
        }

        Ok(unsafe { Self::from_bytes_with_nul_unchecked(bytes) })
    }
    pub fn to_owned_cstring(self) -> CString {
        CString::from(unsafe { core::ffi::CStr::from_ptr(self.ptr.as_ptr()) })
    }
    pub fn borrow(string: &'a CString) -> Self {
        unsafe { Self::from_ptr(string.as_ptr()) }
    }
}

unsafe impl Send for CStr<'_> {}
unsafe impl Sync for CStr<'_> {}

impl From<&core::ffi::CStr> for CStr<'_> {
    fn from(s: &core::ffi::CStr) -> Self {
        // SAFETY:
        // * We can assume that `s` is valid because the caller should have upheld its
        // safety concerns when constructing it.
        unsafe { Self::from_ptr(s.as_ptr()) }
    }
}

#[derive(Debug)]
pub struct FromBytesWithNulError;

#[derive(Debug)]
pub struct FromBytesUntilNulError;

pub use alloc::ffi::CString;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::println;
    use blueos_test_macro::test;

    #[test]
    fn test_from_ptr() {
        let s = b"hello\0";
        let cstr = unsafe { CStr::from_ptr(s.as_ptr() as *const c_char) };
        assert_eq!(cstr.to_str().unwrap(), "hello");
        assert_eq!(cstr.to_bytes(), b"hello");
        assert_eq!(cstr.to_bytes_with_nul(), b"hello\0");
        assert_eq!(cstr.to_owned_cstring().to_string_lossy(), "hello");
    }

    #[test]
    fn test_from_ptr_with_nul() {
        let s = b"hello world\0";
        let cstr = CStr::from_bytes_with_nul(s).unwrap();
        assert_eq!(cstr.to_str().unwrap(), "hello world");
        assert_eq!(cstr.to_bytes(), b"hello world");
        assert_eq!(cstr.to_bytes_with_nul(), b"hello world\0");
    }
}
