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

use super::{fseek_locked, ftell_locked, FILE};
use crate::io::Read;
use libc::{off_t, SEEK_SET};
struct LookAheadBuffer {
    buf: *const u8,
    pos: isize,
    look_ahead: isize,
}
impl LookAheadBuffer {
    fn look_ahead(&mut self) -> Result<Option<u8>, i32> {
        let byte = unsafe { *self.buf.offset(self.look_ahead) };
        if byte == 0 {
            Ok(None)
        } else {
            self.look_ahead += 1;
            Ok(Some(byte))
        }
    }

    fn commit(&mut self) {
        self.pos = self.look_ahead;
    }
}

impl From<*const u8> for LookAheadBuffer {
    fn from(buff: *const u8) -> LookAheadBuffer {
        LookAheadBuffer {
            buf: buff,
            pos: 0,
            look_ahead: 0,
        }
    }
}

struct LookAheadFile<'a> {
    f: &'a mut FILE,
    look_ahead: i64,
}

impl LookAheadFile<'_> {
    fn look_ahead(&mut self) -> Result<Option<u8>, i32> {
        let buf = &mut [0];
        let seek = unsafe { ftell_locked(self.f) };
        unsafe { fseek_locked(self.f, self.look_ahead as off_t, SEEK_SET) };
        let ret = match self.f.read(buf) {
            Ok(0) => Ok(None),
            Ok(_) => Ok(Some(buf[0])),
            Err(_) => Err(-1),
        };
        unsafe { fseek_locked(self.f, seek, SEEK_SET) };
        self.look_ahead += 1;
        ret
    }

    fn commit(&mut self) {
        unsafe { fseek_locked(self.f, self.look_ahead as off_t, SEEK_SET) };
    }
}

impl<'a> From<&'a mut FILE> for LookAheadFile<'a> {
    fn from(f: &'a mut FILE) -> LookAheadFile<'a> {
        let look_ahead = unsafe { ftell_locked(f) } as i64;
        LookAheadFile { f, look_ahead }
    }
}

enum LookAheadReaderEnum<'a> {
    File(LookAheadFile<'a>),
    // (buffer, location)
    Buffer(LookAheadBuffer),
}

pub struct LookAheadReader<'a>(LookAheadReaderEnum<'a>);

impl LookAheadReader<'_> {
    pub fn lookahead1(&mut self) -> Result<Option<u8>, i32> {
        match &mut self.0 {
            LookAheadReaderEnum::File(f) => f.look_ahead(),
            LookAheadReaderEnum::Buffer(b) => b.look_ahead(),
        }
    }
    pub fn commit(&mut self) {
        match &mut self.0 {
            LookAheadReaderEnum::File(f) => f.commit(),
            LookAheadReaderEnum::Buffer(b) => b.commit(),
        }
    }
}

impl<'a> From<&'a mut FILE> for LookAheadReader<'a> {
    fn from(f: &'a mut FILE) -> LookAheadReader<'a> {
        LookAheadReader(LookAheadReaderEnum::File(f.into()))
    }
}

impl<'a> From<*const u8> for LookAheadReader<'a> {
    fn from(buff: *const u8) -> LookAheadReader<'a> {
        LookAheadReader(LookAheadReaderEnum::Buffer(buff.into()))
    }
}
