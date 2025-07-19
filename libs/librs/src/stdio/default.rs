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

use super::{constants, helpers::File, Buffer, BUFSIZ, FILE};
use crate::{
    io::LineWriter,
    sync::{once::Once, GenericMutex},
};
use alloc::{boxed::Box, vec::Vec};
use core::{cell::UnsafeCell, ptr};
use libc::c_int;

pub struct GlobalFile(UnsafeCell<FILE>);

impl GlobalFile {
    fn new(file: c_int, flags: c_int) -> Self {
        let file = File::new(file);
        let writer = Box::new(LineWriter::new(unsafe { file.get_ref() }));
        GlobalFile(UnsafeCell::new(FILE {
            lock: GenericMutex::new(()),
            file,
            flags: constants::F_PERM | flags,
            read_buf: Buffer::Owned(vec![0; BUFSIZ as usize]),
            read_pos: 0,
            read_size: 0,
            unget: Vec::new(),
            writer,
            orientation: 0,
        }))
    }
    pub fn get(&self) -> *mut FILE {
        self.0.get()
    }
}
// statics need to be Sync
unsafe impl Sync for GlobalFile {}

static DEFAULT_STDIN: Once<GlobalFile> = Once::new();
static DEFAULT_STDOUT: Once<GlobalFile> = Once::new();
static DEFAULT_STDERR: Once<GlobalFile> = Once::new();

pub fn default_stdin() -> &'static GlobalFile {
    DEFAULT_STDIN.call_once(|| GlobalFile::new(0, constants::F_NOWR))
}
pub fn default_stdout() -> &'static GlobalFile {
    DEFAULT_STDOUT.call_once(|| GlobalFile::new(1, constants::F_NORD))
}
pub fn default_stderr() -> &'static GlobalFile {
    DEFAULT_STDERR.call_once(|| GlobalFile::new(2, constants::F_NORD))
}

#[no_mangle]
pub static mut stdin: *mut FILE = ptr::null_mut();
#[no_mangle]
pub static mut stdout: *mut FILE = ptr::null_mut();
#[no_mangle]
pub static mut stderr: *mut FILE = ptr::null_mut();
