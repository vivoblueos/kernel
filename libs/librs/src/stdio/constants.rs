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

use libc::c_int;

pub const EOF: c_int = -1;
pub const BUFSIZ: c_int = 1024;
pub const UNGET: c_int = 8;

pub const FILENAME_MAX: c_int = 4096;

// same with newlib header
pub const F_PERM: c_int = 1;
pub const F_NORD: c_int = 4;
pub const F_NOWR: c_int = 8;
pub const F_EOF: c_int = 16;
pub const F_ERR: c_int = 32;
pub const F_SVB: c_int = 64;
pub const F_APP: c_int = 128;
pub const F_BADJ: c_int = 256;

pub const _IOFBF: c_int = 0;
pub const _IOLBF: c_int = 1;
pub const _IONBF: c_int = 2;
