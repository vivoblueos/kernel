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

/// Enumeration of possible methods to seek within an I/O object. same as [`std::io::SeekFrom`].
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum SeekFrom {
    /// Sets the offset to the provided number of bytes. as SEEK_SET.
    Start(u64),
    /// Sets the offset to the size of this object plus the specified number of bytes. as SEEK_END.
    End(i64),
    /// Sets the offset to the current position plus the specified number of bytes. as SEEK_CUR.
    Current(i64),
}

/// Maximum bytes in a file name
pub const NAME_MAX: usize = 255;
