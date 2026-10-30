// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

//! Positional ELF reads supplied by a kernel or another artifact source.

use crate::LoadResult;

/// Read ELF contents independently of how they are stored or opened.
///
/// The image loader uses this contract to read headers at exact offsets.
/// Implementations can read an opened file, an in-memory slice or flash.
/// The length and contents must remain stable throughout one load attempt.
pub trait ElfReader {
    /// Return the source length in bytes.
    fn len(&self) -> LoadResult<u64>;

    #[inline]
    fn is_empty(&self) -> LoadResult<bool> {
        Ok(self.len()? == 0)
    }

    /// Fill `dst` from `offset`, returning an error if the full read fails.
    /// The caller must discard `dst` after an error; its contents are unspecified.
    fn read_exact_at(&self, offset: u64, dst: &mut [u8]) -> LoadResult<()>;
}
