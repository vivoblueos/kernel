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

mod a64_4k;

#[cfg(aarch64_va_bits_39)]
mod a64_4k_39;
#[cfg(aarch64_va_bits_39)]
pub use a64_4k_39::{PageEntry, PAGE_FORMAT};

#[cfg(aarch64_va_bits_48)]
mod a64_4k_48;
#[cfg(aarch64_va_bits_48)]
pub use a64_4k_48::{PageEntry, PAGE_FORMAT};
