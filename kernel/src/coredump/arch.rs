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

//! Architecture dispatch for coredump register capture.
//!
//! Each arch module provides:
//!   - `capture_regs(ctx: &arch::Context) -> [u8; N]`
//!   - `capture_current_regs() -> [u8; N]`

#[cfg(target_arch = "arm")]
mod arm;
#[cfg(target_arch = "arm")]
pub use arm::*;

#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::*;

#[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
mod riscv;
#[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
pub use riscv::*;

/// Return the register dump size in bytes for the current architecture.
#[inline]
pub fn regset_size() -> usize {
    capture_current_regs().len()
}
