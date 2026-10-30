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

#[cfg(cortex_m)]
mod cortex_m;
#[cfg(cortex_m)]
pub use cortex_m::{syscall0, syscall1, syscall2, syscall3, syscall4, syscall5, syscall6};
#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::{syscall0, syscall1, syscall2, syscall3, syscall4, syscall5, syscall6};
#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
mod riscv;
#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
pub use riscv::{syscall0, syscall1, syscall2, syscall3, syscall4, syscall5, syscall6};
