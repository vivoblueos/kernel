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

// We use the term `cycles` to refer to the internal counter of the Clock. We
// use the term `hz` to descripe how many cycles within a second. Tick is
// defined as a short period of time, which is atomic in the system, just like
// the Planck time in physical world. We use `TICKS_PER_SECOND` to measure it.
// A clock instance should be able to interrupt the system.
pub trait Clock {
    fn hz() -> u64;
    // Reading the current counter of the Clock requires some time(Time
    // Drifting), we can only estimate it.
    fn estimate_current_cycles() -> u64;
    fn interrupt_at(moment: u64);
    fn stop();
}

#[cfg(target_arch = "aarch64")]
pub(crate) mod gic_generic_timer;
#[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
pub(crate) mod riscv_clock;
#[cfg(target_arch = "arm")]
pub(crate) mod systick;
