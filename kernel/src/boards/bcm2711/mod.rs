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

pub mod init;
pub use init::*;
pub mod uart;
pub use uart::get_early_uart;
mod config;

use crate::arch::registers::cntfrq_el0::CNTFRQ_EL0;
use tock_registers::interfaces::Readable;
pub(crate) fn get_cycles_to_duration(cycles: u64) -> core::time::Duration {
    core::time::Duration::from_nanos(
        (cycles as f64 * (1_000_000_000f64 / CNTFRQ_EL0.get() as f64)) as u64,
    )
}

pub(crate) fn get_cycles_to_ms(cycles: u64) -> u64 {
    (cycles as f64 * (1_000f64 / CNTFRQ_EL0.get() as f64)) as u64
}
