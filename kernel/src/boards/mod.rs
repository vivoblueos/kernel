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

#[cfg(target_board = "qemu_mps2_an385")]
pub mod qemu_mps2_an385;
#[cfg(target_board = "qemu_mps2_an385")]
pub(crate) use qemu_mps2_an385::{clock_cycles_to_millis, get_early_uart, init};

#[cfg(target_board = "qemu_riscv64")]
mod qemu_riscv64;
#[cfg(target_board = "qemu_riscv64")]
pub(crate) use qemu_riscv64::{
    clock_cycles_to_millis, current_clock_cycles, get_early_uart, handle_irq, init,
    set_timeout_after_nanos,
};

#[cfg(target_board = "qemu_mps3_an547")]
mod qemu_mps3_an547;
#[cfg(target_board = "qemu_mps3_an547")]
pub(crate) use qemu_mps3_an547::{clock_cycles_to_millis, get_early_uart, init};

#[cfg(target_board = "qemu_virt64_aarch64")]
mod qemu_virt64_aarch64;
#[cfg(target_board = "qemu_virt64_aarch64")]
pub(crate) use qemu_virt64_aarch64::{clock_cycles_to_millis, get_early_uart, init};

#[cfg(target_board = "raspberry_pico2_cortexm")]
mod raspberry_pico2_cortexm;
#[cfg(target_board = "raspberry_pico2_cortexm")]
pub(crate) use raspberry_pico2_cortexm::{
    get_cycles_to_duration, get_cycles_to_ms, get_early_uart, init,
};

#[inline]
pub fn clock_cycles_to_duration(cycles: u64) -> core::time::Duration {
    core::time::Duration::from_millis(clock_cycles_to_millis(cycles))
}

// Boards should implement this method to provide accurate information.
#[inline]
pub(crate) fn uptime() -> core::time::Duration {
    core::time::Duration::from_millis(0)
}
