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
mod qemu_mps2_an385;
#[cfg(target_board = "qemu_mps2_an385")]
pub(crate) use qemu_mps2_an385::{get_cycles_to_duration, get_cycles_to_ms, get_early_uart, init};

#[cfg(target_board = "qemu_riscv64")]
mod qemu_riscv64;
#[cfg(target_board = "qemu_riscv64")]
pub(crate) use qemu_riscv64::{
    current_cycles, current_ticks, get_cycles_to_duration, get_cycles_to_ms, get_early_uart,
    handle_plic_irq, init, set_timeout_after,
};

#[cfg(target_board = "qemu_mps3_an547")]
mod qemu_mps3_an547;
#[cfg(target_board = "qemu_mps3_an547")]
pub(crate) use qemu_mps3_an547::{get_cycles_to_duration, get_cycles_to_ms, get_early_uart, init};

#[cfg(target_board = "qemu_virt64_aarch64")]
mod qemu_virt64_aarch64;
#[cfg(target_board = "qemu_virt64_aarch64")]
pub(crate) use qemu_virt64_aarch64::{
    get_cycles_to_duration, get_cycles_to_ms, get_early_uart, init,
};

#[cfg(target_board = "raspberry_pico2_cortexm")]
mod raspberry_pico2_cortexm;
#[cfg(target_board = "raspberry_pico2_cortexm")]
pub(crate) use raspberry_pico2_cortexm::{
    get_cycles_to_duration, get_cycles_to_ms, get_early_uart, init,
};
