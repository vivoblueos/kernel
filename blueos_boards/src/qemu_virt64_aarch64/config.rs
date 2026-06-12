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

// NOTE: This config file provides pure data for the board.
// Types like IrqNumber and mmu::kernel_phys_to_virt are defined
// in the kernel crate and are not available here. Use raw integer
// types instead.

pub const UART0_BASE_S: u64 = 0x59303000;
pub const APBP_CLOCK: u32 = 0x16e3600;
pub const PL011_UART0_BASE: u64 = 0x900_0000;
pub const PL011_UART0_IRQNUM: u32 = 33;
pub const GENERIC_TIMER_IRQNUM: u32 = 30;
pub const HEAP_SIZE: u64 = 16 * 1024 * 1024;
pub const PSCI_BASE: u32 = 0x84000000;
pub const GICD: u64 = 0x8000000;
pub const GICR: u64 = 0x80a0000;
pub const MMU_L1_NORMAL_BASES: &[u64] = &[0x4008_0000];
pub const MMU_L1_DEVICE_BASES: &[u64] = &[0x0];