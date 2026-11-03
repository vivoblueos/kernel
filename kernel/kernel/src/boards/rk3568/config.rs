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

use crate::{
    arch::irq::IrqNumber,
    mm::{kernel_phys_to_virt, memory_bank::MemoryBank, PhysicalAddress},
};

pub const APBP_CLOCK: u32 = 0x16e3600;
pub const CONSOLE_UART_BASE: u64 =
    kernel_phys_to_virt(PhysicalAddress::new(0xFE660000)).into_raw() as u64;
pub const CONSOLE_UART_IRQNUM: IrqNumber = IrqNumber::new(150);
pub const GENERIC_TIMER_IRQNUM: IrqNumber = IrqNumber::new(30);
pub const HEAP_SIZE: u64 = 16 * 1024 * 1024;
pub const PSCI_BASE: u32 = 0x84000000;
pub const GICD: usize = kernel_phys_to_virt(PhysicalAddress::new(0xfd400000)).into_raw();
pub const GICR: usize = kernel_phys_to_virt(PhysicalAddress::new(0xfd460000)).into_raw();

// Physical memory range for buddy allocator (according to uboot bdinfo message).
pub const PHYS_DRAM_BASE: usize = 0x20_0000;
pub const PHYS_DRAM_SIZE: usize = 0xefe0_0000;

// Offset from the 2MiB-aligned base, published in the arm64 Image header.
pub const TEXT_OFFSET: usize = blueos_kconfig::CONFIG_KERNEL_PHYS_BASE as usize % (2 * 1024 * 1024);

// FIXME: Parse the memory banks from the device tree or firmware memory map.
// Keep MMIO last so device attributes take precedence in shared bootstrap blocks.
pub const MEMORY_BANKS: &[MemoryBank] = &[
    MemoryBank::RAM((
        PhysicalAddress::new(PHYS_DRAM_BASE),
        PhysicalAddress::new(PHYS_DRAM_BASE + PHYS_DRAM_SIZE),
    )),
    MemoryBank::MMIO((
        PhysicalAddress::new(0xfd40_0000),
        PhysicalAddress::new(0xfd41_0000),
    )),
    MemoryBank::MMIO((
        PhysicalAddress::new(0xfd46_0000),
        PhysicalAddress::new(0xfd46_0000 + blueos_kconfig::CONFIG_NUM_CORES as usize * 0x2_0000),
    )),
    MemoryBank::MMIO((
        PhysicalAddress::new(0xfe66_0000),
        PhysicalAddress::new(0xfe66_1000),
    )),
];
