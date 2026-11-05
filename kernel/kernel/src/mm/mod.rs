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

pub mod address_space;

#[repr(transparent)]
pub struct PhysicalAddress(usize);

impl PhysicalAddress {
    pub const fn new(addr: usize) -> Self {
        // FIXME: check if addr is valid physical address
        PhysicalAddress(addr)
    }

    pub const fn into_raw(self) -> usize {
        self.0
    }
}

#[repr(transparent)]
pub struct VirtualAddress(usize);

impl VirtualAddress {
    pub const fn new(addr: usize) -> Self {
        // FIXME: check if addr is valid virtual address
        VirtualAddress(addr)
    }

    pub const fn into_raw(self) -> usize {
        self.0
    }
}

pub const KERNEL_VIRT_OFFSET: usize = blueos_kconfig::CONFIG_KERNEL_VIRT_OFFSET as usize;

#[inline]
pub const fn kernel_phys_to_virt(addr: PhysicalAddress) -> VirtualAddress {
    debug_assert!(addr.0.checked_add(KERNEL_VIRT_OFFSET).is_some());
    VirtualAddress(addr.0 + KERNEL_VIRT_OFFSET)
}

#[inline]
pub const fn kernel_virt_to_phys(addr: VirtualAddress) -> PhysicalAddress {
    debug_assert!(addr.0.checked_sub(KERNEL_VIRT_OFFSET).is_some());
    PhysicalAddress(addr.0 - KERNEL_VIRT_OFFSET)
}
