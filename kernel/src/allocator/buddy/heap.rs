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

#[cfg(test)]
use crate::mm::kernel_phys_to_virt;
use crate::{mm::kernel_virt_to_phys, sync::spinlock::SpinLock};
use allocator_crate::buddy::{
    BuddyAllocator, BuddyInitError, BuddyMemoryInfo, PAGE_SHIFT, PAGE_SIZE,
};
use core::ptr::NonNull;

extern "C" {
    static mut _end: u8;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum BuddyLayoutError {
    InvalidPhysicalRange,
    AddressOverflow,
    MetadataOutsidePhysicalMemory,
    Allocator(BuddyInitError),
}

impl From<BuddyInitError> for BuddyLayoutError {
    fn from(value: BuddyInitError) -> Self {
        Self::Allocator(value)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct BuddyLayout {
    pub(super) metadata_virt_start: usize,
    pub(super) metadata_len: usize,
    pub(super) total_pages: usize,
    pub(super) managed_start_pfn: usize,
}

fn checked_align_up(value: usize, align: usize) -> Option<usize> {
    value.checked_add(align - 1).map(|v| v & !(align - 1))
}

// 四个参数：
// 1.物理地址起始位置
// 2.物理地址结束位置 
// 3.内核镜像末尾虚拟地址
// 4.虚拟地址转物理地址的函数
pub(super) fn plan_layout(
    phys_start: usize,
    phys_end: usize,
    kernel_end_virt: usize,
    mut virt_to_phys: impl FnMut(usize) -> usize,
) -> Result<BuddyLayout, BuddyLayoutError> {
    // 1. 检查物理地址是否规范，是否对 PAGE_SIZE 对齐
    if phys_start >= phys_end
        || phys_start & (PAGE_SIZE - 1) != 0
        || phys_end & (PAGE_SIZE - 1) != 0
    {
        return Err(BuddyLayoutError::InvalidPhysicalRange);
    }

    // 2. 计算整个物理内存区域有多少页
    let total_pages = (phys_end - phys_start) >> PAGE_SHIFT;
    let metadata_layout = BuddyAllocator::metadata_layout(total_pages)?;
    let metadata_virt_start =
        checked_align_up(kernel_end_virt, PAGE_SIZE).ok_or(BuddyLayoutError::AddressOverflow)?;
    let metadata_data_end = metadata_virt_start
        .checked_add(metadata_layout.size())
        .ok_or(BuddyLayoutError::AddressOverflow)?;
    let metadata_reserved_end =
        checked_align_up(metadata_data_end, PAGE_SIZE).ok_or(BuddyLayoutError::AddressOverflow)?;

    let metadata_phys_start = virt_to_phys(metadata_virt_start);
    let metadata_phys_end = virt_to_phys(metadata_reserved_end);
    if metadata_phys_start < phys_start
        || metadata_phys_start >= phys_end
        || metadata_phys_end <= metadata_phys_start
        || metadata_phys_end > phys_end
    {
        return Err(BuddyLayoutError::MetadataOutsidePhysicalMemory);
    }

    Ok(BuddyLayout {
        metadata_virt_start,
        metadata_len: metadata_layout.size(),
        total_pages,
        managed_start_pfn: (metadata_phys_end - phys_start) >> PAGE_SHIFT,
    })
}

struct BuddyState {
    allocator: BuddyAllocator,
    phys_base: usize,
    total_pages: usize,
    initialized: bool,
}

impl BuddyState {
    const fn new() -> Self {
        Self {
            allocator: BuddyAllocator::new(),
            phys_base: 0,
            total_pages: 0,
            initialized: false,
        }
    }

    fn pfn_to_phys(&self, pfn: usize) -> Option<usize> {
        if !self.initialized || pfn >= self.total_pages {
            return None;
        }
        pfn.checked_shl(PAGE_SHIFT as u32)
            .and_then(|offset| self.phys_base.checked_add(offset))
    }

    fn phys_to_pfn(&self, phys_addr: usize) -> Option<usize> {
        if !self.initialized || phys_addr & (PAGE_SIZE - 1) != 0 {
            return None;
        }
        let offset = phys_addr.checked_sub(self.phys_base)?;
        let pfn = offset >> PAGE_SHIFT;
        (pfn < self.total_pages).then_some(pfn)
    }
}

/// Kernel synchronization and physical-address wrapper for the raw buddy.
pub(in crate::allocator) struct BuddyHeap {
    inner: SpinLock<BuddyState>,
}

impl BuddyHeap {
    pub(in crate::allocator) const fn new() -> Self {
        Self {
            inner: SpinLock::new(BuddyState::new()),
        }
    }

    /// Initialize the global physical page allocator.
    ///
    /// # Safety
    ///
    /// `phys_start..phys_end` must be valid writable DRAM, must contain the
    /// kernel image and metadata selected from `_end`, and must remain owned by
    /// the allocator for the rest of the boot.
    pub(in crate::allocator) unsafe fn init(&self, phys_start: usize, phys_end: usize) {
        let layout = plan_layout(
            phys_start,
            phys_end,
            core::ptr::addr_of_mut!(_end) as usize,
            kernel_virt_to_phys,
        )
        .expect("invalid kernel buddy metadata layout");
        let metadata = NonNull::new(layout.metadata_virt_start as *mut u8)
            .expect("buddy metadata pointer must not be null");
        {
            let mut state = self.inner.irqsave_lock();
            state.allocator.init(
                metadata,
                layout.metadata_len,
                layout.total_pages,
                layout.managed_start_pfn..layout.total_pages,
            )
            .expect("failed to initialize raw buddy allocator");
            state.phys_base = phys_start;
            state.total_pages = layout.total_pages;
            state.initialized = true;
        }
    }

    pub(in crate::allocator) fn alloc_pages_phys_addr(&self, order: usize) -> Option<usize> {
        let mut state = self.inner.irqsave_lock();
        let frame = state.allocator.alloc_pages(order)?;
        state.pfn_to_phys(frame.pfn())
    }

    #[allow(dead_code)]
    pub(in crate::allocator) fn alloc_pages_aligned_phys_addr(
        &self,
        order: usize,
        align_order: usize,
    ) -> Option<usize> {
        let mut state = self.inner.irqsave_lock();
        let frame = state.allocator.alloc_pages_aligned(order, align_order)?;
        state.pfn_to_phys(frame.pfn())
    }

    /// Release a physical block returned by [`Self::alloc_pages_phys_addr`].
    ///
    /// # Safety
    ///
    /// `phys_addr` must be the address of a live block from this heap, `order`
    /// must match its allocation order, and the block must be released once.
    pub(in crate::allocator) unsafe fn free_pages_phys_addr(&self, phys_addr: usize, order: usize) {
        let mut state = self.inner.irqsave_lock();
        let pfn = state
            .phys_to_pfn(phys_addr)
            .expect("invalid physical address passed to buddy free");
        state.allocator.free_pages_pfn(pfn, order);
    }

    #[allow(dead_code)]
    pub(in crate::allocator) fn memory_info(&self) -> BuddyMemoryInfo {
        self.inner.irqsave_lock().allocator.memory_info()
    }

    #[cfg(test)]
    pub(super) unsafe fn init_for_test(
        &self,
        phys_base: usize,
        total_pages: usize,
        managed_start_pfn: usize,
        metadata: NonNull<u8>,
        metadata_len: usize,
    ) -> Result<(), BuddyInitError> {
        let mut state = self.inner.irqsave_lock();
        state.allocator.init(
            metadata,
            metadata_len,
            total_pages,
            managed_start_pfn..total_pages,
        )?;
        state.phys_base = phys_base;
        state.total_pages = total_pages;
        state.initialized = true;
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn phys_addr_to_pfn_for_test(&self, phys_addr: usize) -> Option<usize> {
        self.inner.irqsave_lock().phys_to_pfn(phys_addr)
    }

    #[cfg(test)]
    pub(super) fn phys_addr_to_virt_for_test(&self, phys_addr: usize) -> usize {
        kernel_phys_to_virt(phys_addr)
    }
}
