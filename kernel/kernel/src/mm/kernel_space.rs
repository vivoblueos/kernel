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

//! The kernel shared virtual address space and permanent page tables.

use super::{
    address_space::Vma,
    kernel_phys_to_virt,
    memory_bank::MemoryRegion,
    paging::{first_fit::FirstFitFrameAllocator, mapper::PageMapper, PageFormat},
    MemAttribute, MemFlags, MemType, PhysicalAddress,
};
use crate::{arch::page::PageEntry, sync::SpinLock};
use spin::Once;

// Disjoint image, boot-data, available RAM and MMIO regions prepared at boot.
const REGION_COUNT: usize = 12 + 4 * crate::boards::MEMORY_BANKS.len();

pub const HEAP_START: usize =
    crate::mm::KERNEL_VIRT_OFFSET + (1usize << (PageEntry::VIRT_ADDR_BITS - 1));
pub const HEAP_END: usize = HEAP_START + (1usize << (PageEntry::VIRT_ADDR_BITS - 2));
const _: () = assert!(allocator_crate::page_heap::PAGE_SIZE == PageEntry::PAGE_SIZE);

static KERNEL_SPACE: Once<KernelAddressSpace> = Once::new();

#[must_use]
pub struct KernelAddressSpace {
    regions: [Option<Vma>; REGION_COUNT],
    mapper: SpinLock<PageMapper<&'static FirstFitFrameAllocator, PageEntry>>,
}

impl KernelAddressSpace {
    pub fn get() -> Option<&'static Self> {
        KERNEL_SPACE.get()
    }

    pub fn root_address(&self) -> PhysicalAddress {
        self.mapper.irqsave_lock().root_address()
    }

    #[cfg(test)]
    pub(crate) fn leaf_descriptor(&self, addr: usize) -> Option<usize> {
        self.find_region(addr)?;
        self.mapper.irqsave_lock().leaf_descriptor(addr)
    }

    pub fn find_region(&self, addr: usize) -> Option<Vma> {
        if (HEAP_START..HEAP_END).contains(&addr) {
            return Vma::new(HEAP_START, HEAP_END, MemFlags::READ | MemFlags::WRITE).ok();
        }
        self.regions
            .iter()
            .flatten()
            .find(|region| region.contains(addr))
            .copied()
    }

    pub fn translate(&self, addr: usize) -> Option<PhysicalAddress> {
        // A root-table walk alone cannot distinguish the TTBR0 and TTBR1
        // halves. Only static regions or the reserved heap window are valid.
        self.find_region(addr)?;
        self.mapper.irqsave_lock().translate(addr)
    }

    pub(crate) fn map_heap(&self, start: usize, pages: usize) -> Result<(), &'static str> {
        let len = pages
            .checked_mul(PageEntry::PAGE_SIZE)
            .ok_or("heap size overflow")?;
        let end = start.checked_add(len).ok_or("heap end overflow")?;
        if pages == 0 || start < HEAP_START || end > HEAP_END {
            return Err("outside heap window");
        }
        // SAFETY: page source exclusively reserves this unmapped VA interval.
        unsafe {
            self.mapper
                .irqsave_lock()
                .map_owned_range(super::VirtualAddress::new(start), len)
        }
    }

    /// # Safety
    /// Caller has stopped all users and exclusively owns this heap reservation.
    pub(crate) unsafe fn release_heap(&self, start: usize, pages: usize) {
        let len = pages.checked_mul(PageEntry::PAGE_SIZE).expect("heap size");
        assert!(start >= HEAP_START && start.checked_add(len).is_some_and(|end| end <= HEAP_END));
        self.mapper
            .irqsave_lock()
            .release_owned_range(super::VirtualAddress::new(start), len);
    }

    /// Map a physical memory region to the kernel virtual address space.
    /// The physical address will be added a KERNEL_OFFSET
    fn map_linear(
        &mut self,
        start: PhysicalAddress,
        end: PhysicalAddress,
        flags: MemFlags,
        memory_type: MemType,
    ) -> Result<(), &'static str> {
        if start == end {
            return Ok(());
        }
        let len = end
            .into_raw()
            .checked_sub(start.into_raw())
            .ok_or("reversed kernel mapping")?;
        let virt = kernel_phys_to_virt(start);
        let virt_end = virt
            .into_raw()
            .checked_add(len)
            .ok_or("kernel mapping overflow")?;
        self.mapper.irqsave_lock().map_range(
            virt,
            start,
            len,
            MemAttribute {
                flags: flags | MemFlags::GLOBAL,
                memory_type,
            },
        )?;
        let vma_flags = MemFlags::READ | flags;
        self.record_region(virt.into_raw(), virt_end, vma_flags)
    }

    fn record_region(
        &mut self,
        start: usize,
        end: usize,
        flags: MemFlags,
    ) -> Result<(), &'static str> {
        if self
            .regions
            .iter()
            .flatten()
            .any(|region| start < region.end() && region.start() < end)
        {
            return Err("overlapping kernel address-space regions");
        }
        let region = Vma::new(start, end, flags).map_err(|_| "invalid kernel region")?;
        let slot = self
            .regions
            .iter_mut()
            .find(|region| region.is_none())
            .ok_or("kernel region table is full")?;
        *slot = Some(region);
        Ok(())
    }
}

pub(crate) fn init_kernel_space(regions: &[MemoryRegion]) -> Result<(), &'static str> {
    KERNEL_SPACE.try_call_once(|| {
        let allocator = FirstFitFrameAllocator::instance();
        // SAFETY: boot initialized the physical allocator and the boot direct
        // map. New table frames are disjoint from the reserved kernel image,
        // and these tables are retained permanently by KERNEL_SPACE.
        let mapper = unsafe { PageMapper::create(allocator)? };
        let mut space = KernelAddressSpace {
            regions: [None; REGION_COUNT],
            mapper: SpinLock::new(mapper),
        };
        for region in regions {
            let end = region
                .base
                .into_raw()
                .checked_add(region.size)
                .ok_or("kernel region overflow")?;
            space.map_linear(
                region.base,
                PhysicalAddress::new(end),
                region.flags,
                region.memory_type,
            )?;
        }
        // Retain the completed tables permanently before publishing them for
        // activation by each CPU during board initialization.
        space.mapper.irqsave_lock().retain_tables();
        Ok(space)
    })?;
    Ok(())
}

#[cfg(all(test, smp))]
mod tests {
    use super::*;
    use crate::allocator::page_heap::source::{PageSource, VmapSource};
    use alloc::sync::Arc;
    use blueos_test_macro::test;
    use core::sync::atomic::{AtomicUsize, Ordering};

    fn wait(phase: &AtomicUsize, expected: usize) {
        let deadline = crate::time::Tick::after(crate::time::Tick::from_millis(5000));
        while phase.load(Ordering::Acquire) != expected {
            assert!(!deadline.is_elapsed(), "cross-CPU mapping test timed out");
            crate::scheduler::yield_me();
        }
    }

    #[test]
    fn remapped_heap_address_discards_other_cpu_translations() {
        let phase = Arc::new(AtomicUsize::new(0));
        let address = Arc::new(AtomicUsize::new(0));
        let worker_phase = phase.clone();
        let worker_address = address.clone();
        let original_cpu = crate::arch::current_cpu_id();
        let _worker = crate::thread::spawn(move || {
            // Warm this address on a different CPU before each replacement.
            let deadline = crate::time::Tick::after(crate::time::Tick::from_millis(5000));
            while crate::arch::current_cpu_id() == original_cpu {
                assert!(!deadline.is_elapsed(), "no second CPU for mapping test");
                crate::scheduler::yield_me();
            }
            for iteration in 0..16 {
                wait(&worker_phase, 4 * iteration + 1);
                let ptr = worker_address.load(Ordering::Acquire) as *const u8;
                assert_eq!(unsafe { ptr.read_volatile() }, 0x2a);
                worker_phase.store(4 * iteration + 2, Ordering::Release);
                wait(&worker_phase, 4 * iteration + 3);
                assert_eq!(unsafe { ptr.read_volatile() }, 0x73);
                worker_phase.store(4 * iteration + 4, Ordering::Release);
            }
        })
        .unwrap();
        let source = VmapSource;
        let span = source
            .allocate(allocator_crate::page_heap::PageRequest {
                pages: 1,
                align: PageEntry::PAGE_SIZE,
            })
            .unwrap();
        let start = span.start().as_ptr() as usize;
        address.store(start, Ordering::Release);
        let space = KernelAddressSpace::get().unwrap();
        for iteration in 0..16 {
            unsafe { span.start().as_ptr().write_volatile(0x2a) };
            phase.store(4 * iteration + 1, Ordering::Release);
            wait(&phase, 4 * iteration + 2);
            let old = space.translate(start).unwrap();
            let replacement = FirstFitFrameAllocator::instance().alloc_frame().unwrap();
            assert_ne!(old, replacement);
            unsafe { space.release_heap(start, 1) };
            space
                .mapper
                .irqsave_lock()
                .map_range(
                    super::super::VirtualAddress::new(start),
                    replacement,
                    PageEntry::PAGE_SIZE,
                    MemAttribute {
                        flags: MemFlags::READ | MemFlags::WRITE | MemFlags::GLOBAL,
                        memory_type: MemType::Normal(super::super::CachePolicy::WriteBack),
                    },
                )
                .unwrap();
            crate::arch::mmu::sync_kernel_mappings();
            unsafe { span.start().as_ptr().write_volatile(0x73) };
            phase.store(4 * iteration + 3, Ordering::Release);
            wait(&phase, 4 * iteration + 4);
        }
        unsafe { source.release(span) };
        assert!(space.translate(start).is_none());
    }
}
