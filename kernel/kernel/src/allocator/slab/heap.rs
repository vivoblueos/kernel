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

use crate::sync::spinlock::SpinLock;
use allocator_crate::{slab::SlabHeap as Slab, MemoryInfo};
use core::{alloc::Layout, ptr::NonNull};

pub type Heap = SlabHeap<2, 4, 2, 1, 1, 1, 1, 1, 1, 1>;
pub struct SlabHeap<
    const S8: usize,
    const S16: usize,
    const S32: usize,
    const S64: usize,
    const S96: usize,
    const S128: usize,
    const S192: usize,
    const S256: usize,
    const S512: usize,
    const S1024: usize,
> {
    heap: SpinLock<Slab<S8, S16, S32, S64, S96, S128, S192, S256, S512, S1024>>,
}

impl<
        const S8: usize,
        const S16: usize,
        const S32: usize,
        const S64: usize,
        const S96: usize,
        const S128: usize,
        const S192: usize,
        const S256: usize,
        const S512: usize,
        const S1024: usize,
    > SlabHeap<S8, S16, S32, S64, S96, S128, S192, S256, S512, S1024>
{
    // Create a new UNINITIALIZED heap allocator
    pub const fn new() -> Self {
        SlabHeap {
            heap: SpinLock::new(
                Slab::<S8, S16, S32, S64, S96, S128, S192, S256, S512, S1024>::new(),
            ),
        }
    }

    // Initializes the heap
    // Safety: the memory start address and size must be valid.
    pub unsafe fn init(&self, start_addr: usize, size: usize) {
        let mut heap = self.heap.irqsave_lock();
        heap.init(start_addr, size);
    }

    // try to allocate memory with the given layout
    pub fn alloc(&self, layout: Layout) -> Option<NonNull<u8>> {
        let mut heap = self.heap.irqsave_lock();
        heap.allocate(&layout)
    }

    // deallocate the memory pointed by ptr with the given layout
    // Safety: the ptr must be a valid pointer.
    pub unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let mut heap = self.heap.irqsave_lock();
        heap.deallocate(NonNull::new_unchecked(ptr), &layout);
    }

    // deallocate the memory pointed by ptr with out align
    // Safety: the ptr must be a valid pointer.
    pub unsafe fn deallocate_unknown_align(&self, ptr: *mut u8) {
        let mut heap = self.heap.irqsave_lock();
        heap.deallocate_unknown_align(NonNull::new_unchecked(ptr));
    }

    // reallocate memory with the given size and layout
    // Safety: the ptr must be a valid pointer.
    pub unsafe fn realloc(
        &self,
        ptr: *mut u8,
        layout: Layout,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let new_layout = Layout::from_size_align(new_size, layout.align()).ok()?;
        let mut heap = self.heap.irqsave_lock();
        heap.reallocate(NonNull::new_unchecked(ptr), &new_layout)
    }

    // reallocate memory with the given size but with out align
    // Safety: the ptr must be a valid pointer.
    pub unsafe fn realloc_unknown_align(
        &self,
        ptr: *mut u8,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let mut heap = self.heap.irqsave_lock();
        heap.reallocate_unknown_align(NonNull::new_unchecked(ptr), new_size)
    }

    // Retrieves various statistics about the current state of the heap's memory usage.
    pub fn memory_info(&self) -> MemoryInfo {
        let heap = self.heap.irqsave_lock();
        MemoryInfo {
            total: heap.total(),
            used: heap.allocated(),
            max_used: heap.maximum(),
        }
    }

    pub fn sys_memory_info(&self) -> MemoryInfo {
        let heap = self.heap.irqsave_lock();
        MemoryInfo {
            total: heap.total() - heap.slab_total_size,
            used: heap.system_allocator.allocated() - heap.slab_total_size,
            max_used: heap.system_allocator.maximum() - heap.slab_total_size,
        }
    }

    pub fn slab_memory_info(&self) -> MemoryInfo {
        let heap = self.heap.irqsave_lock();
        MemoryInfo {
            total: heap.slab_total_size,
            used: heap.allocated() + heap.slab_total_size - heap.system_allocator.allocated(),
            max_used: heap.maximum() + heap.slab_total_size - heap.system_allocator.maximum(),
        }
    }

    pub fn print_slab_stat(&self) {
        // Static slab doesn't support detailed stats, just print basic info
        let (total, used);
        {
            let heap = self.heap.irqsave_lock();
            total = heap.total();
            used = heap.allocated();
        }
        crate::kprintln!("Slab: total={} used={}", total, used);
    }

    pub fn size_of_allocation(&self, ptr: NonNull<u8>) -> usize {
        let mut heap = self.heap.irqsave_lock();
        heap.size_of_allocation(ptr).unwrap_or(0)
    }

    pub fn get_max_free_block_size(&self) -> usize {
        let heap = self.heap.irqsave_lock();
        heap.get_max_free_block_size()
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// DynamicSlabHeap — SpinLock wrapper (mirrors SlabHeap pattern above)
// ═══════════════════════════════════════════════════════════════════════════

#[cfg(allocator = "slab_dynamic")]
use allocator_crate::slab::{DynamicSlabHeap as RawDynHeap, DynamicSlabSystemAllocator};

#[cfg(all(allocator = "slab_dynamic", allocator_buddy))]
use crate::{
    allocator::BUDDY_ALLOC,
    mm::{kernel_phys_to_virt, kernel_virt_to_phys, PhysicalAddress, VirtualAddress},
};

#[cfg(all(allocator = "slab_dynamic", allocator_buddy))]
struct BuddySystemAllocator;

#[cfg(all(allocator = "slab_dynamic", allocator_buddy))]
impl DynamicSlabSystemAllocator for BuddySystemAllocator {
    unsafe fn init(&mut self, _start: usize, _size: usize) {
        // The kernel initializes BUDDY_ALLOC before initializing dynslab.
    }

    fn allocate(&mut self, layout: &Layout) -> Option<NonNull<u8>> {
        let order = allocator_crate::buddy::order_of_size(layout.size().max(layout.align()));
        BUDDY_ALLOC.alloc_pages_phys_addr(order).map(|addr| unsafe {
            NonNull::new_unchecked(
                kernel_phys_to_virt(PhysicalAddress::new(addr)).into_raw() as *mut u8
            )
        })
    }

    unsafe fn deallocate(&mut self, ptr: NonNull<u8>) -> usize {
        let phys_addr = kernel_virt_to_phys(VirtualAddress::new(ptr.as_ptr() as usize)).into_raw();
        BUDDY_ALLOC
            .free_pages_phys_addr_unknown_order(phys_addr)
            .expect("dynslab passed a non-buddy allocation to buddy")
    }

    fn size_of_allocation(&self, ptr: NonNull<u8>) -> Option<usize> {
        let phys_addr = kernel_virt_to_phys(VirtualAddress::new(ptr.as_ptr() as usize)).into_raw();
        BUDDY_ALLOC.phys_to_size(phys_addr)
    }

    fn allocation_charge(&self, ptr: NonNull<u8>) -> Option<usize> {
        self.size_of_allocation(ptr)
    }

    fn get_max_free_block_size(&self) -> usize {
        BUDDY_ALLOC.get_max_free_block_size()
    }
}

#[cfg(all(allocator = "slab_dynamic", allocator_buddy))]
type DynHeap = RawDynHeap<BuddySystemAllocator>;

#[cfg(all(allocator = "slab_dynamic", not(allocator_buddy)))]
type DynHeap = RawDynHeap;

#[cfg(allocator = "slab_dynamic")]
pub struct DynamicSlabHeap {
    heap: SpinLock<DynHeap>,
}

#[cfg(allocator = "slab_dynamic")]
impl DynamicSlabHeap {
    pub const fn new() -> Self {
        #[cfg(allocator_buddy)]
        let heap = RawDynHeap::new_with_system_allocator(BuddySystemAllocator);
        #[cfg(not(allocator_buddy))]
        let heap = RawDynHeap::new();

        DynamicSlabHeap {
            heap: SpinLock::new(heap),
        }
    }

    /// # Safety
    /// `start_addr..start_addr+size` must describe valid, exclusively owned,
    /// writable virtual memory.
    pub unsafe fn init(&self, start_addr: usize, size: usize) {
        let mut heap = self.heap.irqsave_lock();
        heap.init(start_addr, size);
    }

    pub fn alloc(&self, layout: Layout) -> Option<NonNull<u8>> {
        let mut heap = self.heap.irqsave_lock();
        heap.allocate(&layout)
    }

    /// # Safety
    /// `ptr` must have been returned by `alloc` on this heap.
    pub unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let mut heap = self.heap.irqsave_lock();
        heap.deallocate(NonNull::new_unchecked(ptr), &layout);
    }

    /// # Safety
    /// `ptr` must have been returned by `alloc` on this heap.
    pub unsafe fn deallocate_unknown_align(&self, ptr: *mut u8) {
        let mut heap = self.heap.irqsave_lock();
        heap.deallocate_unknown_align(NonNull::new_unchecked(ptr));
    }

    /// # Safety
    /// `ptr` must have been returned by `alloc` on this heap.
    pub unsafe fn realloc(
        &self,
        ptr: *mut u8,
        layout: Layout,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let new_layout = Layout::from_size_align(new_size, layout.align()).ok()?;
        let mut heap = self.heap.irqsave_lock();
        heap.reallocate(NonNull::new_unchecked(ptr), &new_layout)
    }

    /// # Safety
    /// `ptr` must have been returned by `alloc` on this heap.
    pub unsafe fn realloc_unknown_align(
        &self,
        ptr: *mut u8,
        new_size: usize,
    ) -> Option<NonNull<u8>> {
        let mut heap = self.heap.irqsave_lock();
        heap.reallocate_unknown_align(NonNull::new_unchecked(ptr), new_size)
    }

    pub fn memory_info(&self) -> allocator_crate::MemoryInfo {
        let heap = self.heap.irqsave_lock();
        allocator_crate::MemoryInfo {
            total: heap.total(),
            used: heap.allocated(),
            max_used: heap.maximum(),
        }
    }

    pub fn size_of_allocation(&self, ptr: NonNull<u8>) -> usize {
        let heap = self.heap.irqsave_lock();
        heap.size_of_allocation(ptr).unwrap_or(0)
    }

    pub fn get_max_free_block_size(&self) -> usize {
        let heap = self.heap.irqsave_lock();
        heap.get_max_free_block_size()
    }

    pub fn print_slab_stat(&self) {
        use crate::kprintln;

        let (data, pool_total, pool_max) = {
            let heap = self.heap.irqsave_lock();
            heap.get_slab_stat()
        };

        kprintln!("size   pages  total  free   alloc ");
        kprintln!("------ ------ ------ ------ ------");
        for (size, pages, total, free) in data {
            kprintln!(
                "{:6} {:6} {:6} {:6} {:6}",
                size,
                pages,
                total,
                free,
                total - free
            );
        }
        kprintln!("PagePool: {}/{}", pool_total, pool_max);
    }

    /// Reclaim all pages from the page pool back to the system allocator.
    /// Used in tests for accurate memory leak detection.
    #[cfg(allocator = "slab_dynamic")]
    pub fn reclaim_page_pool(&self) {
        let mut heap = self.heap.irqsave_lock();
        heap.reclaim_page_pool();
    }

    /// Reclaim pages from the pool when system memory pressure is detected.
    /// Can be called by idle thread for proactive memory reclaim.
    #[cfg(allocator = "slab_dynamic")]
    pub fn check_memory_pressure(&self) {
        let mut heap = self.heap.irqsave_lock();
        heap.check_memory_pressure();
    }
}
