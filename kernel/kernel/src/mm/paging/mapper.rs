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

//! Builds page tables using architecture-provided descriptors and frame allocation.
//!
//! Inactive tables are reclaimed on drop, including partially built trees.
//! Call `retain_tables` before installing a root in hardware. Modifying active
//! tables requires a separate TLB protocol.

use super::{FrameAllocator, PageFormat};
use crate::mm::{
    kernel_phys_to_virt, MemAttribute, MemFlags, MemType, PhysicalAddress, VirtualAddress,
};
use core::{marker::PhantomData, mem::size_of};

/// Initialization of newly allocated mapping backing, before publication.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FrameInit {
    /// Preserve previous contents. Initialize them before exposing to users.
    Uninitialized,
    /// Clear every backing page through its kernel direct-map alias.
    Zeroed,
}

#[must_use = "dropping an inactive mapper releases its page tables"]
pub struct PageMapper<F: FrameAllocator, P: PageFormat = crate::arch::page::PageEntry> {
    root_addr: usize,
    owns_tables: bool,
    allocator: F,
    format: PhantomData<P>,
}

impl<F: FrameAllocator, P: PageFormat> PageMapper<F, P> {
    /// Allocate and clear a new root table.
    ///
    /// # Safety
    /// P must describe the configured hardware format. Every frame returned by
    /// the allocator must be exclusively owned, writable through the kernel
    /// direct mapping, and remain valid for the lifetime of these page tables.
    pub unsafe fn create(allocator: F) -> Result<Self, &'static str> {
        if !P::PAGE_SIZE.is_power_of_two()
            || P::PAGE_SIZE < size_of::<usize>()
            || P::LEVELS == 0
            || P::PHYS_ADDR_BITS >= usize::BITS as u8
            || P::VIRT_ADDR_BITS >= usize::BITS as u8
        {
            return Err("unsupported page-table geometry");
        }
        let mut mapper = Self {
            root_addr: 0,
            owns_tables: false,
            allocator,
            format: PhantomData,
        };
        mapper.root_addr = mapper.allocate_table()?;
        mapper.owns_tables = true;
        Ok(mapper)
    }

    /// Keep the table tree permanently allocated, even when this mapper drops.
    /// Call before installing the root on any CPU. This does not manage mapped
    /// data pages; their owner must separately guarantee their lifetime.
    pub fn retain_tables(&mut self) {
        self.owns_tables = false;
    }

    pub fn root_address(&self) -> PhysicalAddress {
        PhysicalAddress::new(self.root_addr)
    }

    fn allocate_table(&mut self) -> Result<usize, &'static str> {
        let addr = self
            .allocator
            .alloc_frame()
            .ok_or("out of page-table frames")?
            .into_raw();
        if addr & (P::PAGE_SIZE - 1) != 0 || addr >= (1usize << P::PHYS_ADDR_BITS) {
            // SAFETY: the unpublished allocation has no users.
            unsafe { self.allocator.free_frame(PhysicalAddress::new(addr)) }
                .expect("failed to return an unusable page-table frame");
            return Err("invalid page-table frame");
        }
        let table = kernel_phys_to_virt(PhysicalAddress::new(addr)).into_raw() as *mut u8;
        // SAFETY: create's caller guarantees exclusive, writable backing frames.
        unsafe { table.write_bytes(0, P::PAGE_SIZE) };
        Ok(addr)
    }

    fn valid_va(addr: usize) -> bool {
        let mask = (1usize << P::VIRT_ADDR_BITS) - 1;
        addr <= mask || addr >= !mask
    }

    fn entry_ptr(table: usize, va: usize, level: u8) -> Result<*mut usize, &'static str> {
        let index = P::get_index(va, level);
        if index >= P::PAGE_SIZE / size_of::<usize>() {
            return Err("page-table index exceeds table size");
        }
        let table = kernel_phys_to_virt(PhysicalAddress::new(table)).into_raw() as *mut usize;
        // SAFETY: the index is in bounds of a page-table frame.
        Ok(unsafe { table.add(index) })
    }

    fn leaf_entry(&self, va: usize) -> Option<usize> {
        if !Self::valid_va(va) {
            return None;
        }
        let mut table = self.root_addr;
        for level in 0..P::LEVELS {
            let entry = Self::entry_ptr(table, va, level).ok()?;
            // SAFETY: tables remain live while this mapper is borrowed.
            let entry = unsafe { entry.read() };
            if level == P::LEVELS - 1 {
                return P::is_valid(entry).then_some(entry);
            }
            table = P::table_address(entry)?;
        }
        None
    }

    #[cfg(test)]
    pub(crate) fn leaf_descriptor(&self, addr: usize) -> Option<usize> {
        self.leaf_entry(addr)
    }

    /// Translate a mapped address, including its offset within the page.
    pub fn translate(&self, addr: usize) -> Option<PhysicalAddress> {
        let frame = P::table_address(self.leaf_entry(addr)?)?;
        Some(PhysicalAddress::new(frame + (addr & (P::PAGE_SIZE - 1))))
    }

    fn leaf_slot(&mut self, va: usize) -> Result<*mut usize, &'static str> {
        let mut table = self.root_addr;
        for level in 0..P::LEVELS - 1 {
            let slot = Self::entry_ptr(table, va, level)?;
            // SAFETY: this mapper exclusively builds inactive tables.
            let entry = unsafe { slot.read() };
            table = if !P::is_valid(entry) {
                let next = self.allocate_table()?;
                unsafe { slot.write(P::table_descriptor(next)) };
                next
            } else {
                P::table_address(entry).ok_or("mapping conflicts with a block descriptor")?
            };
        }
        Self::entry_ptr(table, va, P::LEVELS - 1)
    }

    /// Allocate the intermediate tables for a virtual range before assigning
    /// backing pages. Existing leaf entries are left unchanged. This lets a
    /// caller consume the remaining frames without starving table allocation.
    pub fn prepare_range(&mut self, virt: VirtualAddress, len: usize) -> Result<(), &'static str> {
        if len == 0 {
            return Ok(());
        }
        if (virt.into_raw() | len) & (P::PAGE_SIZE - 1) != 0 {
            return Err("mapping range must be page aligned");
        }
        let end = virt
            .into_raw()
            .checked_add(len)
            .ok_or("virtual mapping range overflow")?;
        if !Self::valid_va(virt.into_raw())
            || !Self::valid_va(end - 1)
            || (virt.into_raw() >> P::VIRT_ADDR_BITS) != ((end - 1) >> P::VIRT_ADDR_BITS)
        {
            return Err("mapping range exceeds address space");
        }
        let span = P::PAGE_SIZE
            .checked_mul(P::PAGE_SIZE / size_of::<usize>())
            .ok_or("page-table span overflow")?;
        let mut addr = virt.into_raw();
        while addr < end {
            self.leaf_slot(addr)?;
            addr += (span - (addr & (span - 1))).min(end - addr);
        }
        Ok(())
    }

    fn existing_slot(&self, va: usize) -> Option<*mut usize> {
        let mut table = self.root_addr;
        for level in 0..P::LEVELS - 1 {
            let slot = Self::entry_ptr(table, va, level).ok()?;
            table = P::table_address(unsafe { slot.read() })?;
        }
        Self::entry_ptr(table, va, P::LEVELS - 1).ok()
    }

    /// Back an exclusively reserved VA range with individually owned frames.
    /// Mapping attributes, backing initialization and translation synchronization
    /// are supplied by the caller. Failure restores an unmapped range.
    ///
    /// # Safety
    /// Caller serializes all walks/updates, owns the VA reservation, and ensures
    /// the range has no users until success. Uninitialized backing must be fully
    /// initialized before exposing it to users. Attributes must be compatible
    /// with the backing RAM and its kernel direct-map alias.
    ///
    /// `synchronize` must publish table writes and complete invalidation of all
    /// relevant translations and walk caches before returning, and must not
    /// unwind. It may be a no-op only for tables never installed on any CPU.
    /// The callback is also used during rollback, before frames are released.
    pub(crate) unsafe fn map_owned_range(
        &mut self,
        virt: VirtualAddress,
        len: usize,
        attributes: MemAttribute,
        init: FrameInit,
        mut synchronize: impl FnMut(),
    ) -> Result<(), &'static str> {
        Self::validate_attributes(attributes)?;
        let start = virt.into_raw();
        let end = start.checked_add(len).ok_or("owned mapping overflow")?;
        if len == 0 || (start | len) & (P::PAGE_SIZE - 1) != 0 {
            return Err("invalid owned range");
        }
        // Rollback walks raw table indices, so reject invalid address aliases
        // before entering a path that can release any existing table entries.
        if !Self::valid_va(start)
            || !Self::valid_va(end - 1)
            || (start >> P::VIRT_ADDR_BITS) != ((end - 1) >> P::VIRT_ADDR_BITS)
        {
            return Err("mapping range exceeds address space");
        }
        for va in (start..end).step_by(P::PAGE_SIZE) {
            if self.leaf_entry(va).is_some() {
                return Err("owned range already mapped");
            }
        }
        let result = (|| {
            self.prepare_range(virt, len)?;
            for va in (start..end).step_by(P::PAGE_SIZE) {
                let frame = self
                    .allocator
                    .alloc_frame()
                    .ok_or("out of backing frames")?;
                if init == FrameInit::Zeroed {
                    let ptr = kernel_phys_to_virt(frame).into_raw() as *mut u8;
                    ptr.write_bytes(0, P::PAGE_SIZE);
                }
                if let Err(e) =
                    self.map_range(VirtualAddress::new(va), frame, P::PAGE_SIZE, attributes)
                {
                    self.allocator
                        .free_frame(frame)
                        .expect("return unpublished frame");
                    return Err(e);
                }
            }
            Ok(())
        })();
        if result.is_err() {
            self.release_owned_range(virt, len, &mut synchronize);
        } else {
            synchronize();
        }
        result
    }

    /// Revoke an owned range, synchronize CPUs, then release data/table frames.
    /// Invalid leaf descriptors temporarily retain PFNs as a no-allocation
    /// retirement ledger; the caller's mapping lock excludes software walkers.
    ///
    /// # Safety
    /// The caller exclusively owns the range and its backing, has stopped all
    /// users and serializes walks/updates. No unrelated mapping may lie inside.
    /// The range must be nonempty, page aligned and valid for this format.
    /// `synchronize` has the same requirements as in `map_owned_range`; it is
    /// called before releasing data frames and again before releasing retired
    /// tables, if any. It must invalidate intermediate walk caches as well.
    pub(crate) unsafe fn release_owned_range(
        &mut self,
        virt: VirtualAddress,
        len: usize,
        mut synchronize: impl FnMut(),
    ) {
        let start = virt.into_raw();
        let end = start.checked_add(len).expect("owned range overflow");
        for va in (start..end).step_by(P::PAGE_SIZE) {
            if let Some(slot) = self.existing_slot(va) {
                let entry = slot.read();
                if P::is_valid(entry) {
                    slot.write(entry & !1);
                }
            }
        }
        synchronize();
        for va in (start..end).step_by(P::PAGE_SIZE) {
            if let Some(slot) = self.existing_slot(va) {
                let entry = slot.read();
                if entry & 0b11 == 0b10 {
                    let frame = P::table_address(entry | 1).expect("retired page descriptor");
                    slot.write(0);
                    self.allocator
                        .free_frame(PhysicalAddress::new(frame))
                        .expect("release owned backing");
                }
            }
        }
        // Disconnect empty tables but keep their storage until walk-cache
        // invalidation completes. The retired page's first word stores a PFN
        // link with invalid descriptor bits, never a writable live mapping.
        let mut retired = 0;
        let span = P::PAGE_SIZE * (P::PAGE_SIZE / size_of::<usize>());
        let mut va = start;
        while va < end {
            self.prune_empty_path(va, &mut retired);
            va += (span - (va & (span - 1))).min(end - va);
        }
        if retired != 0 {
            synchronize();
            while retired != 0 {
                let frame = retired;
                retired = (kernel_phys_to_virt(PhysicalAddress::new(frame)).into_raw()
                    as *const usize)
                    .read();
                self.allocator
                    .free_frame(PhysicalAddress::new(frame))
                    .expect("release empty owned table");
            }
        }
    }

    unsafe fn prune_empty_path(&mut self, va: usize, retired: &mut usize) {
        assert!(P::LEVELS <= 4);
        let mut tables = [0usize; 4];
        let mut slots = [core::ptr::null_mut::<usize>(); 4];
        tables[0] = self.root_addr;
        let mut depth = 0;
        for level in 0..P::LEVELS - 1 {
            let slot = Self::entry_ptr(tables[level as usize], va, level).unwrap();
            let Some(child) = P::table_address(slot.read()) else {
                break;
            };
            slots[level as usize] = slot;
            tables[level as usize + 1] = child;
            depth = level as usize + 1;
        }
        for level in (1..=depth).rev() {
            let ptr =
                kernel_phys_to_virt(PhysicalAddress::new(tables[level])).into_raw() as *mut usize;
            if core::slice::from_raw_parts(ptr, P::PAGE_SIZE / size_of::<usize>())
                .iter()
                .any(|e| *e != 0)
            {
                break;
            }
            slots[level - 1].write(0);
            ptr.write(*retired);
            *retired = tables[level];
        }
    }

    fn validate_attributes(attributes: MemAttribute) -> Result<(), &'static str> {
        if attributes
            .flags
            .contains(MemFlags::WRITE | MemFlags::EXECUTE)
        {
            return Err("writable executable mappings are not supported");
        }
        if !attributes.flags.contains(MemFlags::READ)
            || (matches!(attributes.memory_type, MemType::Device)
                && attributes.flags.contains(MemFlags::EXECUTE))
        {
            return Err("mapping must be readable and device memory cannot be executable");
        }
        Ok(())
    }

    /// Map an aligned range in an inactive table. Existing mappings are rejected.
    /// On allocation failure, some of the range may already have been mapped;
    /// the caller must discard the table rather than install a partial layout.
    pub fn map_range(
        &mut self,
        virt: VirtualAddress,
        phys: PhysicalAddress,
        len: usize,
        attributes: MemAttribute,
    ) -> Result<(), &'static str> {
        Self::validate_attributes(attributes)?;
        if len == 0 {
            return Ok(());
        }
        if (virt.into_raw() | phys.into_raw() | len) & (P::PAGE_SIZE - 1) != 0 {
            return Err("mapping range must be page aligned");
        }
        let end = virt
            .into_raw()
            .checked_add(len)
            .ok_or("virtual mapping range overflow")?;
        let phys_end = phys
            .into_raw()
            .checked_add(len)
            .ok_or("physical mapping range overflow")?;
        if !Self::valid_va(virt.into_raw())
            || !Self::valid_va(end - 1)
            || (virt.into_raw() >> P::VIRT_ADDR_BITS) != ((end - 1) >> P::VIRT_ADDR_BITS)
            || phys_end > (1usize << P::PHYS_ADDR_BITS)
        {
            return Err("mapping range exceeds address space");
        }
        for addr in (virt.into_raw()..end).step_by(P::PAGE_SIZE) {
            if self.leaf_entry(addr).is_some() {
                return Err("virtual page is already mapped");
            }
        }
        for offset in (0..len).step_by(P::PAGE_SIZE) {
            let slot = self.leaf_slot(virt.into_raw() + offset)?;
            unsafe {
                slot.write(P::get_translate(
                    phys.into_raw() + offset,
                    attributes,
                    false,
                ))
            };
        }
        Ok(())
    }
}

impl<F: FrameAllocator, P: PageFormat> Drop for PageMapper<F, P> {
    fn drop(&mut self) {
        if self.owns_tables {
            // SAFETY: these tables have not been published to hardware. Only
            // child tables are released; leaf backing belongs to the caller.
            unsafe { self.release_table(self.root_addr, 0) };
        }
    }
}

impl<F: FrameAllocator, P: PageFormat> PageMapper<F, P> {
    unsafe fn release_table(&mut self, table: usize, level: u8) {
        if level + 1 < P::LEVELS {
            let entries =
                kernel_phys_to_virt(PhysicalAddress::new(table)).into_raw() as *const usize;
            for index in 0..P::PAGE_SIZE / size_of::<usize>() {
                if let Some(child) = P::table_address(unsafe { entries.add(index).read() }) {
                    unsafe { self.release_table(child, level + 1) };
                }
            }
        }
        unsafe { self.allocator.free_frame(PhysicalAddress::new(table)) }
            .expect("invalid page-table frame during cleanup");
    }
}
