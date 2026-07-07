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

//! User-space pointer validation via page-table walk.
//!
//! Before dereferencing a pointer supplied by EL0, the kernel walks the
//! calling process's L1→L2→L3 page table to confirm that every page in the
//! range has a valid (present) L3 PTE.  This prevents kernel faults when a
//! malicious or buggy user thread passes an unmapped address to a syscall
//! such as `write`.

use super::AddressSpace;
use crate::arch::aarch64::mmu::PageTableManager;

const L1_SHIFT: usize = 30;
const L2_SHIFT: usize = 21;
const L3_SHIFT: usize = 12;

#[inline]
fn page_table_index(addr: usize, shift: usize) -> usize {
    (addr >> shift) & 0x1FF
}

/// Walk the page table for a single virtual address and return `true` if a
/// valid L3 page mapping exists.
///
/// Returns `false` for null pointers, kernel-range addresses, or any address
/// whose translation encounters an invalid descriptor before reaching L3.
pub fn is_user_va_mapped(address_space: &AddressSpace, va: usize) -> bool {
    if va == 0 {
        return false;
    }
    // User-space VAs on AArch64 have bit 63 clear.  Reject kernel-range
    // addresses so we never accidentally validate a kernel pointer.
    if (va as u64) & (1u64 << 63) != 0 {
        return false;
    }

    let l1 = unsafe { &*address_space.root_ptr() };
    let l1_entry = l1.entry(page_table_index(va, L1_SHIFT));
    let Some(l2_ptr) = l1_entry.table_ptr() else {
        return false;
    };
    let l2 = unsafe { &*l2_ptr };
    let l2_entry = l2.entry(page_table_index(va, L2_SHIFT));
    let Some(l3_ptr) = l2_entry.table_ptr() else {
        return false;
    };
    let l3 = unsafe { &*l3_ptr };
    let l3_entry = l3.entry(page_table_index(va, L3_SHIFT));
    l3_entry.is_valid()
}

/// Check that every page overlapping `[va, va+len)` is mapped.
///
/// `len == 0` is treated as valid (no bytes to touch).  Wrapping ranges
/// (where `va + len` overflows) are rejected.
pub fn is_user_range_mapped(address_space: &AddressSpace, va: usize, len: usize) -> bool {
    if len == 0 {
        return true;
    }
    let Some(end) = va.checked_add(len) else {
        return false;
    };
    let first_page = va & !0xFFF;
    let last_page = (end - 1) & !0xFFF;
    let mut page = first_page;
    loop {
        if !is_user_va_mapped(address_space, page) {
            return false;
        }
        if page == last_page {
            break;
        }
        page = page.checked_add(0x1000).unwrap();
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_null_pointer_unmapped() {
        let asp = AddressSpace::try_new().expect("AddressSpace::try_new failed");
        assert!(!is_user_va_mapped(&asp, 0), "null must be unmapped");
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_unmapped_user_va() {
        let asp = AddressSpace::try_new().expect("AddressSpace::try_new failed");
        // A freshly created address space has no user mappings.
        assert!(
            !is_user_va_mapped(&asp, 0x10000),
            "unmapped user VA must return false"
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_empty_range_is_valid() {
        let asp = AddressSpace::try_new().expect("AddressSpace::try_new failed");
        assert!(
            is_user_range_mapped(&asp, 0x10000, 0),
            "zero-length range must be considered valid"
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_unmapped_range() {
        let asp = AddressSpace::try_new().expect("AddressSpace::try_new failed");
        assert!(
            !is_user_range_mapped(&asp, 0x10000, 0x2000),
            "unmapped range must return false"
        );
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_wrapping_range_rejected() {
        let asp = AddressSpace::try_new().expect("AddressSpace::try_new failed");
        assert!(
            !is_user_range_mapped(&asp, usize::MAX, 1),
            "wrapping range must be rejected"
        );
    }

    // W3: A VA that IS mapped in the page table must return true.
    // This is the positive case the spec scenario "Mapped buffer succeeds"
    // requires; all other tests above only cover the negative path.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_mapped_va_returns_true() {
        let asp = AddressSpace::try_new().expect("AddressSpace::try_new failed");
        // Pick a user-space VA and PA, both 4 KiB-aligned, within the user
        // VA range (< 2^39).  Map one page and verify the walk finds it.
        const VA: usize = 0x0001_0000; // 64 KiB, in user space
        const PA: usize = 0x0001_0000; // identity-mapped for the test
        let root = unsafe { &mut *asp.root_ptr() };
        crate::arch::aarch64::mmu::map_user_range_in_pgtbl(
            root,
            VA,
            PA,
            0x1000,
            crate::arch::aarch64::mmu::MemAttributes::Normal,
        )
        .expect("map_user_range_in_pgtbl failed");

        assert!(
            is_user_va_mapped(&asp, VA),
            "a VA with a valid L3 PTE must return true"
        );
        assert!(
            is_user_range_mapped(&asp, VA, 0x1000),
            "a fully-mapped range must return true"
        );
        // An adjacent unmapped page still returns false.
        assert!(
            !is_user_va_mapped(&asp, VA + 0x1000),
            "an unmapped neighbour VA must return false"
        );
    }

    // W6 / spec scenario "Buffer spanning mapped and unmapped pages returns
    // EFAULT": a single buffer whose first page is mapped but whose second
    // page is not must be rejected by is_user_range_mapped.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_range_spanning_mapped_and_unmapped_pages() {
        let asp = AddressSpace::try_new().expect("AddressSpace::try_new failed");
        const VA: usize = 0x0002_0000;
        const PA: usize = 0x0002_0000;
        let root = unsafe { &mut *asp.root_ptr() };
        // Map exactly ONE page at VA.
        crate::arch::aarch64::mmu::map_user_range_in_pgtbl(
            root,
            VA,
            PA,
            0x1000,
            crate::arch::aarch64::mmu::MemAttributes::Normal,
        )
        .expect("map_user_range_in_pgtbl failed");

        // A 2-page buffer starting at VA spans one mapped page and one
        // unmapped page (VA + 0x1000).  The range check must fail.
        assert!(
            !is_user_range_mapped(&asp, VA, 0x2000),
            "a range spanning a mapped and an unmapped page must return false"
        );
    }
}
