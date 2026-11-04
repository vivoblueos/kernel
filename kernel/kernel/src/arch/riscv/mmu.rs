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

//! Sv39 page tables for RISC-V64 — the paging half of roadmap item #1.
//!
//! # Scope
//!
//! Building block (M0) only: create/destroy Sv39 page tables and encode
//! `satp`. It does **not** install them — see the blueprint
//! (`docs/MMU设计蓝图.md`), milestones M1+.
//!
//! # Why the kernel runs in M-mode and this still works
//!
//! RISC-V translates **only** S-mode and U-mode accesses; M-mode is never
//! translated regardless of `satp`. Our kernel runs in M-mode
//! (`arch/riscv/mod.rs` sets `MSTATUS_MPP_M`), so:
//!
//! - The kernel needs no page table for itself and keeps using physical
//!   addresses, exactly as today.
//! - A page-table frame can be reached as `*mut PageTable` at its **physical**
//!   address — see [`table_at`]. No linear map, no `KERNEL_VIRT_OFFSET`.
//! - The tables built here only ever govern the code we later drop into
//!   U-mode.
//!
//! # Why this module has no `crate::` dependencies
//!
//! Physical frames come from an injected [`FrameAllocator`], so this module
//! depends on nothing but `core`. That keeps it compilable inside the kernel
//! *and* includable in a host unit test (see the `tests` module at the bottom),
//! which is how the walk/map/translate logic is verified without the blueos
//! toolchain.

use core::ptr;

// ---------------------------------------------------------------------------
// Sv39 geometry
// ---------------------------------------------------------------------------

/// Granule size of an Sv39 leaf page.
pub const PAGE_SIZE: usize = 4096;
/// Size of a 2 MiB leaf ("megapage") produced at level 1.
pub const MEGAPAGE_SIZE: usize = 2 * 1024 * 1024;
/// Number of page-table levels (L2 root → L1 → L0 leaf).
pub const LEVELS: usize = 3;
/// Entries per page table: 9 index bits.
pub const ENTRIES: usize = 512;

/// VPN shift for each level: L0 = 12 (4 KiB), L1 = 21 (2 MiB), L2 = 30 (1 GiB).
const VPN_SHIFT: [usize; LEVELS] = [12, 21, 30];
const INDEX_MASK: usize = ENTRIES - 1;

/// Highest virtual address Sv39 can name: bits [38:0], sign-extended.
const VA_LIMIT: usize = 1usize << 39;

// ---------------------------------------------------------------------------
// satp
// ---------------------------------------------------------------------------

/// `satp.MODE` value selecting Sv39.
pub const SATP_MODE_SV39: u64 = 8;
const SATP_MODE_SHIFT: u64 = 60;
const SATP_PPN_BITS: u64 = 44;

/// Encode `satp` for Sv39 with `root_phys` as the root page table.
///
/// `root_phys` must be 4 KiB aligned. Bits [63:60] = MODE, [43:0] = PPN.
pub const fn satp_sv39(root_phys: usize) -> u64 {
    let ppn = (root_phys >> 12) as u64 & ((1u64 << SATP_PPN_BITS) - 1);
    (SATP_MODE_SV39 << SATP_MODE_SHIFT) | ppn
}

/// Extract the root table physical address back out of an `satp` value.
pub const fn satp_root(satp: u64) -> usize {
    ((satp & ((1u64 << SATP_PPN_BITS) - 1)) as usize) << 12
}

// ---------------------------------------------------------------------------
// PTE bits
// ---------------------------------------------------------------------------

pub const PTE_V: u64 = 1 << 0;
pub const PTE_R: u64 = 1 << 1;
pub const PTE_W: u64 = 1 << 2;
pub const PTE_X: u64 = 1 << 3;
pub const PTE_U: u64 = 1 << 4;
pub const PTE_G: u64 = 1 << 5;
pub const PTE_A: u64 = 1 << 6;
pub const PTE_D: u64 = 1 << 7;

const PTE_PPN_SHIFT: u64 = 10;
const PTE_PPN_BITS: u64 = 44;
/// PPN occupies bits [53:10].
const PTE_PPN_MASK: u64 = ((1u64 << PTE_PPN_BITS) - 1) << PTE_PPN_SHIFT;
/// Every architecturally defined flag bit (V..D).
const PTE_FLAGS_MASK: u64 = 0xff;

/// A single page table entry.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Pte(u64);

impl Pte {
    #[inline]
    pub const fn raw(self) -> u64 {
        self.0
    }

    #[inline]
    pub const fn is_valid(self) -> bool {
        self.0 & PTE_V != 0
    }

    /// True when this entry is a leaf, i.e. it carries any of R/W/X.
    ///
    /// A non-leaf entry has R = W = X = 0 and points at the next level.
    #[inline]
    pub const fn is_leaf(self) -> bool {
        self.0 & (PTE_R | PTE_W | PTE_X) != 0
    }

    /// Physical address this entry points at (next table, or leaf target).
    #[inline]
    pub const fn ppn(self) -> usize {
        ((self.0 & PTE_PPN_MASK) >> PTE_PPN_SHIFT) as usize
    }

    /// Physical **address** (PPN << 12).
    #[inline]
    pub const fn phys(self) -> usize {
        self.ppn() << 12
    }

    /// Build a non-leaf entry pointing at the next-level table at `phys`.
    #[inline]
    pub const fn next_table(phys: usize) -> Self {
        Self(Self::ppn_field(phys) | PTE_V)
    }

    /// Build a leaf entry for the page frame at `phys` with `perms`.
    ///
    /// A/D are set eagerly: our trap handler does not yet implement the
    /// "fault to set A/D" shortcut, and leaving them clear is only legal if
    /// the hardware or software updates them on access.
    #[inline]
    pub const fn leaf(phys: usize, perms: Perms) -> Self {
        Self(
            Self::ppn_field(phys)
                | perms.to_pte()
                | PTE_V
                | PTE_A
                | PTE_D,
        )
    }

    #[inline]
    const fn ppn_field(phys: usize) -> u64 {
        (((phys >> 12) as u64) << PTE_PPN_SHIFT) & PTE_PPN_MASK
    }

    #[inline]
    pub const fn perms(self) -> Perms {
        Perms::from_pte(self.0)
    }
}

/// Access permissions for a mapping.
///
/// Mirrors `blueos_loader::MemoryPermissions` (R/W/X) plus a [`Perms::USER`]
/// flag for the PTE `U` bit — without depending on the loader crate, so this
/// module stays self-contained. Callers bridging from the loader map
/// `MemoryPermissions` onto this type and OR in [`Perms::USER`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Perms(u8);

impl Perms {
    pub const NONE: Self = Self(0);
    pub const READ: Self = Self(1 << 0);
    pub const WRITE: Self = Self(1 << 1);
    pub const EXEC: Self = Self(1 << 2);
    /// PTE `U` bit: reachable from U-mode. Absent ⇒ kernel-only.
    pub const USER: Self = Self(1 << 3);

    /// Convenience: read + write, user accessible.
    pub const RW_USER: Self = Self(Self::READ.0 | Self::WRITE.0 | Self::USER.0);
    /// Convenience: read + execute, user accessible.
    pub const RX_USER: Self = Self(Self::READ.0 | Self::EXEC.0 | Self::USER.0);
    /// Convenience: read-only, user accessible.
    pub const RO_USER: Self = Self(Self::READ.0 | Self::USER.0);

    #[inline]
    pub const fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }

    /// Same set of permissions, minus those in `rhs`.
    ///
    /// Only used to drop `W` when a page is write-protected for copy-on-write;
    /// there is no general "unset" because every other caller builds its
    /// permissions from scratch.
    #[inline]
    pub const fn without(self, rhs: Self) -> Self {
        Self(self.0 & !rhs.0)
    }

    #[inline]
    pub const fn contains(self, requested: Self) -> bool {
        self.0 & requested.0 == requested.0
    }

    #[inline]
    const fn to_pte(self) -> u64 {
        let mut p = 0u64;
        if self.contains(Self::READ) {
            p |= PTE_R;
        }
        if self.contains(Self::WRITE) {
            p |= PTE_W;
        }
        if self.contains(Self::EXEC) {
            p |= PTE_X;
        }
        if self.contains(Self::USER) {
            p |= PTE_U;
        }
        p
    }

    #[inline]
    const fn from_pte(bits: u64) -> Self {
        let mut p = 0u8;
        if bits & PTE_R != 0 {
            p |= Self::READ.0;
        }
        if bits & PTE_W != 0 {
            p |= Self::WRITE.0;
        }
        if bits & PTE_X != 0 {
            p |= Self::EXEC.0;
        }
        if bits & PTE_U != 0 {
            p |= Self::USER.0;
        }
        Self(p)
    }
}

// ---------------------------------------------------------------------------
// Page table
// ---------------------------------------------------------------------------

/// One level of an Sv39 page table: 512 entries, one 4 KiB frame.
#[repr(C, align(4096))]
pub struct PageTable {
    entries: [Pte; ENTRIES],
}

impl PageTable {
    /// Zero a freshly allocated frame so stale entries cannot alias memory.
    ///
    /// # Safety
    /// `self` must exclusively own the frame it lives in.
    #[inline]
    pub unsafe fn zero(&mut self) {
        ptr::write_bytes(self as *mut Self as *mut u8, 0, PAGE_SIZE);
    }

    #[inline]
    pub fn entry(&self, index: usize) -> Pte {
        self.entries[index]
    }

    #[inline]
    pub fn set_entry(&mut self, index: usize, pte: Pte) {
        self.entries[index] = pte;
    }

    /// True when no entry is valid — the table can be freed.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.entries.iter().all(|e| !e.is_valid())
    }
}

/// Reach the page-table frame living at physical address `phys`.
///
/// Correct on this port precisely **because** the kernel runs in M-mode and is
/// therefore never translated: a physical address is a directly usable
/// address. (A host unit test hands us host addresses that behave the same
/// way, which is why the walk logic can be tested off-target.)
///
/// # Safety
/// `phys` must be a 4 KiB-aligned address of a frame owned as a page table.
#[inline]
pub(crate) unsafe fn table_at(phys: usize) -> *mut PageTable {
    phys as *mut PageTable
}

#[inline]
const fn is_page_aligned(addr: usize) -> bool {
    addr & (PAGE_SIZE - 1) == 0
}

// ---------------------------------------------------------------------------
// Frame allocation
// ---------------------------------------------------------------------------

/// Source of 4 KiB physical frames for page tables.
///
/// Implemented by the kernel (backed by the buddy allocator,
/// `alloc_pages_phys_addr(0)` → one 4 KiB page) and by a static arena in the
/// host unit tests.
pub trait FrameAllocator {
    /// Allocate one zeroed, 4 KiB-aligned frame; return its physical address.
    fn alloc_frame(&self) -> Option<usize>;
    /// Release a frame previously returned by [`FrameAllocator::alloc_frame`].
    ///
    /// # Safety
    /// `phys` must be an unallocated frame obtained from `alloc_frame`.
    unsafe fn free_frame(&self, phys: usize);
}

/// The registered allocator. Written once during early boot, read-only after.
///
/// Deliberately a raw `static mut` like the other bootstrap state in
/// `arch/riscv/mod.rs` (`EARLY_SCRATCH`): registration happens on one hart
/// before anything else can run.
static mut FRAME_ALLOC: Option<&'static dyn FrameAllocator> = None;

/// Register the frame allocator. Call once, early, before any mapping.
pub fn set_frame_allocator(alloc: &'static dyn FrameAllocator) {
    unsafe {
        FRAME_ALLOC = Some(alloc);
    }
}

#[inline]
fn alloc_frame() -> Option<usize> {
    // SAFETY: `FRAME_ALLOC` is written once before use and only read after.
    unsafe { FRAME_ALLOC.and_then(|a| a.alloc_frame()) }
}

#[inline]
unsafe fn free_frame(phys: usize) {
    // SAFETY: caller guarantees `phys` came from `alloc_frame`.
    if let Some(a) = FRAME_ALLOC {
        a.free_frame(phys);
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MapError {
    /// Frame allocator exhausted, or not registered yet.
    NoMemory,
    /// An intermediate level already holds a 2 MiB/1 GiB leaf, so a 4 KiB
    /// mapping would overwrite it.
    LeafConflict,
    /// `va`/`pa` not page aligned, zero length, or the range leaves the 39-bit
    /// space.
    InvalidRange,
}

pub type MapResult = Result<(), MapError>;

// ---------------------------------------------------------------------------
// Mapping
// ---------------------------------------------------------------------------

/// Allocate a zeroed root page table (level 2) for a new address space.
pub fn new_root() -> Option<usize> {
    let phys = alloc_frame()?;
    unsafe { (*table_at(phys)).zero() };
    Some(phys)
}

/// Map `[va, va + size)` onto `[pa, pa + size)` as 4 KiB pages.
///
/// `va` and `pa` must be page aligned; `size` is rounded up to a whole number
/// of pages. Intermediate tables are allocated on demand.
///
/// Only **page-table** frames are owned by this module; the mapped `pa` range
/// belongs to the caller and is *not* freed by [`unmap_range`].
///
/// # Safety
/// `root_phys` must be a live root table from [`new_root`], and the frames it
/// points at must be exclusively owned by this address space.
pub unsafe fn map_range(
    root_phys: usize,
    va: usize,
    pa: usize,
    size: usize,
    perms: Perms,
) -> MapResult {
    if size == 0 || !is_page_aligned(va) || !is_page_aligned(pa) {
        return Err(MapError::InvalidRange);
    }
    // Reject absurd sizes *before* computing `pages`: `size + PAGE_SIZE - 1`
    // would wrap around `usize::MAX`, and this also caps `pages * PAGE_SIZE`
    // below the overflow point.
    if size > VA_LIMIT {
        return Err(MapError::InvalidRange);
    }
    let pages = size.div_ceil(PAGE_SIZE);
    if va.checked_add(pages * PAGE_SIZE).is_none_or(|end| end > VA_LIMIT) {
        return Err(MapError::InvalidRange);
    }

    for i in 0..pages {
        let v = va + i * PAGE_SIZE;
        let p = pa + i * PAGE_SIZE;

        // Descend L2 → L1, allocating intermediate tables as needed.
        let mut table = root_phys;
        for level in (1..LEVELS).rev() {
            let index = (v >> VPN_SHIFT[level]) & INDEX_MASK;
            let entry = {
                let t = &mut *table_at(table);
                let e = t.entry(index);
                if !e.is_valid() {
                    let frame = alloc_frame().ok_or(MapError::NoMemory)?;
                    (*table_at(frame)).zero();
                    let next = Pte::next_table(frame);
                    t.set_entry(index, next);
                    next
                } else if e.is_leaf() {
                    return Err(MapError::LeafConflict);
                } else {
                    e
                }
            };
            table = entry.phys();
        }

        // Level 0 holds the leaf.
        let index = (v >> VPN_SHIFT[0]) & INDEX_MASK;
        let t = &mut *table_at(table);
        t.set_entry(index, Pte::leaf(p, perms));
    }
    Ok(())
}

/// Unmap `[va, va + size)`, freeing page-table frames that become empty.
///
/// The mapped target frames are **not** released — they are owned by whoever
/// supplied `pa` to [`map_range`].
///
/// # Safety
/// As [`map_range`].
pub unsafe fn unmap_range(root_phys: usize, va: usize, size: usize) -> MapResult {
    if size == 0 || !is_page_aligned(va) {
        return Err(MapError::InvalidRange);
    }
    let pages = size.div_ceil(PAGE_SIZE);

    for i in 0..pages {
        let v = va + i * PAGE_SIZE;
        // Walk down, recording the tables we pass through.
        let mut path = [0usize; LEVELS];
        let mut table = root_phys;
        let mut levels_descended = 0usize;
        let mut ok = true;

        for level in (0..LEVELS).rev() {
            path[level] = table;
            levels_descended += 1;
            let index = (v >> VPN_SHIFT[level]) & INDEX_MASK;
            let entry = (*table_at(table)).entry(index);
            if level == 0 {
                if entry.is_valid() {
                    (*table_at(table)).set_entry(index, Pte(0));
                }
                break;
            }
            if !entry.is_valid() {
                ok = false;
                break;
            }
            if entry.is_leaf() {
                // A megapage/gigapage leaf covers this whole page; drop it.
                (*table_at(table)).set_entry(index, Pte(0));
                ok = false;
                break;
            }
            table = entry.phys();
        }
        if !ok {
            continue;
        }

        // Reclaim intermediate tables that just went empty, bottom-up.
        for level in 1..levels_descended {
            let parent = path[level];
            let child_index = (v >> VPN_SHIFT[level - 1]) & INDEX_MASK;
            let child_entry = (*table_at(parent)).entry(child_index);
            if !child_entry.is_valid() || child_entry.is_leaf() {
                continue;
            }
            let child = child_entry.phys();
            if (*table_at(child)).is_empty() {
                (*table_at(parent)).set_entry(child_index, Pte(0));
                free_frame(child);
            }
        }
    }
    Ok(())
}

/// Translate `va` through `root_phys`.
///
/// Returns the physical address (with the intra-page offset preserved) and the
/// permissions of the leaf that covers it, or `None` if unmapped. Handles
/// 2 MiB/1 GiB leaves as well as 4 KiB pages.
///
/// # Safety
/// `root_phys` must be a live root table.
pub unsafe fn translate(root_phys: usize, va: usize) -> Option<(usize, Perms)> {
    let mut table = root_phys;
    for level in (0..LEVELS).rev() {
        let index = (va >> VPN_SHIFT[level]) & INDEX_MASK;
        let entry = (*table_at(table)).entry(index);
        if !entry.is_valid() {
            return None;
        }
        if entry.is_leaf() {
            let offset = va & ((1usize << VPN_SHIFT[level]) - 1);
            return Some((entry.phys() + offset, entry.perms()));
        }
        table = entry.phys();
    }
    None
}

/// Rewrite the permissions of the leaf that maps `va`, keeping its frame.
///
/// Used to write-protect a page that has just become shared (COW): the frame
/// stays where it is, only the `W` bit goes away, so every existing translation
/// starts faulting without a single byte being copied.
///
/// Returns `false` when `va` is unmapped — a caller that expected a page there
/// has a bug, and silently creating one would hide it.
///
/// # Safety
/// `root_phys` must be a live root table.
pub unsafe fn set_leaf_perms(root_phys: usize, va: usize, perms: Perms) -> bool {
    let mut table = root_phys;
    for level in (0..LEVELS).rev() {
        let index = (va >> VPN_SHIFT[level]) & INDEX_MASK;
        let entry = (*table_at(table)).entry(index);
        if !entry.is_valid() {
            return false;
        }
        if entry.is_leaf() {
            // Keep PPN and A/D; replace only the permission bits.
            let kept = entry.raw() & !(PTE_R | PTE_W | PTE_X | PTE_U);
            (*table_at(table)).set_entry(index, Pte(kept | perms.to_pte()));
            return true;
        }
        table = entry.phys();
    }
    false
}

/// Permissions currently carried by the leaf mapping `va`, if any.
///
/// # Safety
/// `root_phys` must be a live root table.
pub unsafe fn leaf_perms(root_phys: usize, va: usize) -> Option<Perms> {
    translate(root_phys, va).map(|(_, p)| p)
}

/// Drop every cached translation on this hart.
///
/// Mandatory after touching a PTE of the table `satp` currently names: the hart
/// may have cached the old translation, and a COW page that stays writable in
/// the TLB is shared memory corruption that only shows up later.
#[inline]
pub fn flush_tlb() {
    unsafe {
        core::arch::asm!("sfence.vma zero, zero", options(nostack));
    }
}

/// Free a whole address space: every page-table frame under `root_phys`.
///
/// Target frames mapped by [`map_range`] are untouched — free those with
/// whatever owns them.
///
/// # Safety
/// `root_phys` must be the last remaining reference to that address space.
pub unsafe fn free_root(root_phys: usize) {
    free_level(root_phys, LEVELS - 1);
}

/// Recursively release the tables below `table_phys`, then the table itself.
///
/// # Safety
/// `table_phys` must be an exclusively owned page-table frame.
unsafe fn free_level(table_phys: usize, level: usize) {
    let t = &mut *table_at(table_phys);
    if level > 0 {
        for index in 0..ENTRIES {
            let entry = t.entry(index);
            if entry.is_valid() && !entry.is_leaf() {
                free_level(entry.phys(), level - 1);
            }
        }
    }
    free_frame(table_phys);
}

// ---------------------------------------------------------------------------
// User-space helpers
// ---------------------------------------------------------------------------

/// Map a contiguous user image — code and data as one span — as R/W/X + USER.
///
/// # Safety
/// As [`map_range`].
///
/// FIXME: W^X. The loader already knows each ELF segment's true permissions
/// (`MemoryPermissions`), but `MemoryMapper` does not expose them per segment,
/// so M1 maps the whole image read+write+execute. Tighten this once the loader
/// offers a segment iterator: a user process should not be able to write to
/// its own code.
pub unsafe fn map_user_image(root_phys: usize, va: usize, pa: usize, size: usize) -> MapResult {
    map_range(
        root_phys,
        va,
        pa,
        size,
        Perms::READ
            .bitor(Perms::WRITE)
            .bitor(Perms::EXEC)
            .bitor(Perms::USER),
    )
}

/// Map a user stack as read/write + USER — never executable.
///
/// # Safety
/// As [`map_range`].
pub unsafe fn map_user_stack(root_phys: usize, va: usize, pa: usize, size: usize) -> MapResult {
    map_range(root_phys, va, pa, size, Perms::RW_USER)
}

// ---------------------------------------------------------------------------
// User pointer access
// ---------------------------------------------------------------------------
//
// The kernel runs in M-mode, where `satp` does not apply. That is what keeps
// this module simple — and it is exactly why a user pointer must never be
// dereferenced directly. Hand a virtual address to `ptr::copy` and it is read
// as a *physical* address: a syscall like `write(fd, 0x8000_0000, ...)` would
// address kernel RAM, giving any user process a read/write primitive over all
// of physical memory.
//
// So every user pointer is resolved through the address space that owns it,
// and every resolution demands the `U` bit. A mapping without `U` is
// kernel-only and stays out of reach even when its VA resolves.

/// Why a user-memory access was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UserFault {
    /// Unmapped, or mapped without the permission this access needs.
    NotPermitted,
    /// The range runs off the end of the address space.
    Overflow,
}

pub type UserResult<T> = Result<T, UserFault>;

/// Resolve up to `len` bytes at user `va`, requiring `need`.
///
/// Deliberately returns a span within a **single** page: a buffer crossing a
/// page boundary is normally *not* physically contiguous, so callers must
/// re-enter for each page. Assuming contiguity across a boundary is the
/// classic way to corrupt the wrong page.
///
/// # Safety
/// `root_phys` must be a root table built by [`new_root`]; the returned
/// physical address is only safe to touch because the kernel runs untranslated
/// in M-mode.
unsafe fn resolve(
    root_phys: usize,
    va: usize,
    len: usize,
    need: Perms,
) -> UserResult<(usize, usize)> {
    let Some((pa, perms)) = translate(root_phys, va) else {
        return Err(UserFault::NotPermitted);
    };
    // `USER` is not optional: without it the page is kernel-only, and a user
    // process naming its VA must not reach it.
    if !perms.contains(Perms::USER) || !perms.contains(need) {
        return Err(UserFault::NotPermitted);
    }
    let in_page = PAGE_SIZE - (va & (PAGE_SIZE - 1));
    Ok((pa, core::cmp::min(len, in_page)))
}

/// Copy `dst.len()` bytes from user `src_va` into kernel `dst`.
///
/// # Safety
/// As [`resolve`]. `dst` must be kernel memory.
pub unsafe fn copy_from_user(root_phys: usize, dst: &mut [u8], src_va: usize) -> UserResult<()> {
    let mut va = src_va;
    let mut done = 0;
    while done < dst.len() {
        let (pa, n) = resolve(root_phys, va, dst.len() - done, Perms::READ)?;
        ptr::copy_nonoverlapping(pa as *const u8, dst[done..].as_mut_ptr(), n);
        va = va.checked_add(n).ok_or(UserFault::Overflow)?;
        done += n;
    }
    Ok(())
}

/// Copy `src` into user memory at `dst_va`.
///
/// # Safety
/// As [`resolve`]. `src` must be kernel memory.
pub unsafe fn copy_to_user(root_phys: usize, dst_va: usize, src: &[u8]) -> UserResult<()> {
    let mut va = dst_va;
    let mut done = 0;
    while done < src.len() {
        let (pa, n) = resolve(root_phys, va, src.len() - done, Perms::WRITE)?;
        ptr::copy_nonoverlapping(src[done..].as_ptr(), pa as *mut u8, n);
        va = va.checked_add(n).ok_or(UserFault::Overflow)?;
        done += n;
    }
    Ok(())
}

/// Length of the NUL-terminated string at user `va`, capped at `max`.
///
/// Returns [`UserFault::NotPermitted`] if no NUL is found within `max` — an
/// unterminated string is a fault, not a silent truncation, because callers
/// would otherwise use the capped length as if it were the real one.
///
/// # Safety
/// As [`resolve`].
pub unsafe fn user_strnlen(root_phys: usize, va: usize, max: usize) -> UserResult<usize> {
    let mut offset = 0;
    while offset < max {
        let (pa, n) = resolve(root_phys, va + offset, max - offset, Perms::READ)?;
        let slice = core::slice::from_raw_parts(pa as *const u8, n);
        if let Some(hit) = slice.iter().position(|&b| b == 0) {
            return Ok(offset + hit);
        }
        offset += n;
    }
    Err(UserFault::NotPermitted)
}

// ---------------------------------------------------------------------------
// Host unit tests
// ---------------------------------------------------------------------------
//
// The walk/map/unmap/translate logic is pure arithmetic over frames handed out
// by a `FrameAllocator`, so it is testable on the host — which is the only
// automated verification available while the blueos toolchain is unavailable.

// These tests are written for the **host**, not for the kernel's own test
// image. They exercise the walk/map/translate logic against a static arena, and
// they use the ordinary `#[test]` attribute — which pulls in the `test` crate
// and its own `panic_impl`. Compiling them into `kernel_unittest` (a `--test`
// build of the kernel, which already defines a `panic_handler`) is a duplicate
// lang item, so they are excluded on the target they would break.
//
// Run them on the host with:
//   rustc --test kernel/kernel/src/arch/riscv/mmu.rs --edition 2021
#[cfg(all(test, not(target_arch = "riscv64")))]
mod tests {
    use super::*;
    use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    /// Frames in the test arena. Sized so the exhaustion test below needs
    /// strictly more tables than this (a 2 GiB span wants ~1027), while every
    /// other test uses a handful.
    const ARENA_FRAMES: usize = 512;
    /// Static arena standing in for physical memory.
    ///
    /// Wrapped in a `repr(align(4096))` struct on purpose: a bare `[u8; N]`
    /// has alignment 1, so aligning its base up to a page boundary would push
    /// frame `ARENA_FRAMES - 1` past the end of the array.
    #[repr(align(4096))]
    struct Arena([u8; ARENA_FRAMES * PAGE_SIZE]);

    static mut ARENA: Arena = Arena([0; ARENA_FRAMES * PAGE_SIZE]);
    static NEXT_FRAME: AtomicUsize = AtomicUsize::new(0);

    /// Tests share one arena and one registered allocator, but the default
    /// harness runs them in parallel threads. Serialise them and hand each a
    /// fresh arena, so frame allocation counts stay deterministic.
    static TEST_LOCK: AtomicBool = AtomicBool::new(false);

    struct TestGuard;

    impl Drop for TestGuard {
        fn drop(&mut self) {
            TEST_LOCK.store(false, Ordering::SeqCst);
        }
    }

    /// Acquire the arena and reset it to a clean slate.
    fn begin() -> TestGuard {
        while TEST_LOCK
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_err()
        {
            core::hint::spin_loop();
        }
        NEXT_FRAME.store(0, Ordering::SeqCst);
        set_frame_allocator(&TEST_FRAMES);
        TestGuard
    }

    /// Base of the frame arena. `addr_of!` keeps this from creating a shared
    /// reference to the `static mut`.
    fn arena_base() -> usize {
        let raw = unsafe { core::ptr::addr_of!(ARENA) as usize };
        debug_assert!(is_page_aligned(raw), "Arena must be page aligned");
        raw
    }

    struct TestFrames;

    impl FrameAllocator for TestFrames {
        fn alloc_frame(&self) -> Option<usize> {
            let i = NEXT_FRAME.fetch_add(1, Ordering::SeqCst);
            if i >= ARENA_FRAMES {
                return None;
            }
            let phys = arena_base() + i * PAGE_SIZE;
            unsafe { (*table_at(phys)).zero() };
            Some(phys)
        }

        unsafe fn free_frame(&self, _phys: usize) {
            // Leak on purpose: the arena is a fixed bump region, and the tests
            // assert on allocation order, not on recycling.
        }
    }

    static TEST_FRAMES: TestFrames = TestFrames;

    /// Addresses used as "physical" targets. Deliberately not inside the arena
    /// so a bug that maps the wrong thing is visible.
    const TARGET_BASE: usize = 0x8000_0000;
    const VA_BASE: usize = 0x0000_1000;

    #[test]
    fn satp_encoding_round_trips() {
        let root = 0x8000_1000;
        let satp = satp_sv39(root);
        assert_eq!((satp >> 60) & 0xf, SATP_MODE_SV39, "MODE must be Sv39 (8)");
        assert_eq!(satp_root(satp), root, "PPN must round-trip");
        // PPN is 44 bits: anything above 2^56 of physical address is dropped.
        assert_eq!(satp & !((1u64 << 44) - 1), SATP_MODE_SV39 << 60);
    }

    #[test]
    fn pte_bit_layout() {
        let leaf = Pte::leaf(TARGET_BASE, Perms::RW_USER);
        assert!(leaf.is_valid());
        assert!(leaf.is_leaf());
        assert_eq!(leaf.phys(), TARGET_BASE);
        assert!(leaf.perms().contains(Perms::READ));
        assert!(leaf.perms().contains(Perms::WRITE));
        assert!(leaf.perms().contains(Perms::USER));
        assert!(!leaf.perms().contains(Perms::EXEC));
        // A/D are set so we never take an access fault just to age a page.
        assert_ne!(leaf.raw() & PTE_A, 0);
        assert_ne!(leaf.raw() & PTE_D, 0);

        let next = Pte::next_table(TARGET_BASE + 0x1000);
        assert!(next.is_valid());
        assert!(!next.is_leaf(), "a next-level pointer must not look like a leaf");
        assert_eq!(next.phys(), TARGET_BASE + 0x1000);
    }

    #[test]
    fn no_user_bit_means_kernel_only() {
        let leaf = Pte::leaf(TARGET_BASE, Perms::READ);
        assert_eq!(leaf.raw() & PTE_U, 0);
        assert!(!leaf.perms().contains(Perms::USER));
    }

    #[test]
    fn map_then_translate() {
        let _g = begin();
        let root = new_root().expect("root frame");
        unsafe {
            map_range(root, VA_BASE, TARGET_BASE, PAGE_SIZE, Perms::RW_USER).unwrap();
        }
        let (pa, perms) = unsafe { translate(root, VA_BASE) }.expect("mapped page resolves");
        assert_eq!(pa, TARGET_BASE);
        assert_eq!(perms, Perms::RW_USER);

        // Offset within the page is preserved.
        let (pa2, _) = unsafe { translate(root, VA_BASE + 0xabc) }.unwrap();
        assert_eq!(pa2, TARGET_BASE + 0xabc);
    }

    #[test]
    fn unmapped_address_is_none() {
        let _g = begin();
        let root = new_root().unwrap();
        unsafe {
            map_range(root, VA_BASE, TARGET_BASE, PAGE_SIZE, Perms::RW_USER).unwrap();
        }
        assert!(unsafe { translate(root, VA_BASE + PAGE_SIZE) }.is_none());
        // A different, never-touched region.
        assert!(unsafe { translate(root, 0x0040_0000) }.is_none());
    }

    #[test]
    fn multi_page_range_is_contiguous() {
        let _g = begin();
        let root = new_root().unwrap();
        let size = 8 * PAGE_SIZE;
        unsafe {
            map_range(root, VA_BASE, TARGET_BASE, size, Perms::RX_USER).unwrap();
        }
        for i in 0..8 {
            let (pa, perms) = unsafe { translate(root, VA_BASE + i * PAGE_SIZE) }.unwrap();
            assert_eq!(pa, TARGET_BASE + i * PAGE_SIZE);
            assert_eq!(perms, Perms::RX_USER);
        }
        assert!(unsafe { translate(root, VA_BASE + size) }.is_none());
    }

    #[test]
    fn unmap_removes_mapping_and_keeps_neighbours() {
        let _g = begin();
        let root = new_root().unwrap();
        unsafe {
            map_range(root, VA_BASE, TARGET_BASE, 4 * PAGE_SIZE, Perms::RW_USER).unwrap();
        }
        unsafe {
            unmap_range(root, VA_BASE + PAGE_SIZE, 2 * PAGE_SIZE).unwrap();
        }
        // Neighbours survive...
        assert!(unsafe { translate(root, VA_BASE) }.is_some());
        assert!(unsafe { translate(root, VA_BASE + 3 * PAGE_SIZE) }.is_some());
        // ...the unmapped middle does not.
        assert!(unsafe { translate(root, VA_BASE + PAGE_SIZE) }.is_none());
        assert!(unsafe { translate(root, VA_BASE + 2 * PAGE_SIZE) }.is_none());
    }

    #[test]
    fn unaligned_or_empty_range_is_rejected() {
        let _g = begin();
        let root = new_root().unwrap();
        unsafe {
            assert_eq!(
                map_range(root, VA_BASE + 1, TARGET_BASE, PAGE_SIZE, Perms::RW_USER),
                Err(MapError::InvalidRange)
            );
            assert_eq!(
                map_range(root, VA_BASE, TARGET_BASE + 1, PAGE_SIZE, Perms::RW_USER),
                Err(MapError::InvalidRange)
            );
            assert_eq!(
                map_range(root, VA_BASE, TARGET_BASE, 0, Perms::RW_USER),
                Err(MapError::InvalidRange)
            );
            // Leaving the 39-bit space is caught rather than silently wrapped.
            assert_eq!(
                map_range(root, VA_LIMIT - PAGE_SIZE, TARGET_BASE, 2 * PAGE_SIZE, Perms::RW_USER),
                Err(MapError::InvalidRange)
            );
        }
    }

    #[test]
    fn frame_exhaustion_is_reported_not_panicked() {
        let _g = begin();
        let root = new_root().unwrap();
        // A 2 GiB span walks ~1027 page-table frames (root + 2 L1 + 1024 L0),
        // well past the 512-frame arena. The walk must report exhaustion
        // rather than panic, wrap, or silently reuse a frame.
        let huge = 2 * 1024 * 1024 * 1024;
        let res = unsafe { map_range(root, VA_BASE, TARGET_BASE, huge, Perms::RW_USER) };
        assert_eq!(res, Err(MapError::NoMemory));
    }

    #[test]
    fn user_image_and_stack_carry_the_u_bit() {
        let _g = begin();
        let root = new_root().unwrap();
        let stack_va = 0x0001_0000;
        unsafe {
            map_user_image(root, VA_BASE, TARGET_BASE, 2 * PAGE_SIZE).unwrap();
            map_user_stack(root, stack_va, TARGET_BASE + 0x1_0000, PAGE_SIZE).unwrap();
        }

        // Without the U bit the process could not fetch a single instruction
        // once `enter_user` drops to U-mode.
        let (_, image) = unsafe { translate(root, VA_BASE) }.unwrap();
        assert!(image.contains(Perms::USER), "user image must be U-accessible");
        assert!(image.contains(Perms::EXEC));

        let (_, stack) = unsafe { translate(root, stack_va) }.unwrap();
        assert_eq!(stack, Perms::RW_USER);
        assert!(!stack.contains(Perms::EXEC), "a stack must never be executable");
        assert!(!stack.contains(Perms::USER) == false, "stack must be U-accessible");
    }

    #[test]
    fn translate_walks_all_three_levels() {
        let _g = begin();
        let root = new_root().unwrap();
        // 2 MiB apart: the two mappings sit in different L1/L0 tables, so a
        // correct walk is required to reach both.
        let va_far = VA_BASE + 2 * 1024 * 1024;
        unsafe {
            map_range(root, VA_BASE, TARGET_BASE, PAGE_SIZE, Perms::RO_USER).unwrap();
            map_range(root, va_far, TARGET_BASE + 0x10_0000, PAGE_SIZE, Perms::RX_USER).unwrap();
        }
        let (pa_near, near_perms) = unsafe { translate(root, VA_BASE) }.unwrap();
        let (pa_far, far_perms) = unsafe { translate(root, va_far) }.unwrap();
        assert_eq!(pa_near, TARGET_BASE);
        assert_eq!(pa_far, TARGET_BASE + 0x10_0000);
        assert_eq!(near_perms, Perms::RO_USER);
        assert_eq!(far_perms, Perms::RX_USER);
    }

    // --- user pointer access -----------------------------------------------
    //
    // These map *real* frames from the arena: the copy helpers dereference the
    // physical address they resolve, so a fake one (TARGET_BASE) would be a
    // host segfault rather than a test failure.

    #[test]
    fn user_copy_round_trips() {
        let _g = begin();
        let root = new_root().unwrap();
        let frame = TEST_FRAMES.alloc_frame().unwrap();
        unsafe { map_range(root, VA_BASE, frame, PAGE_SIZE, Perms::RW_USER).unwrap() };

        unsafe { copy_to_user(root, VA_BASE, b"hello").unwrap() };
        let mut buf = [0u8; 5];
        unsafe { copy_from_user(root, &mut buf, VA_BASE).unwrap() };
        assert_eq!(&buf, b"hello");
    }

    /// A buffer spanning two pages is only contiguous in *virtual* memory.
    /// Mapping the halves to non-adjacent frames is what catches code that
    /// translates once and then copies linearly.
    #[test]
    fn user_copy_across_non_contiguous_pages() {
        let _g = begin();
        let root = new_root().unwrap();
        // Deliberately skip a frame between the two, so the physical pages
        // backing the pair are not adjacent.
        let first = TEST_FRAMES.alloc_frame().unwrap();
        let _gap = TEST_FRAMES.alloc_frame().unwrap();
        let second = TEST_FRAMES.alloc_frame().unwrap();
        assert_eq!(second - first, 2 * PAGE_SIZE, "pages must be non-adjacent");
        unsafe {
            map_range(root, VA_BASE, first, PAGE_SIZE, Perms::RW_USER).unwrap();
            map_range(root, VA_BASE + PAGE_SIZE, second, PAGE_SIZE, Perms::RW_USER).unwrap();
        }

        // 8 bytes straddling the boundary: 4094 in the first page, 2 in the next.
        let src: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
        let straddle = VA_BASE + PAGE_SIZE - 6;
        unsafe { copy_to_user(root, straddle, &src).unwrap() };

        // Read each half back through its own frame to prove the split landed
        // where it should.
        let tail_of_first = unsafe { core::slice::from_raw_parts(first as *const u8, PAGE_SIZE) };
        assert_eq!(&tail_of_first[PAGE_SIZE - 6..], &src[0..6]);
        let head_of_second = unsafe { core::slice::from_raw_parts(second as *const u8, 2) };
        assert_eq!(head_of_second, &src[6..8]);

        let mut back = [0u8; 8];
        unsafe { copy_from_user(root, &mut back, straddle).unwrap() };
        assert_eq!(back, src);
    }

    /// The security property: a mapping without the `U` bit is kernel-only, so
    /// a user process naming its address must not reach it. Without this check
    /// `write(fd, <kernel address>, ...)` would read or write kernel memory.
    #[test]
    fn user_copy_refuses_kernel_only_mapping() {
        let _g = begin();
        let root = new_root().unwrap();
        let frame = TEST_FRAMES.alloc_frame().unwrap();
        let kernel_only = Perms::READ.bitor(Perms::WRITE); // no USER
        unsafe { map_range(root, VA_BASE, frame, PAGE_SIZE, kernel_only).unwrap() };

        let mut buf = [0u8; 4];
        assert_eq!(
            unsafe { copy_from_user(root, &mut buf, VA_BASE) },
            Err(UserFault::NotPermitted)
        );
        assert_eq!(
            unsafe { copy_to_user(root, VA_BASE, b"x") },
            Err(UserFault::NotPermitted)
        );
    }

    #[test]
    fn user_copy_refuses_unmapped_and_read_only() {
        let _g = begin();
        let root = new_root().unwrap();

        let mut buf = [0u8; 4];
        assert_eq!(
            unsafe { copy_from_user(root, &mut buf, VA_BASE) },
            Err(UserFault::NotPermitted),
            "unmapped address must fault"
        );

        let frame = TEST_FRAMES.alloc_frame().unwrap();
        unsafe { map_range(root, VA_BASE, frame, PAGE_SIZE, Perms::RO_USER).unwrap() };
        assert_eq!(
            unsafe { copy_to_user(root, VA_BASE, b"x") },
            Err(UserFault::NotPermitted),
            "writing a read-only user page must fault"
        );
        assert_eq!(
            unsafe { copy_from_user(root, &mut buf, VA_BASE) },
            Ok(()),
            "reading it is fine"
        );
    }

    #[test]
    fn user_string_length_is_bounded() {
        let _g = begin();
        let root = new_root().unwrap();
        let frame = TEST_FRAMES.alloc_frame().unwrap();
        unsafe { map_range(root, VA_BASE, frame, PAGE_SIZE, Perms::RW_USER).unwrap() };

        unsafe { copy_to_user(root, VA_BASE, b"abc\0def").unwrap() };
        assert_eq!(unsafe { user_strnlen(root, VA_BASE, 16) }, Ok(3));
        // No NUL within the cap is a fault, not a silent truncation: callers
        // would otherwise treat the capped length as the real one.
        assert_eq!(
            unsafe { user_strnlen(root, VA_BASE, 3) },
            Err(UserFault::NotPermitted)
        );
    }
}
