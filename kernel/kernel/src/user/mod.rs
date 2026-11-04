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

//! User address spaces, image loading, and the U-mode entry path.
//!
//! # What this module owns
//!
//! - **Address spaces.** [`AddressSpace`] holds one Sv39 root table plus the
//!   *data* frames it maps. The distinction matters: [`crate::arch::riscv::mmu`]
//!   owns page-table frames and frees them in `free_root`; the frames a segment
//!   or a stack is mapped onto are allocated here and freed here.
//! - **Two kinds of "mapped".** A [`Region`] says an address *may* be used and
//!   with what permissions; `AddressSpace::pages` says a frame actually exists.
//!   They diverge because `mmap` does not allocate up front: a region with no
//!   pages behind it is valid, and the first touch fills it in
//!   ([`AddressSpace::fault_in`]).
//! - **Loading.** [`AddressSpace::load`] turns an ELF byte slice into a mapped
//!   image: per-segment permissions from the ELF (`W^X` enforced), relocations
//!   applied through the *physical* frames, and a stack at a fixed address.
//! - **Entering user mode.** [`spawn`] creates an ordinary kernel thread whose
//!   body drops to U-mode via [`crate::arch::riscv::enter_user`] and never
//!   returns. [`fork`] is the other door: its thread restores a *saved trap
//!   frame* through `enter_user_from_frame`, so the child continues the
//!   parent's program rather than starting a new one.
//! - **Copy-on-write.** [`AddressSpace::fork_clone`] shares every frame and
//!   strips `W` from both sides; the frames with more than one holder are
//!   counted in [`SHARED_FRAMES`], and [`drop_frame_ref`] is the only way a
//!   frame goes back to the allocator.
//!
//! # Why a thread and not a "process switch"
//!
//! There is no separate user scheduler: [`crate::scheduler`] schedules
//! *threads*, and `enter_user` is just a privileged instruction sequence. A
//! user process is a thread executing in U-mode with a non-zero `satp`. A trap
//! from U-mode is routed correctly because `trap.rs` swaps to the kernel stack
//! through `mscratch`, so nothing else in the kernel needs to know that user
//! processes exist.
//!
//! # Frame ownership
//!
//! [`AddressSpace`] holds a *reference* to each data frame it maps and releases
//! it in [`AddressSpace::release`] through [`drop_frame_ref`] — not with a bare
//! free, because after a `fork` the same frame belongs to two spaces. The space
//! itself lives in the owning [`Process`], which is what lets the trap path and
//! `exit` find it and hand every frame back.

use crate::{
    allocator::frame::{alloc_frame_phys, free_frame_phys},
    arch::riscv::mmu::{self, MapError, Perms, PAGE_SIZE},
    error::code,
    process::{current_process, Process},
    thread::Thread,
    time::Tick,
};
use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use blueos_infra::no_let_underscore::IgnoreResult;
use core::sync::atomic::{AtomicUsize, Ordering};
use spin::Mutex;

pub mod programs;

/// Highest address a user stack may reach. 4 MiB is far above anything a small
/// image occupies at its link address and far below the Sv39 limit, so the two
/// never meet regardless of how fat the image grows.
pub const USER_STACK_TOP: usize = 0x0040_0000;
/// Size of the user stack mapping.
pub const USER_STACK_SIZE: usize = 64 * 1024;

/// `AT_*` keys of the auxiliary vector, numbered as the rv64 ELF psABI does.
///
/// Only the six a program cannot guess are filled in. `AT_PHDR` is the one that
/// makes a program interpreter possible at all: after `execve` the file is
/// closed, so the headers exist only in memory, and this is the only pointer to
/// them.
pub const AT_NULL: usize = 0;
pub const AT_PHDR: usize = 3;
pub const AT_PHENT: usize = 4;
pub const AT_PHNUM: usize = 5;
pub const AT_PAGESZ: usize = 6;
pub const AT_BASE: usize = 7;
pub const AT_ENTRY: usize = 9;

/// Default link address for a non-PIE image, mirrored by the user-program
/// linker script. Kept here so a mismatch shows up as a load error instead of
/// as a fault at the first instruction.
pub const USER_IMAGE_BASE: usize = 0x0001_0000;

/// The signal trampoline every user address space gets.
///
/// A signal handler runs in U-mode and returns with `ret`, which lands here.
/// The two instructions issue `sigreturn` as an ecall, and the kernel restores
/// the interrupted register state from the frame the delivery built. Keeping
/// the stub in its own read-execute page (rather than on the writable user
/// stack) means a program cannot rewrite the code that returns from its
/// handlers.
///
/// The address sits one page above the stack, in the gap before `MMAP_BASE`.
pub const SIGTRAMPOLINE_VA: usize = USER_STACK_TOP + PAGE_SIZE;

/// The stub a U-mode thread returns to when its entry function returns.
///
/// A thread started by `create_thread()` from U-mode begins at a function the
/// caller chose, so the kernel cannot know whether that function returns. The
/// return address is pointed at this page instead of being left at zero: the
/// stub issues `exit_thread`, which retires the calling thread without taking
/// the rest of the process with it (that is `exit_group`'s job).
///
/// `ra` is the caller's to overwrite, so a thread that wants a different exit
/// path can simply not use it. The page is read-execute for the same reason as
/// the signal trampoline: user code must not be able to patch its own exit.
pub const THREAD_EXIT_TRAMPOLINE_VA: usize = SIGTRAMPOLINE_VA + PAGE_SIZE;

/// Encodes `addi rd, x0, imm` (opcode `OP-IMM`, funct3 0), for the 12-bit
/// immediate the trampoline needs.
const fn addi_x0(rd: u32, imm: i32) -> u32 {
    ((imm as u32 & 0xfff) << 20) | (rd << 7) | 0x13
}

/// Encodes `ecall` (environment call from U-mode).
const ECALL_INSN: u32 = 0x0000_0073;

/// Encodes `jal x0, 0`, i.e. an unconditional jump to itself. The backstop for
/// a trampoline whose syscall unexpectedly returns.
const SPIN_INSN: u32 = 0x0000_006f;

/// First address handed out by `mmap(0, ...)`.
///
/// Above every load address a small image uses and above the stack at 4 MiB, so
/// a growable heap and a growable stack approach each other from 8 MiB and from
/// below without meeting.
pub const MMAP_BASE: usize = 0x0080_0000;

/// Top of the mmap area, i.e. how far a heap may grow.
pub const MMAP_LIMIT: usize = 0x2000_0000;

/// Largest image `exec` will read. 16 MiB: comfortably above a static Rust
/// binary, far below the `mmap` limit, and small enough that a corrupt size
/// field cannot exhaust the frame allocator in one allocation.
pub const MAX_IMAGE: usize = 16 * 1024 * 1024;

/// Why an image could not be started.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoadError {
    /// The ELF parser rejected the image.
    BadImage(&'static str),
    /// The image does not fit the address range a user process may occupy.
    OutOfRange,
    /// The frame allocator could not supply a page.
    NoMemory,
    /// The mapping itself failed (usually a page-table conflict).
    Map(MapError),
    /// The image has no entry point inside any loadable segment.
    NoEntry,
    /// The image asks for a program interpreter (`PT_INTERP`), which this
    /// kernel cannot provide yet.
    NeedsInterp(String),
}

impl From<MapError> for LoadError {
    fn from(e: MapError) -> Self {
        LoadError::Map(e)
    }
}

impl LoadError {
    /// Map a load failure onto the errno `execve` should report.
    pub fn to_errno(&self) -> isize {
        match self {
            // A bad ELF is not a "bad argument" in the sense of a malformed
            // pointer; Linux reports ENOEXEC for both. This kernel's table has
            // no ENOEXEC yet, so EINVAL is the honest nearest.
            LoadError::BadImage(_) | LoadError::NoEntry | LoadError::OutOfRange => {
                code::EINVAL.to_errno() as isize
            }
            LoadError::NoMemory | LoadError::Map(MapError::NoMemory) => {
                code::ENOMEM.to_errno() as isize
            }
            LoadError::Map(_) => code::EINVAL.to_errno() as isize,
            // The image is fine; the kernel is what is missing a piece.
            LoadError::NeedsInterp(_) => code::EINVAL.to_errno() as isize,
        }
    }
}

/// One (virtual page, physical frame) pair the address space owns.
///
/// Kept as a flat list rather than inferred from the page tables because the
/// tables only record what is *mapped*, not what is *owned*: a shared read-only
/// page and a private one look identical there, and freeing the wrong one
/// corrupts whoever else maps it.
#[derive(Clone, Copy)]
struct OwnedPage {
    va: usize,
    pa: usize,
}

/// A range of user addresses the process is allowed to touch, and how.
///
/// This is the piece an eager loader does not need: with every page
/// materialised up front, "is this address valid?" is answered by the page
/// table itself. Once mapping is on demand that is circular — the fault has to
/// be resolved *before* there is a translation to consult — so the intent has
/// to be recorded separately from the mapping.
#[derive(Clone)]
struct Region {
    start: usize,
    end: usize,
    perms: Perms,
    /// `MAP_SHARED` file mappings keep `W` on both sides of a `fork`; every
    /// other region becomes copy-on-write.
    shared: bool,
}

/// Process credentials.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Credentials {
    pub uid: u32,
    pub gid: u32,
    pub euid: u32,
    pub egid: u32,
}

impl Credentials {
    /// The boot identity. Nothing runs as anyone else until a `setuid` says so.
    pub const ROOT: Self = Credentials {
        uid: 0,
        gid: 0,
        euid: 0,
        egid: 0,
    };
}

/// A loaded user image: page tables, mapped frames, and where to start.
pub struct AddressSpace {
    root: usize,
    pages: Vec<OwnedPage>,
    regions: Vec<Region>,
    entry: usize,
    stack_top: usize,
    /// Next address `mmap(0, ...)` will hand out. Grows upward; see
    /// [`MMAP_BASE`].
    map_next: usize,
    name: String,
    /// Where the program header table landed, for `AT_PHDR`.
    phdr: Option<usize>,
    phnum: usize,
    phentsize: usize,
    /// `sp` for the program's first instruction: the base of the
    /// `argc/argv/envp/auxv` block built at load time.
    startup_sp: usize,
    /// Process identity; starts as `ROOT` and is the only field `setuid`
    /// touches.
    cred: Credentials,
}

impl core::fmt::Debug for AddressSpace {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AddressSpace")
            .field("name", &self.name)
            .field("root", &format_args!("0x{:x}", self.root))
            .field("entry", &format_args!("0x{:x}", self.entry))
            .field("pages", &self.pages.len())
            .finish()
    }
}

impl AddressSpace {
    /// Parse and map `bytes` as a user image called `name`.
    ///
    /// On failure, everything already allocated is released before returning —
    /// a half-mapped image must not survive as a leak, and callers retry.
    pub fn load(name: &str, bytes: &[u8]) -> Result<Self, LoadError> {
        let image = crate::elf::parse(bytes).map_err(|e| LoadError::BadImage(e.0))?;

        // A dynamic image's `e_entry` belongs to `ld.so`, not to the program.
        // Running it here would start at an address the image never mapped.
        if let Some(interp) = image.interp.as_deref() {
            crate::kearly_println!(
                "user: \"{}\" is dynamically linked (PT_INTERP = {}); no loader yet",
                name,
                interp
            );
            return Err(LoadError::NeedsInterp(interp.to_string()));
        }

        // A PIE image can be based anywhere; a fixed image must land where it
        // was linked. Either way the whole image has to sit below the stack,
        // or the stack would overwrite it as it grows down.
        let bias = if image.is_pie {
            USER_IMAGE_BASE.wrapping_sub(image.vaddr_min())
        } else {
            0
        };
        let image_start = image.vaddr_min().wrapping_add(bias);
        let image_end = image.vaddr_max().saturating_add(bias);
        if image_start == 0 || image_end > USER_STACK_TOP || image_end <= image_start {
            return Err(LoadError::OutOfRange);
        }

        let Some(root) = mmu::new_root() else {
            return Err(LoadError::NoMemory);
        };
        let mut space = Self {
            root,
            pages: Vec::new(),
            regions: Vec::new(),
            entry: image.entry.wrapping_add(bias),
            stack_top: USER_STACK_TOP,
            map_next: MMAP_BASE,
            name: name.to_string(),
            phdr: image.phdr_vaddr.map(|a| a.wrapping_add(bias)),
            phnum: image.phnum,
            phentsize: image.phentsize,
            // Replaced by `build_startup` before the image runs; a non-zero
            // value here would be a lie, and 0 is a guarded address anyway.
            startup_sp: 0,
            cred: Credentials::ROOT,
        };

        // Any error past this point must release what was mapped, including
        // the root table: `load` has no owner to hand a partial space to.
        let result = space
            .map_image(&image, bias, bytes)
            .and_then(|()| space.map_stack())
            .and_then(|()| space.map_trampoline());
        if let Err(e) = result {
            space.release();
            return Err(e);
        }
        Ok(space)
    }

    fn map_image(
        &mut self,
        image: &crate::elf::Image,
        bias: usize,
        bytes: &[u8],
    ) -> Result<(), LoadError> {
        for seg in &image.segments {
            let seg_start = seg.vaddr.wrapping_add(bias);
            let seg_end = seg_start + seg.memsz;
            let page_start = seg_start & !(PAGE_SIZE - 1);
            let page_end = seg_end.div_ceil(PAGE_SIZE) * PAGE_SIZE;
            if page_end <= page_start {
                return Err(LoadError::OutOfRange);
            }
            let perms = perms_from_elf(seg.perms);
            // Record the span even though every page is mapped below: `fork`
            // copies the permission claims, not the frames.
            self.regions.push(Region {
                start: page_start,
                end: page_end,
                perms,
                shared: false,
            });

            for va in (page_start..page_end).step_by(PAGE_SIZE) {
                let pa = alloc_frame_phys().ok_or(LoadError::NoMemory)?;
                if let Err(e) = unsafe { mmu::map_range(self.root, va, pa, PAGE_SIZE, perms) } {
                    // The frame is not yet reachable from the table, so it is
                    // safe to hand back before bailing out.
                    unsafe { free_frame_phys(pa) };
                    return Err(e.into());
                }
                self.pages.push(OwnedPage { va, pa });
            }

            // Copy the file bytes through the *physical* frames: writing via
            // the virtual address would mean switching `satp` first, and the
            // kernel is not translated, so `seg_start` there is just a number.
            self.copy_into(seg_start, &bytes[seg.offset..seg.offset + seg.filesz])
                .map_err(|_| LoadError::OutOfRange)?;
        }

        // Relocations last: they may point at any segment, and writing them
        // before the bytes are in place would be overwritten by the copy.
        for reloc in &image.relocs {
            let va = reloc.offset.wrapping_add(bias);
            let value = (bias as i64).wrapping_add(reloc.addend) as usize;
            self.write_usize(va, value)
                .map_err(|_| LoadError::OutOfRange)?;
        }

        if !self.contains(self.entry) {
            return Err(LoadError::NoEntry);
        }
        Ok(())
    }

    fn map_stack(&mut self) -> Result<(), LoadError> {
        let base = USER_STACK_TOP - USER_STACK_SIZE;
        for va in (base..USER_STACK_TOP).step_by(PAGE_SIZE) {
            let pa = alloc_frame_phys().ok_or(LoadError::NoMemory)?;
            if let Err(e) = unsafe { mmu::map_range(self.root, va, pa, PAGE_SIZE, Perms::RW_USER) } {
                unsafe { free_frame_phys(pa) };
                return Err(e.into());
            }
            self.pages.push(OwnedPage { va, pa });
        }
        self.regions.push(Region {
            start: base,
            end: USER_STACK_TOP,
            perms: Perms::RW_USER,
            shared: false,
        });
        Ok(())
    }

    /// Maps the signal trampoline stub described by [`SIGTRAMPOLINE_VA`].
    ///
    /// Every address space gets one, because any thread can take a signal.
    /// The two instructions are `addi a7, x0, NR_SigReturn; ecall`; the page
    /// is read-execute only so a buggy or hostile program cannot patch the
    /// return path away.
    fn map_trampoline(&mut self) -> Result<(), LoadError> {
        self.map_stub(
            SIGTRAMPOLINE_VA,
            &[
                addi_x0(17, blueos_header::syscalls::NR::SigReturn as i32),
                ECALL_INSN,
            ],
        )?;
        self.map_stub(
            THREAD_EXIT_TRAMPOLINE_VA,
            &[
                addi_x0(17, blueos_header::syscalls::NR::ExitThread as i32),
                ECALL_INSN,
                SPIN_INSN,
            ],
        )
    }

    /// Map one read-execute page at `va` holding `insns`.
    ///
    /// Shared by the signal and thread-exit trampolines: both are tiny stubs
    /// that must live where user code cannot rewrite them.
    fn map_stub(&mut self, va: usize, insns: &[u32]) -> Result<(), LoadError> {
        let pa = alloc_frame_phys().ok_or(LoadError::NoMemory)?;
        if let Err(e) = unsafe { mmu::map_range(self.root, va, pa, PAGE_SIZE, Perms::RX_USER) } {
            unsafe { free_frame_phys(pa) };
            return Err(e.into());
        }
        unsafe {
            core::ptr::copy_nonoverlapping(insns.as_ptr(), pa as *mut u32, insns.len());
            // The first fetch of this page happens on another privilege level,
            // possibly on another hart; make sure it sees the stores.
            core::arch::asm!("fence.i", options(nostack, preserves_flags));
        }
        self.pages.push(OwnedPage { va, pa });
        self.regions.push(Region {
            start: va,
            end: va + PAGE_SIZE,
            perms: Perms::RX_USER,
            shared: false,
        });
        Ok(())
    }

    /// Lay out the `argc/argv/envp/auxv` block a program's first instruction
    /// expects, and return the `sp` that points at it.
    ///
    /// The layout is the rv64 psABI's, from the top of the stack down:
    ///
    /// ```text
    /// sp -> argc
    ///       argv[0..argc], NULL
    ///       envp[0..envc], NULL
    ///       auxv (key, value) pairs, AT_NULL
    ///       ... padding ...
    ///       string bytes
    /// ```
    pub fn build_startup(&mut self, argv: &[&str], envp: &[&str]) -> Result<usize, LoadError> {
        let stack_base = USER_STACK_TOP - USER_STACK_SIZE;
        let w = core::mem::size_of::<usize>();
        let mut top = USER_STACK_TOP;

        // 1. Strings, highest first. Each `argv[i]` will point into this area,
        //    so the addresses are collected while the bytes are written.
        let mut str_at = Vec::with_capacity(argv.len() + envp.len());
        for s in argv.iter().chain(envp.iter()) {
            let bytes = s.as_bytes();
            top = top
                .checked_sub(bytes.len() + 1)
                .filter(|&a| a >= stack_base)
                .ok_or(LoadError::OutOfRange)?;
            self.copy_into(top, bytes).map_err(|_| LoadError::OutOfRange)?;
            self.copy_into(top + bytes.len(), &[0])
                .map_err(|_| LoadError::OutOfRange)?;
            str_at.push(top);
        }

        // 2. Reserve the block below the strings. Its size has to be known
        //    before `sp` can be aligned, which is why the words are counted
        //    here rather than discovered while writing.
        let aux_pairs = 5 + usize::from(self.phdr.is_some());
        let mut words = 1                    // argc
            + argv.len() + 1                 // argv[], NULL
            + envp.len() + 1                 // envp[], NULL
            + 2 * (aux_pairs + 1); // auxv pairs, AT_NULL
        if !words.is_multiple_of(2) {
            words += 1; // an odd word count would break the 16-byte alignment
        }
        let sp = (top & !0xf)
            .checked_sub(words * w)
            .filter(|&a| a >= stack_base)
            .ok_or(LoadError::OutOfRange)?;

        // 3. Fill it in, lowest address first.
        self.write_word(sp, argv.len())?;
        let mut at = sp + w;
        for p in &str_at[..argv.len()] {
            self.write_word(at, *p)?;
            at += w;
        }
        self.write_word(at, 0)?;
        at += w;
        for p in &str_at[argv.len()..] {
            self.write_word(at, *p)?;
            at += w;
        }
        self.write_word(at, 0)?;
        at += w;

        // `AT_NULL` terminates the vector; the order before it is not
        // significant, but keeping it stable makes a hexdump readable.
        if let Some(phdr) = self.phdr {
            at = self.write_aux(at, AT_PHDR, phdr)?;
        }
        at = self.write_aux(at, AT_PAGESZ, PAGE_SIZE)?;
        at = self.write_aux(at, AT_PHNUM, self.phnum)?;
        at = self.write_aux(at, AT_PHENT, self.phentsize)?;
        at = self.write_aux(at, AT_ENTRY, self.entry)?;
        at = self.write_aux(at, AT_BASE, 0)?;
        self.write_aux(at, AT_NULL, 0).ignore_result();

        self.startup_sp = sp;
        Ok(sp)
    }

    /// `sp` to hand the program: the base of the block `build_startup` wrote.
    pub fn startup_sp(&self) -> usize {
        self.startup_sp
    }

    fn write_word(&mut self, va: usize, value: usize) -> Result<(), LoadError> {
        self.copy_into(va, &value.to_ne_bytes())
            .map_err(|_| LoadError::OutOfRange)
    }

    fn write_aux(&mut self, at: usize, key: usize, value: usize) -> Result<usize, LoadError> {
        let w = core::mem::size_of::<usize>();
        self.write_word(at, key)?;
        self.write_word(at + w, value)?;
        Ok(at + 2 * w)
    }

    /// Permission claim covering `va`, if any.
    ///
    /// Searched newest-first: `mmap` appends, and a later region that overlaps
    /// an earlier one is the one that should win.
    fn region_at(&self, va: usize) -> Option<&Region> {
        self.regions
            .iter()
            .rev()
            .find(|r| va >= r.start && va < r.end)
    }

    /// Physical address backing `va`, if this space mapped it.
    fn phys_of(&self, va: usize) -> Option<usize> {
        let page = va & !(PAGE_SIZE - 1);
        self.pages
            .iter()
            .find(|p| p.va == page)
            .map(|p| p.pa + (va - page))
    }

    fn contains(&self, va: usize) -> bool {
        self.phys_of(va).is_some()
    }

    /// Copy `data` to `va`, page by page, through whatever frame each page
    /// landed on.
    ///
    /// The image's pages are not contiguous in physical memory — the buddy
    /// allocator has no reason to hand out adjacent frames — so this cannot be
    /// one `copy_nonoverlapping`.
    fn copy_into(&mut self, va: usize, data: &[u8]) -> Result<(), MapError> {
        let mut done = 0usize;
        while done < data.len() {
            let cur = va + done;
            let pa = self.phys_of(cur).ok_or(MapError::InvalidRange)?;
            let in_page = PAGE_SIZE - (cur & (PAGE_SIZE - 1));
            let n = core::cmp::min(in_page, data.len() - done);
            unsafe {
                core::ptr::copy_nonoverlapping(data[done..].as_ptr(), pa as *mut u8, n);
            }
            done += n;
        }
        Ok(())
    }

    fn write_usize(&mut self, va: usize, value: usize) -> Result<(), MapError> {
        let pa = self.phys_of(va).ok_or(MapError::InvalidRange)?;
        // A relocation is 8 bytes wide and the loader guarantees the image is
        // 8-byte aligned, so it never straddles a page boundary.
        unsafe { (pa as *mut usize).write(value) };
        Ok(())
    }

    /// Root table physical address, i.e. what `satp` must name.
    pub fn root(&self) -> usize {
        self.root
    }

    pub fn entry(&self) -> usize {
        self.entry
    }

    pub fn stack_top(&self) -> usize {
        self.stack_top
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn cred(&self) -> Credentials {
        self.cred
    }

    /// Frames currently mapped by this space.
    pub fn page_count(&self) -> usize {
        self.pages.len()
    }

    /// Tear the space down: unmap everything, free the data frames, then free
    /// the page tables themselves.
    ///
    /// Order matters. `free_root` walks the tables; unmapping first means it
    /// sweeps already-empty tables, and freeing the data frames only after the
    /// mappings are gone means no frame is released while still reachable.
    ///
    /// Idempotent, because [`Drop`] calls it: the explicit call in an error
    /// path must not be followed by a second free.
    pub fn release(&mut self) {
        if self.root == 0 {
            return;
        }
        for page in &self.pages {
            unsafe {
                mmu::unmap_range(self.root, page.va, PAGE_SIZE).ignore_result();
            }
        }
        for page in &self.pages {
            drop_frame_ref(page.pa);
        }
        self.pages.clear();
        self.regions.clear();
        let root = core::mem::replace(&mut self.root, 0);
        unsafe { mmu::free_root(root) };
    }
}

impl Drop for AddressSpace {
    fn drop(&mut self) {
        self.release();
    }
}

// ---------------------------------------------------------------------------
// Copy-on-write bookkeeping
// ---------------------------------------------------------------------------
//
// A `fork` does not copy memory; it makes two page tables point at the same
// frames and marks both read-only. The first write from either side faults, and
// the fault handler copies that one page. The only thing a `Vec<OwnedPage>` per
// space cannot answer is "may I free this?" — and getting that wrong is the
// classic double free that shows up as corruption in an unrelated process.

static SHARED_FRAMES: Mutex<BTreeMap<usize, usize>> = Mutex::new(BTreeMap::new());

/// Record one more holder of `pa`.
fn share_frame(pa: usize) {
    *SHARED_FRAMES.lock().entry(pa).or_insert(1) += 1;
}

/// Release one holder of `pa`, freeing the frame when it was the last.
fn drop_frame_ref(pa: usize) {
    let last = {
        let mut t = SHARED_FRAMES.lock();
        match t.get_mut(&pa) {
            Some(n) if *n > 1 => {
                *n -= 1;
                false
            }
            Some(_) => {
                t.remove(&pa);
                true
            }
            None => true,
        }
    };
    if last {
        unsafe { free_frame_phys(pa) };
    }
}

fn frame_is_shared(pa: usize) -> bool {
    SHARED_FRAMES.lock().contains_key(&pa)
}

/// Translate an ELF `p_flags` mask into page-table permissions.
///
/// `USER` is always set: these pages exist to be reached from U-mode, and a
/// segment without it would fault on its own first instruction.
fn perms_from_elf(flags: u32) -> Perms {
    let mut out = Perms::USER;
    if flags & crate::elf::PF_R != 0 {
        out = out.bitor(Perms::READ);
    }
    if flags & crate::elf::PF_W != 0 {
        out = out.bitor(Perms::WRITE);
    }
    if flags & crate::elf::PF_X != 0 {
        out = out.bitor(Perms::EXEC);
    }
    out
}

// ---------------------------------------------------------------------------
// satp and the scheduler hand-off
// ---------------------------------------------------------------------------

/// `satp` as the CPU currently has it.
///
/// While user code runs this names its address space; while the kernel runs in
/// M-mode it is whatever the last user process left behind (M-mode is never
/// translated, so the kernel does not care). Reading the CSR rather than a
/// process field keeps the answer exact: it is the table the hardware is
/// actually using, which is precisely what a user-pointer check must consult.
pub fn current_satp() -> usize {
    let v: usize;
    unsafe { core::arch::asm!("csrr {}, satp", out(reg) v, options(nostack, nomem)) };
    v
}

/// Root table of the address space user code is currently running in, if any.
pub fn current_root() -> Option<usize> {
    let satp = current_satp();
    if satp == 0 {
        None
    } else {
        Some(mmu::satp_root(satp as u64))
    }
}

/// Install an `satp` value. Safe only in M-mode: it affects the *next* entry to
/// U-mode, never the instruction stream that executes.
fn set_satp(satp: u64) {
    unsafe {
        core::arch::asm!(
            "csrw satp, {satp}",
            // Flush the TLB for every address, on every ASID. Without this the
            // hart may keep resolving through the previous process's entries —
            // the exact failure mode where a new program reads its own old
            // text.
            "sfence.vma zero, zero",
            satp = in(reg) satp,
            options(nostack),
        );
    }
}

/// Stop translating through whatever table `satp` names.
///
/// Called when a user process ends. Without it the next thread to run inherits
/// the dead process's view of memory, which is how two processes end up sharing
/// an address space by accident.
pub fn drop_satp() {
    set_satp(0);
}

/// Point `satp` at the address space of `next`, or at nothing.
///
/// Called by the scheduler immediately before it restores a thread's context.
/// Without this a second user process would return from its own trap into the
/// *first* process's page tables — each process would see the other's memory,
/// and neither would see its own.
pub fn switch_satp_for(next: &Thread) {
    let want = next
        .process()
        .and_then(|p| p.mm_root())
        .map_or(0, mmu::satp_sv39);
    if want != current_satp() as u64 {
        set_satp(want);
    }
}

// ---------------------------------------------------------------------------
// Address-space operations on the current process
// ---------------------------------------------------------------------------

/// Run `f` with the calling thread's address space locked.
///
/// `None` means "kernel thread", which is the honest answer for every thread
/// that never entered U-mode.
fn with_current_space<R>(f: impl FnOnce(&mut AddressSpace) -> R) -> Option<R> {
    let proc = current_process()?;
    let mut mm = proc.mm().irqsave_lock();
    mm.as_mut().map(f)
}

impl AddressSpace {
    /// Resolve a fault on `va` that needs `need`, by materialising or copying
    /// exactly one page.
    ///
    /// Returns `false` for anything that is not a legitimate demand-paging or
    /// COW miss — an address outside every region, a write to a read-only
    /// segment, a read of a page that is already mapped (nothing to fix, so the
    /// fault is real). The caller turns `false` into process retirement, which
    /// is what keeps a wild pointer inside the process that made it.
    ///
    /// Frames come back zeroed from the allocator, so a fresh anonymous page
    /// needs no `memset`.
    pub fn fault_in(&mut self, va: usize, need: Perms) -> bool {
        let page = va & !(PAGE_SIZE - 1);
        // Already satisfied: `fault_in` is also used as "make sure this is
        // there" from the syscall copy helpers, which re-run over a range that
        // may be entirely mapped. Touching every page twice must not turn into
        // a fault.
        if let Some((_, perms)) = unsafe { mmu::translate(self.root, page) } {
            if perms.contains(need) {
                return true;
            }
        }
        let Some(region) = self.region_at(va) else {
            return false;
        };
        let want = region.perms;
        if !want.contains(need) {
            return false;
        }

        match self.phys_of(page) {
            // Not mapped yet: this is plain demand paging.
            None => {
                let Some(pa) = alloc_frame_phys() else {
                    return false;
                };
                if let Err(e) = unsafe { mmu::map_range(self.root, page, pa, PAGE_SIZE, want) } {
                    unsafe { free_frame_phys(pa) };
                    crate::kearly_println!("user: fault-in 0x{:x} failed: {:?}", page, e);
                    return false;
                }
                self.pages.push(OwnedPage { va: page, pa });
                true
            }
            // Mapped but the access still faulted. Only one case is fixable: a
            // write to a page that is read-only *because it is shared*.
            Some(old) => {
                if !need.contains(Perms::WRITE) || !frame_is_shared(old) {
                    return false;
                }
                let Some(fresh) = alloc_frame_phys() else {
                    return false;
                };
                unsafe {
                    core::ptr::copy_nonoverlapping(old as *const u8, fresh as *mut u8, PAGE_SIZE);
                }
                // Repoint the leaf. `map_range` overwrites an existing level-0
                // entry, which is what turns the shared read-only mapping into
                // a private writable one without disturbing the parent's.
                if let Err(e) = unsafe { mmu::map_range(self.root, page, fresh, PAGE_SIZE, want) } {
                    unsafe { free_frame_phys(fresh) };
                    crate::kearly_println!("user: COW 0x{:x} failed: {:?}", page, e);
                    return false;
                }
                for p in self.pages.iter_mut() {
                    if p.va == page {
                        p.pa = fresh;
                    }
                }
                drop_frame_ref(old);
                true
            }
        }
    }

    /// Deep-copy the *address space* for `fork`, sharing every frame
    /// copy-on-write.
    ///
    /// Nothing is copied: the child's tables point at the parent's frames and
    /// both sides lose `W`. The first write on either side faults and
    /// [`AddressSpace::fault_in`] clones that single page.
    ///
    /// The parent is write-protected in place, so its own next write faults
    /// too — that is not a wart, it is the mechanism. It also means this must
    /// run with the parent stopped in a syscall, which is where `fork` is
    /// called from.
    pub fn fork_clone(&mut self, name: &str) -> Result<Self, LoadError> {
        let root = mmu::new_root().ok_or(LoadError::NoMemory)?;
        let mut child = Self {
            root,
            pages: Vec::new(),
            regions: self.regions.clone(),
            entry: self.entry,
            stack_top: self.stack_top,
            map_next: self.map_next,
            name: name.to_string(),
            phdr: self.phdr,
            phnum: self.phnum,
            phentsize: self.phentsize,
            startup_sp: self.startup_sp,
            // The child is the same identity as the parent until it calls
            // `setuid`.
            cred: self.cred,
        };

        let result = (|| -> Result<(), LoadError> {
            for page in &self.pages {
                let parent_perms =
                    unsafe { mmu::leaf_perms(self.root, page.va) }.ok_or(LoadError::OutOfRange)?;
                // A `MAP_SHARED` page must *not* be write-protected: sharing is
                // the whole point, so both sides keep `W` and keep pointing at
                // the same frame. Everything else drops `W` and lets the first
                // store clone it.
                let is_shared_mapping = self.region_at(page.va).is_some_and(|r| r.shared);
                let child_perms = if parent_perms.contains(Perms::WRITE) && !is_shared_mapping {
                    let ro = parent_perms.without(Perms::WRITE);
                    if !unsafe { mmu::set_leaf_perms(self.root, page.va, ro) } {
                        return Err(LoadError::OutOfRange);
                    }
                    ro
                } else {
                    parent_perms
                };
                unsafe {
                    mmu::map_range(child.root, page.va, page.pa, PAGE_SIZE, child_perms)?;
                }
                child.pages.push(OwnedPage {
                    va: page.va,
                    pa: page.pa,
                });
                share_frame(page.pa);
            }
            Ok(())
        })();

        if let Err(e) = result {
            child.release();
            return Err(e);
        }
        // The parent's old writable translations are stale the moment the PTEs
        // change: a TLB entry that still permits a store would let the parent
        // write straight into the frame the child now shares.
        mmu::flush_tlb();
        Ok(child)
    }

    /// Claim `len` zeroed, anonymous, private bytes and return their address.
    ///
    /// **No frame is allocated here.** The call records a [`Region`] and lets
    /// the fault handler fill pages in as they are touched; the first touch of
    /// each page is the only place a frame is ever spent.
    pub fn map_anon(
        &mut self,
        addr: usize,
        len: usize,
        prot: u8,
        shared: bool,
    ) -> Result<usize, MapError> {
        if len == 0 {
            return Err(MapError::InvalidRange);
        }
        let size = len.div_ceil(PAGE_SIZE) * PAGE_SIZE;

        let base = if addr != 0 {
            if !addr.is_multiple_of(PAGE_SIZE) {
                return Err(MapError::InvalidRange);
            }
            addr
        } else {
            self.map_next
        };
        let end = base.checked_add(size).ok_or(MapError::InvalidRange)?;
        if end > MMAP_LIMIT || base < MMAP_BASE {
            return Err(MapError::InvalidRange);
        }
        // Refuse to overlap anything already claimed. Checking regions rather
        // than the page table is what makes this work now that a region can be
        // valid before any of its pages exist.
        for va in (base..end).step_by(PAGE_SIZE) {
            if self.region_at(va).is_some() {
                return Err(MapError::InvalidRange);
            }
        }

        self.regions.push(Region {
            start: base,
            end,
            perms: perms_from_prot(prot),
            shared,
        });
        if addr == 0 || base == self.map_next {
            self.map_next = end;
        }
        Ok(base)
    }

    /// Unmap and free every page in `[va, va + len)`.
    ///
    /// Pages that are not mapped are ignored, matching `munmap`'s contract that
    /// unmapping already-unmapped memory succeeds. A range that *partially*
    /// covers a page is refused rather than rounded: silently unmapping more
    /// than asked would corrupt a neighbouring mapping.
    pub fn unmap(&mut self, va: usize, len: usize) -> Result<(), MapError> {
        if len == 0 {
            return Ok(());
        }
        if !va.is_multiple_of(PAGE_SIZE) {
            return Err(MapError::InvalidRange);
        }
        let size = len.div_ceil(PAGE_SIZE) * PAGE_SIZE;
        let end = va.checked_add(size).ok_or(MapError::InvalidRange)?;
        for page_va in (va..end).step_by(PAGE_SIZE) {
            if let Some(pos) = self.pages.iter().position(|p| p.va == page_va) {
                let page = self.pages.remove(pos);
                unsafe {
                    mmu::unmap_range(self.root, page.va, PAGE_SIZE).ignore_result();
                }
                drop_frame_ref(page.pa);
            }
        }
        // Trim the permission claim as well, or the pages just unmapped would
        // be faulted straight back in by the next access.
        self.trim_regions(va, end);
        mmu::flush_tlb();
        Ok(())
    }

    /// Cut `[va, end)` out of the region list, splitting regions that straddle
    /// a boundary.
    fn trim_regions(&mut self, va: usize, end: usize) {
        let mut keep = Vec::with_capacity(self.regions.len() + 1);
        for r in self.regions.drain(..) {
            if r.end <= va || r.start >= end {
                keep.push(r);
                continue;
            }
            if r.start < va {
                keep.push(Region {
                    start: r.start,
                    end: va,
                    perms: r.perms,
                    shared: r.shared,
                });
            }
            if r.end > end {
                keep.push(Region {
                    start: end,
                    end: r.end,
                    perms: r.perms,
                    shared: r.shared,
                });
            }
        }
        self.regions = keep;
    }
}

/// Translate a Linux `PROT_*` mask into page-table permissions.
///
/// `PROT_NONE` (0) yields a mapping with neither R nor W nor X — which Sv39
/// treats as a *non-leaf* entry, not an accessible one. A `PROT_NONE` page is
/// therefore refused explicitly by `sys_mmap` rather than mapped as something
/// else.
fn perms_from_prot(prot: u8) -> Perms {
    let mut p = Perms::USER;
    if prot & 0x1 != 0 {
        p = p.bitor(Perms::READ);
    }
    if prot & 0x2 != 0 {
        p = p.bitor(Perms::WRITE);
    }
    if prot & 0x4 != 0 {
        p = p.bitor(Perms::EXEC);
    }
    p
}

// ---------------------------------------------------------------------------
// Page faults
// ---------------------------------------------------------------------------

/// Try to satisfy a fault taken at `va` that needs `need`.
///
/// Called from the trap layer, i.e. from inside the kernel while the faulting
/// thread is the current one — so the address space is looked up through the
/// current process and the fix-up is visible to the very next instruction the
/// `mret` runs.
///
/// A `false` here means "this process really did something illegal"; the caller
/// retires it.
pub fn handle_page_fault(va: usize, need: Perms) -> bool {
    let Some(ok) = with_current_space(|space| space.fault_in(va, need)) else {
        return false;
    };
    if ok {
        // The PTE changed under a live `satp`: without this the hart may keep
        // using the translation that faulted (or the writable one that must not
        // be writable any more).
        mmu::flush_tlb();
    }
    ok
}

/// Materialise `[va, va + len)` for a syscall about to touch it.
///
/// The copy helpers resolve through the page table and fail on an unmapped
/// page. That is correct for a pointer the process never claimed, and wrong for
/// memory it got from `mmap` and has not written yet — which is every buffer
/// large enough to be interesting. This runs the same fault path a real access
/// would, then the caller retries the copy.
pub fn fault_in_range(va: usize, len: usize, need: Perms) -> bool {
    if len == 0 {
        return true;
    }
    let end = match va.checked_add(len) {
        Some(e) => e,
        None => return false,
    };
    let mut cur = va & !(PAGE_SIZE - 1);
    while cur < end {
        if !handle_page_fault(cur, need) {
            crate::kearly_println!(
                "user: fault-in 0x{:x} failed — pointer does not address a mapped region",
                cur
            );
            return false;
        }
        cur += PAGE_SIZE;
    }
    true
}

// ---------------------------------------------------------------------------
// User-pointer access for syscalls
// ---------------------------------------------------------------------------

/// Copy `dst.len()` bytes out of user memory at `src`.
///
/// Every syscall that takes a pointer from U-mode goes through here. A raw
/// dereference would be a privilege escalation: the kernel runs in M-mode,
/// where `satp` does not apply, so `0x8000_0000` from user space would be read
/// as *physical* memory.
pub fn copy_from_user(dst: &mut [u8], src: usize) -> Result<(), crate::error::Error> {
    let Some(root) = current_root() else {
        return Err(code::EPERM);
    };
    // Demand-paging first: a buffer from `mmap` may legitimately have no frame
    // until this very access.
    if !fault_in_range(src, dst.len(), Perms::READ) {
        return Err(code::EINVAL);
    }
    match unsafe { mmu::copy_from_user(root, dst, src) } {
        Ok(()) => Ok(()),
        Err(_) => Err(code::EINVAL),
    }
}

/// Copy `src` into user memory at `dst`.
pub fn copy_to_user(dst: usize, src: &[u8]) -> Result<(), crate::error::Error> {
    let Some(root) = current_root() else {
        return Err(code::EPERM);
    };
    if !fault_in_range(dst, src.len(), Perms::WRITE) {
        return Err(code::EINVAL);
    }
    match unsafe { mmu::copy_to_user(root, dst, src) } {
        Ok(()) => Ok(()),
        Err(_) => Err(code::EINVAL),
    }
}

/// Copy a NUL-terminated string out of user memory, capped at `max` bytes.
///
/// Returns the string *without* its terminator. A pointer to an unterminated
/// run of bytes is an error rather than a silent truncation, because callers
/// would otherwise use the truncated value as if it were the real one.
pub fn copy_cstr_from_user(src: usize, max: usize) -> Result<String, crate::error::Error> {
    let Some(root) = current_root() else {
        return Err(code::EPERM);
    };
    let limit = core::cmp::min(max, 4096);
    // Walk one byte at a time, paging in each 4 KiB window on the way. The cap
    // keeps a hostile unterminated buffer from reading the whole address space
    // just to discover there is no terminator.
    let mut len = 0usize;
    loop {
        if len >= limit {
            return Err(code::ENAMETOOLONG);
        }
        let at = src.checked_add(len).ok_or(code::EINVAL)?;
        if at & (PAGE_SIZE - 1) == 0 && !handle_page_fault(at, Perms::READ) {
            return Err(code::EINVAL);
        }
        let mut byte = [0u8; 1];
        unsafe { mmu::copy_from_user(root, &mut byte, at) }.map_err(|_| code::EINVAL)?;
        if byte[0] == 0 {
            break;
        }
        len += 1;
    }
    let mut buf = alloc::vec![0u8; len];
    if len > 0 {
        unsafe { mmu::copy_from_user(root, &mut buf, src) }.map_err(|_| code::EINVAL)?;
    }
    core::str::from_utf8(&buf)
        .map(|s| s.to_string())
        .map_err(|_| code::EINVAL)
}

// ---------------------------------------------------------------------------
// Spawning and exec
// ---------------------------------------------------------------------------

/// Number of user processes started since boot, for diagnostics.
pub static STARTED: AtomicUsize = AtomicUsize::new(0);

/// Load `path` into a new user thread, leaving the caller running.
///
/// This is `execve`'s mirror image: the way for a kernel thread — a shell, a
/// boot-time helper — to start a user program. The new process is a child of
/// the caller's process, so `waitpid` from the caller can collect it.
pub fn spawn_path(path: &str) -> Result<crate::process::Pid, isize> {
    let bytes = crate::vfs::read_whole_file(path, MAX_IMAGE).map_err(|e| e.to_errno() as isize)?;
    let name = path.rsplit('/').next().unwrap_or(path);
    let mut space = AddressSpace::load(name, &bytes).map_err(|e| e.to_errno())?;
    // A spawned process gets the same startup block an `exec` one does: a
    // program that reads `argv` must not care which call started it.
    space
        .build_startup(&[name], &[])
        .map_err(|e| e.to_errno())?;
    spawn(space)
}

/// Run `space` as a user thread.
///
/// The thread body is [`user_thread_entry`], which the kernel schedules like
/// any other thread: it starts in M-mode on a kernel stack and immediately
/// drops to U-mode. From that point the thread only ever re-enters the kernel
/// through a trap.
///
/// Returns the new pid, or the space itself if the thread could not be queued,
/// so a caller can retry without leaking frames.
pub fn spawn(space: AddressSpace) -> Result<crate::process::Pid, isize> {
    use crate::process::ProcessManager;
    let mgr = ProcessManager::get();
    let parent = current_process().map_or_else(
        || Arc::downgrade(mgr.root_process()),
        |p| Arc::downgrade(&p),
    );
    let proc = mgr.create_process(parent).map_err(|e| e.to_errno() as isize)?;
    let space_root = space.root();
    let satp = mmu::satp_sv39(space_root);
    let entry = space.entry();
    let sp = space.startup_sp();
    let label = space.name().to_string();
    let pages = space.page_count();
    *proc.mm().irqsave_lock() = Some(space);

    // The entry address only exists at run time, so the thread body is a
    // closure rather than an `Entry::C` function pointer: it captures the three
    // numbers that define this image, instead of parking them in a side table
    // keyed by thread id.
    let body =
        alloc::boxed::Box::new(move || unsafe { crate::arch::riscv::enter_user(satp, entry, sp) });
    let node = crate::thread::Builder::new(crate::thread::Entry::Closure(body)).build();
    if !proc.add_thread(node.clone()) {
        mgr.destroy_process(proc.pid());
        return Err(code::EAGAIN.to_errno() as isize);
    }
    if crate::scheduler::queue_ready_thread(crate::thread::IDLE, node).is_err() {
        mgr.destroy_process(proc.pid());
        return Err(code::EAGAIN.to_errno() as isize);
    }
    STARTED.fetch_add(1, Ordering::Relaxed);
    crate::kearly_println!(
        "user: \"{}\" -> pid {}, entry=0x{:x} sp=0x{:x}, {} pages",
        label,
        proc.pid().0,
        entry,
        sp,
        pages
    );
    Ok(proc.pid())
}

/// What the trap layer must write into the saved frame for an `exec` to take
/// effect.
#[derive(Debug, Clone, Copy)]
pub struct ExecOutcome {
    /// New program counter.
    pub entry: usize,
    /// New user stack pointer.
    pub sp: usize,
}

/// Take the outcome of an `exec` performed during this syscall, if any.
///
/// Called by the trap layer immediately after dispatching. The redirect is
/// stored on the calling thread rather than in a global, so a concurrent
/// `execve` on another hart (or a preemption in between) cannot make a
/// different thread resume at a program it never loaded.
pub fn take_exec_outcome() -> Option<ExecOutcome> {
    // Every `ecall` ends here, including the kernel-internal ones (`malloc`
    // reaches `AllocMem` this way) that run long before the scheduler has
    // published `RUNNING_THREADS`. Touching the current thread there would
    // dereference an uninitialised per-CPU slot.
    if !crate::scheduler::is_schedule_ready() {
        return None;
    }
    crate::scheduler::current_thread_ref().take_pending_exec()
}

/// Replace the calling thread's image with the program at `path`.
///
/// The syscall does **not** return to the caller: it loads the new image, swaps
/// the calling process's address space, writes the new entry point and stack
/// into a global, and returns. The trap layer then picks those two numbers up
/// and overwrites the saved frame — `mepc` and `mscratch` — so the `mret` that
/// ends this syscall lands in the new program. That is what makes exec work
/// without a separate "return to user" path: the return is redirected, not
/// taken.
pub fn exec(path: &str, argv: &[&str], envp: &[&str]) -> Result<(), isize> {
    // Refuse kernel threads: there is no user frame to redirect, and silently
    // doing the load anyway would leave an image nobody runs.
    if current_root().is_none() {
        return Err(code::EPERM.to_errno() as isize);
    }
    let Some(proc) = current_process() else {
        return Err(code::EPERM.to_errno() as isize);
    };

    let bytes = crate::vfs::read_whole_file(path, MAX_IMAGE).map_err(|e| e.to_errno() as isize)?;

    // Name the space after the last path component: `/bin/hello` prints as
    // "hello", which is what the exit log should say.
    let name = path.rsplit('/').next().unwrap_or(path);
    let mut space = AddressSpace::load(name, &bytes).map_err(|e| e.to_errno())?;

    // An explicit `argv` wins; an empty one means `execve(path, NULL, NULL)`,
    // which POSIX says the kernel may treat as a single-element vector holding
    // the program name.
    let sp = if argv.is_empty() {
        space.build_startup(&[name], envp)
    } else {
        space.build_startup(argv, envp)
    }
    .map_err(|e| e.to_errno())?;

    let space_root = space.root();
    let satp = mmu::satp_sv39(space_root);
    let entry = space.entry();
    let new_pages = space.page_count();

    // Swap under the lock so another hart cannot observe a process with no
    // space, then release the old one outside it: `release` frees frames and
    // takes no process lock, but holding one across it is a needless window.
    let old = {
        let mut mm = proc.mm().irqsave_lock();
        mm.replace(space)
    };
    set_satp(satp);
    if let Some(mut old) = old {
        let old_pages = old.page_count();
        old.release();
        crate::kearly_println!(
            "user: exec \"{}\" -> \"{}\" on pid {}, entry=0x{:x} sp=0x{:x}, {} pages (freed {})",
            old.name(),
            name,
            proc.pid().0,
            entry,
            sp,
            new_pages,
            old_pages
        );
    }

    // `execve` closes descriptors marked `FD_CLOEXEC`; the surviving ones keep
    // their numbers. This is the other half of descriptor inheritance: `fork`
    // copies the table, `exec` applies the per-descriptor close flag.
    #[cfg(enable_vfs)]
    proc.fd_manager().irqsave_lock().close_on_exec();

    crate::scheduler::current_thread_ref().set_pending_exec(ExecOutcome { entry, sp });
    Ok(())
}

/// `fork(2)`: clone the calling process, returning the child's pid in the
/// parent and zero in the child.
///
/// `frame` is the parent's saved trap frame. It is the *only* way to give the
/// child a correct starting point: the child must resume at the instruction
/// after the parent's `ecall` with the parent's registers, and those registers
/// exist nowhere else. `mepc` has already been advanced past the `ecall` by the
/// trap layer, which is why nothing here adds 4.
pub(crate) fn fork(frame: &crate::arch::riscv::Context) -> isize {
    if current_root().is_none() {
        return code::EPERM.to_errno() as isize;
    }
    let Some(parent_proc) = current_process() else {
        return code::EPERM.to_errno() as isize;
    };

    // The child's whole visible state is the parent's frame minus `a0`.
    // `mscratch` already holds the parent's user `sp`, which is exactly where
    // the child must continue.
    let mut child_frame = frame.clone();
    child_frame.a0 = 0;
    let mepc = child_frame.mepc;
    let sp = child_frame.mscratch;

    let child = {
        let mut mm = parent_proc.mm().irqsave_lock();
        let Some(parent_space) = mm.as_mut() else {
            return code::EPERM.to_errno() as isize;
        };
        let name = alloc::format!("{}#fork", parent_space.name());
        match parent_space.fork_clone(&name) {
            Ok(c) => c,
            Err(e) => return e.to_errno(),
        }
    };
    let pages = child.page_count();
    let satp = mmu::satp_sv39(child.root());

    let mgr = crate::process::ProcessManager::get();
    let Ok(child_proc) = mgr.create_process(Arc::downgrade(&parent_proc)) else {
        return code::EAGAIN.to_errno() as isize;
    };
    // The descriptor table is copied from the parent, not reopened: the
    // child's slots name the parent's open file descriptions (so offsets are
    // shared, as POSIX requires), while `close()` in either process only
    // drops its own reference.
    #[cfg(enable_vfs)]
    {
        let parent_fds = parent_proc.fd_manager().irqsave_lock().fork_copy();
        *child_proc.fd_manager().irqsave_lock() = parent_fds;
    }
    *child_proc.mm().irqsave_lock() = Some(child);

    let body = alloc::boxed::Box::new(move || unsafe {
        crate::arch::riscv::enter_user_from_frame(&child_frame, satp)
    });
    let node = crate::thread::Builder::new(crate::thread::Entry::Closure(body)).build();
    if !child_proc.add_thread(node.clone())
        || crate::scheduler::queue_ready_thread(crate::thread::IDLE, node).is_err()
    {
        mgr.destroy_process(child_proc.pid());
        return code::EAGAIN.to_errno() as isize;
    }
    crate::kearly_println!(
        "user: fork -> pid {}, resumes at 0x{:x} sp=0x{:x}, {} pages shared",
        child_proc.pid().0,
        mepc,
        sp,
        pages
    );
    child_proc.pid().0 as isize
}

/// `mmap(2)` for the calling process.
pub fn sys_mmap(addr: usize, len: usize, prot: usize, flags: usize, fd: i32, off: usize) -> isize {
    const MAP_SHARED: usize = 0x01;
    const MAP_PRIVATE: usize = 0x02;
    const MAP_FIXED: usize = 0x10;
    const MAP_ANONYMOUS: usize = 0x20;

    // `MAP_SHARED` and `MAP_PRIVATE` are mutually exclusive; exactly one is
    // required. Linux silently prefers `MAP_SHARED` when both are set, which is
    // a footgun, so this refuses instead.
    let shared = flags & MAP_SHARED != 0;
    let private = flags & MAP_PRIVATE != 0;
    if shared == private {
        return code::EINVAL.to_errno() as isize;
    }
    if prot & 0x7 == 0 {
        return code::EINVAL.to_errno() as isize;
    }
    // File-backed mappings wait for the page-fault path to grow a backing
    // store; refusing now is honest, and every caller that would use one gets
    // EINVAL rather than a mapping that reads zeros.
    if flags & MAP_ANONYMOUS == 0 {
        return code::EINVAL.to_errno() as isize;
    }
    if fd >= 0 || off != 0 {
        return code::EINVAL.to_errno() as isize;
    }
    let req = if flags & MAP_FIXED != 0 { addr } else { 0 };

    let Some(mapped) = with_current_space(|space| space.map_anon(req, len, prot as u8, shared))
    else {
        return code::ENOMEM.to_errno() as isize;
    };
    match mapped {
        Ok(va) => va as isize,
        Err(MapError::NoMemory) => code::ENOMEM.to_errno() as isize,
        Err(_) => code::EINVAL.to_errno() as isize,
    }
}

/// `munmap(2)` for the calling process.
pub fn sys_munmap(addr: usize, len: usize) -> isize {
    match with_current_space(|space| space.unmap(addr, len)) {
        Some(Ok(())) => 0,
        _ => code::EINVAL.to_errno() as isize,
    }
}

/// `getpid(2)`.
pub fn sys_getpid() -> isize {
    current_process().map_or(code::EPERM.to_errno() as isize, |p| p.pid().0 as isize)
}

/// `getppid(2)`: the process that created the caller, or 0 for the root.
pub fn sys_getppid() -> isize {
    current_process()
        .and_then(|p| p.parent())
        .map_or(0, |p| p.pid().0 as isize)
}

// ---------------------------------------------------------------------------
// Process-model syscalls
//
// These are the thin layer between the ABI (pointers, shifted status words)
// and the machinery above (address spaces, `Process` topology). Keeping the
// ABI translation here, rather than in the dispatcher, means the dispatcher
// stays a table of numbers and every syscall can be exercised from a unit test
// without a trap frame.
// ---------------------------------------------------------------------------

/// Largest `argv` or `envp` `execve` will read before giving up with `E2BIG`.
///
/// A vector is read until a NULL terminator, so the only defence against a
/// caller that never writes one is a cap. 256 is what a shell needs by a wide
/// margin and small enough that the strings behind it are the real cost.
const MAX_EXEC_ARGS: usize = 256;

/// `execve(2)`: replace the calling process's image.
///
/// Returns only on failure. On success the trap layer redirects the saved
/// frame to the new entry point (see [`PENDING_EXEC`]), so the caller never
/// sees a return value — which is exactly the POSIX contract.
pub fn sys_execve(
    path: *const core::ffi::c_char,
    argv: *const *const core::ffi::c_char,
    envp: *const *const core::ffi::c_char,
) -> isize {
    use crate::vfs::uptr;
    let path = match uptr::cstr(path) {
        Ok(p) => p,
        Err(e) => return e.to_errno() as isize,
    };
    let argv = match uptr::cstr_vec(argv, MAX_EXEC_ARGS) {
        Ok(v) => v,
        Err(e) => return e.to_errno() as isize,
    };
    let envp = match uptr::cstr_vec(envp, MAX_EXEC_ARGS) {
        Ok(v) => v,
        Err(e) => return e.to_errno() as isize,
    };
    // The strings live in the vectors, so the borrowed slices stay valid for
    // the duration of the call.
    let argv_refs: Vec<&str> = argv.iter().map(String::as_str).collect();
    let envp_refs: Vec<&str> = envp.iter().map(String::as_str).collect();
    match exec(&path, &argv_refs, &envp_refs) {
        Ok(()) => 0,
        Err(errno) => errno,
    }
}

/// `waitpid(2)`: collect one exited child.
///
/// `status` receives the wait status word, not the bare exit code: POSIX puts
/// the code in bits 8..16 so that the low byte can say "killed by signal"
/// instead. `WEXITSTATUS()` in every libc does that shift, so the kernel has to
/// do it too — returning the raw code would make `WIFEXITED()` false for a
/// process that exited normally.
pub fn sys_waitpid(pid: i32, status: *mut core::ffi::c_int, options: i32) -> isize {
    use crate::vfs::uptr;
    const WNOHANG: i32 = 1;

    let Some(proc) = current_process() else {
        return code::EPERM.to_errno() as isize;
    };
    let nohang = options & WNOHANG != 0;

    loop {
        // Sample the epoch *before* scanning. A child that exits between the
        // scan and the wait bumps the counter, `atomic_wait` sees a mismatch
        // and returns immediately — the same lost-wakeup defence `poll` uses.
        let observed = proc.child_exit_epoch().load(Ordering::Acquire);

        // `for_each_child` holds the topology read lock, and `destroy_process`
        // takes the write lock, so the reaping happens after the scan.
        let mut found: Option<Arc<Process>> = None;
        proc.for_each_child(|child| {
            if found.is_some() {
                return;
            }
            if pid > 0 && child.pid().0 as i32 != pid {
                return;
            }
            if child.exit_code().is_some() {
                found = Some(Arc::clone(child));
            }
        });

        if let Some(child) = found {
            let exit = child.exit_code().unwrap_or(0);
            if !status.is_null() {
                if let Err(e) = uptr::write_struct(status, &(exit << 8)) {
                    return e.to_errno() as isize;
                }
            }
            // The status is collected, so the zombie may go: `mark_reaped`
            // first, or `destroy_process` would decline to finalise it and the
            // process (and its frames) would stay in the table for ever.
            child.mark_reaped();
            crate::process::ProcessManager::get().destroy_process(child.pid());
            return child.pid().0 as isize;
        }

        if proc.has_no_children() {
            return code::ECHILD.to_errno() as isize;
        }
        if nohang {
            return 0;
        }
        crate::sync::atomic_wait::atomic_wait(proc.child_exit_epoch(), observed, Tick::MAX).ok();
    }
}

/// `exit_group(2)`: end every thread of the calling process.
pub fn sys_exit_group(status: i32) -> isize {
    if let Some(proc) = current_process() {
        // Order matters: the status and the wake must be visible before the
        // parent can observe the zombie, otherwise a `waitpid` could reap a
        // child whose status is still `NOT_EXITED`.
        proc.set_exit_code(status & 0xff);
        if let Some(parent) = proc.parent() {
            parent.notify_child_exited();
        }
        // Marks the process a zombie. The actual teardown happens in the
        // scheduler once the last thread retires — including this one.
        crate::process::ProcessManager::get().destroy_process(proc.pid());
    }
    crate::scheduler::retire_me();
    // `retire_me` never comes back: this thread is off every run queue for
    // good. If it ever did, returning into the trap would `mret` with a freed
    // address space, so park here instead.
    loop {
        crate::scheduler::yield_me();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate as blueos;
    use alloc::vec;
    use blueos_test_macro::test;

    /// Hand-build a minimal `ET_EXEC` image: one RX segment at `vaddr`, plus a
    /// `.bss` tail, so the loader has to zero-fill past `filesz`.
    fn tiny_elf(vaddr: u64, filesz: usize, memsz: usize) -> Vec<u8> {
        let phoff: u64 = 64;
        let phentsize: u16 = 56;
        let phnum: u16 = 1;
        let payload_off = 64 + 56;
        let mut b = vec![0u8; payload_off + filesz];
        b[..4].copy_from_slice(b"\x7fELF");
        b[4] = 2; // ELFCLASS64
        b[5] = 1; // ELFDATA2LSB
        b[6] = 1; // EV_CURRENT
        b[16..18].copy_from_slice(&2u16.to_le_bytes()); // ET_EXEC
        b[18..20].copy_from_slice(&crate::elf::EM_RISCV.to_le_bytes());
        b[20..24].copy_from_slice(&1u32.to_le_bytes());
        b[24..32].copy_from_slice(&vaddr.to_le_bytes());
        b[32..40].copy_from_slice(&phoff.to_le_bytes());
        b[52..54].copy_from_slice(&64u16.to_le_bytes());
        b[54..56].copy_from_slice(&phentsize.to_le_bytes());
        b[56..58].copy_from_slice(&phnum.to_le_bytes());
        let ph = phoff as usize;
        b[ph..ph + 4].copy_from_slice(&1u32.to_le_bytes()); // PT_LOAD
        b[ph + 4..ph + 8].copy_from_slice(&5u32.to_le_bytes()); // R|X
        b[ph + 8..ph + 16].copy_from_slice(&(payload_off as u64).to_le_bytes());
        b[ph + 16..ph + 24].copy_from_slice(&vaddr.to_le_bytes());
        b[ph + 32..ph + 40].copy_from_slice(&(filesz as u64).to_le_bytes());
        b[ph + 40..ph + 48].copy_from_slice(&(memsz as u64).to_le_bytes());
        for (i, byte) in b[payload_off..].iter_mut().enumerate() {
            *byte = i as u8;
        }
        b
    }

    #[test]
    fn load_maps_segments_and_stack() {
        let image = tiny_elf(USER_IMAGE_BASE as u64, 8, 16);
        let space = AddressSpace::load("test", &image).expect("load failed");
        // One page of text (8 bytes + bss tail), a 64 KiB stack, and the two
        // read-execute trampoline pages (signal return and thread exit).
        assert_eq!(space.page_count(), 3 + USER_STACK_SIZE / PAGE_SIZE);
        assert_eq!(space.entry(), USER_IMAGE_BASE);

        // The segment must be readable and executable, and *not* writable:
        // `W^X` is enforced from the ELF's own `p_flags`.
        let (_, perms) = unsafe { mmu::translate(space.root(), USER_IMAGE_BASE) }
            .expect("entry page is not mapped");
        assert!(perms.contains(Perms::READ));
        assert!(perms.contains(Perms::EXEC));
        assert!(!perms.contains(Perms::WRITE));
        assert!(perms.contains(Perms::USER));

        // The file bytes must have landed in the frame that backs the address.
        let (pa, _) = unsafe { mmu::translate(space.root(), USER_IMAGE_BASE) }.unwrap();
        let byte = unsafe { core::ptr::read_volatile(pa as *const u8) };
        assert_eq!(byte, 0);
        let second = unsafe { core::ptr::read_volatile((pa + 1) as *const u8) };
        assert_eq!(second, 1);

        // The `.bss` tail is inside the same page but past `filesz`; a fresh
        // frame is zeroed by the allocator, so it must read zero.
        let tail = unsafe { core::ptr::read_volatile((pa + 12) as *const u8) };
        assert_eq!(tail, 0, "bss tail must be zero");

        // The stack is writable and user-accessible, never executable.
        let (_, stack_perms) = unsafe { mmu::translate(space.root(), USER_STACK_TOP - 8) }
            .expect("stack top is not mapped");
        assert!(stack_perms.contains(Perms::WRITE));
        assert!(!stack_perms.contains(Perms::EXEC));
    }

    #[test]
    fn load_rejects_an_image_that_overlaps_the_stack() {
        let image = tiny_elf((USER_STACK_TOP - 8) as u64, 8, 64);
        match AddressSpace::load("overlap", &image) {
            Err(LoadError::OutOfRange) => {}
            other => panic!("expected OutOfRange, got {:?}", other.map(|s| s.page_count())),
        }
    }

    #[test]
    fn demand_paging_fills_a_page_on_first_touch() {
        let image = tiny_elf(USER_IMAGE_BASE as u64, 8, 16);
        let mut space = AddressSpace::load("anon", &image).expect("load failed");
        let base = space.map_anon(0, 2 * PAGE_SIZE, 0x3, false).expect("mmap failed");
        assert_eq!(base, MMAP_BASE);
        assert_eq!(
            space.page_count(),
            3 + USER_STACK_SIZE / PAGE_SIZE,
            "mmap must not allocate up front"
        );

        assert!(space.fault_in(base, Perms::WRITE), "first touch must map");
        assert_eq!(space.page_count(), 4 + USER_STACK_SIZE / PAGE_SIZE);
        // A second touch of the same page is a no-op, not a second frame.
        assert!(space.fault_in(base + 8, Perms::READ));
        assert_eq!(space.page_count(), 4 + USER_STACK_SIZE / PAGE_SIZE);

        // A write outside every region is refused rather than mapped.
        assert!(!space.fault_in(MMAP_LIMIT + PAGE_SIZE, Perms::READ));
    }

    #[test]
    fn cow_fork_shares_until_a_write() {
        let image = tiny_elf(USER_IMAGE_BASE as u64, 8, 16);
        let mut parent = AddressSpace::load("cow", &image).expect("load failed");
        let pages_before = parent.page_count();

        let mut child = parent.fork_clone("cow-child").expect("fork_clone failed");
        assert_eq!(child.page_count(), pages_before);
        // Both sides now see the same frame, read-only. The stack is the page to
        // watch: it is `RW` before the fork, so the write-protect is what the
        // fork did, not what the ELF asked for.
        let stack_va = USER_STACK_TOP - 8;
        let (pp, pperms) = unsafe { mmu::translate(parent.root(), stack_va) }.unwrap();
        let (cp, cperms) = unsafe { mmu::translate(child.root(), stack_va) }.unwrap();
        assert_eq!(pp, cp, "fork must share the frame, not copy it");
        assert!(!pperms.contains(Perms::WRITE));
        assert!(!cperms.contains(Perms::WRITE));

        // A write in the child clones exactly that one page.
        assert!(child.fault_in(stack_va, Perms::WRITE));
        let (cp2, cperms2) = unsafe { mmu::translate(child.root(), stack_va) }.unwrap();
        assert_ne!(cp2, cp, "the child must get a private frame");
        assert!(cperms2.contains(Perms::WRITE));
        // The parent is untouched.
        let (pp2, _) = unsafe { mmu::translate(parent.root(), stack_va) }.unwrap();
        assert_eq!(pp2, pp);
        // The shared contents came across.
        let parent_byte = unsafe { core::ptr::read_volatile(pp as *const u8) };
        let child_byte = unsafe { core::ptr::read_volatile(cp2 as *const u8) };
        assert_eq!(child_byte, parent_byte);

        // A write to the read-only text segment stays refused on both sides:
        // copy-on-write must not become a way to defeat `W^X`.
        assert!(!child.fault_in(USER_IMAGE_BASE, Perms::WRITE));
    }

    #[test]
    fn startup_block_is_written_where_the_abi_says() {
        let image = tiny_elf(USER_IMAGE_BASE as u64, 8, 16);
        let mut space = AddressSpace::load("argv", &image).expect("load failed");
        let sp = space.build_startup(&["prog", "arg"], &["K=V"]).expect("startup failed");
        assert_eq!(sp & 0xf, 0, "sp must be 16-byte aligned");
        let read_word = |va: usize| -> usize {
            let mut b = [0u8; 8];
            unsafe { mmu::copy_from_user(space.root(), &mut b, va) }.expect("read failed");
            usize::from_ne_bytes(b)
        };
        assert_eq!(read_word(sp), 2, "argc");
        // argv[0] points at the string "prog".
        let a0 = read_word(sp + 8);
        let mut byte = [0u8; 1];
        unsafe { mmu::copy_from_user(space.root(), &mut byte, a0) }.unwrap();
        assert_eq!(byte[0], b'p');
        // argv[1] is "arg", then a NULL terminator for the argv vector.
        let a1 = read_word(sp + 16);
        unsafe { mmu::copy_from_user(space.root(), &mut byte, a1) }.unwrap();
        assert_eq!(byte[0], b'a');
        assert_eq!(read_word(sp + 24), 0, "argv is NULL-terminated");
        // envp[0] follows, then its own NULL.
        let e0 = read_word(sp + 32);
        unsafe { mmu::copy_from_user(space.root(), &mut byte, e0) }.unwrap();
        assert_eq!(byte[0], b'K');
        assert_eq!(read_word(sp + 40), 0, "envp is NULL-terminated");
    }

    #[test]
    fn release_returns_every_frame() {
        let image = tiny_elf(USER_IMAGE_BASE as u64, 8, 16);
        let mut space = AddressSpace::load("reap", &image).expect("load failed");
        let n = space.page_count();
        assert!(n > 0);
        space.release();
        assert_eq!(space.page_count(), 0);
        // Releasing twice is a no-op, not a double free: `Drop` runs after an
        // explicit `release` on every error path.
        space.release();
    }
}
