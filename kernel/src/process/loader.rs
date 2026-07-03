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

//! Inlined ELF loader for user-space processes.
//!
//! These functions are adapted from `blueos_loader` and inlined here to
//! avoid a GN dependency cycle: `blueos` → `blueos_loader` → `librs` →
//! `scal` → `blueos`.
//!
//! Only the subset needed by the kernel (Phase 3 first-process startup)
//! is included.  See `//kernel/loader/` for the full loader crate.

use crate::process::elf::MemoryAllocator;
use goblin::elf;

// ---------------------------------------------------------------------------
// Re-export goblin types needed by callers
// ---------------------------------------------------------------------------

pub(crate) use goblin::elf::Elf;

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Load an ELF binary into the memory space described by `allocator`.
///
/// Steps: parse → build virtual-memory layout → allocate physical backing →
/// copy file-backed content → apply relocations.
pub(crate) fn load_elf(buffer: &[u8], allocator: &mut impl MemoryAllocator) -> Result<(), &'static str> {
    let Ok(binary) = Elf::parse(buffer) else {
        return Err("Unable to parse the ELF buffer");
    };
    build_memory_layout(&binary, allocator)?;
    allocate_memory_for_segments(allocator)?;
    copy_content_to_memory(buffer, &binary, allocator)?;
    relocate(&binary, allocator)?;
    allocator.real_entry()?;
    Ok(())
}

/// Zero the BSS region of any segment where `p_memsz > p_filesz`.
///
/// Must be called after [`copy_content_to_memory`] has written the
/// file-backed portions.
pub(crate) fn zero_bss_segments(
    binary: &Elf,
    allocator: &mut impl MemoryAllocator,
) -> Result<(), &'static str> {
    for ph in &binary.program_headers {
        if ph.p_type != goblin::elf::program_header::PT_LOAD {
            continue;
        }
        if ph.p_memsz > ph.p_filesz {
            let bss_start = ph.p_vaddr as usize + ph.p_filesz as usize;
            let bss_size = (ph.p_memsz - ph.p_filesz) as usize;
            // Use a temporary zeroed buffer to write through the allocator.
            let zeros = alloc::vec![0u8; bss_size];
            allocator.write_slice_at(bss_start, &zeros)?;
        }
    }
    Ok(())
}

/// Check for an INTERP segment and warn if one is found.
///
/// Phase 3 does not support dynamic linking, so we emit a warning and
/// continue.  The ELF may still be loaded as a static PIE if the entry
/// point is correct.
pub(crate) fn check_interp(binary: &Elf) {
    for ph in &binary.program_headers {
        if ph.p_type == goblin::elf::program_header::PT_INTERP {
            log::warn!(
                "ELF has PT_INTERP (dynamic linker) — not supported in Phase 3; \
                 loading as static PIE"
            );
            return;
        }
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

fn build_memory_layout(
    binary: &Elf,
    allocator: &mut impl MemoryAllocator,
) -> Result<(), &'static str> {
    for ph in &binary.program_headers {
        if ph.p_type == goblin::elf::program_header::PT_LOAD {
            allocator
                .update_start(ph.p_vaddr as usize)
                .update_end((ph.p_vaddr + ph.p_memsz) as usize);
        }
    }
    allocator.set_entry(binary.entry as usize);
    Ok(())
}

fn allocate_memory_for_segments(
    allocator: &mut impl MemoryAllocator,
) -> Result<(), &'static str> {
    allocator.allocate()?;
    Ok(())
}

fn copy_content_to_memory(
    buffer: &[u8],
    binary: &Elf,
    allocator: &mut impl MemoryAllocator,
) -> Result<(), &'static str> {
    for ph in &binary.program_headers {
        if ph.p_type != goblin::elf::program_header::PT_LOAD {
            continue;
        }
        let Some(src) =
            buffer.get(ph.p_offset as usize..(ph.p_offset + ph.p_filesz) as usize)
        else {
            return Err("Invalid indices to the buffer");
        };
        allocator.write_slice_at(ph.p_vaddr as usize, src)?;
    }
    Ok(())
}

fn handle_relative_reloc(
    allocator: &mut impl MemoryAllocator,
    addend: i64,
    offset: u64,
) -> Result<(), &'static str> {
    let vaddr = offset as usize;
    let val = allocator.real_start()? + addend as usize;
    allocator.write_value_at(vaddr, val)?;
    Ok(())
}

fn relocate(
    binary: &Elf,
    allocator: &mut impl MemoryAllocator,
) -> Result<(), &'static str> {
    let reloc_section = &binary.dynrelas;
    for reloc in reloc_section.iter() {
        // R_AARCH64_RELATIVE = 1027, R_RISCV_RELATIVE = 3
        // For AArch64 PIE, the static linker emits R_AARCH64_RELATIVE.
        // We also handle R_RISCV_RELATIVE for cross-arch compatibility.
        match reloc.r_type {
            1027 | 3 => {
                let addend = reloc.r_addend.unwrap_or(0);
                handle_relative_reloc(allocator, addend, reloc.r_offset)?;
            }
            _ => {}
        }
    }
    Ok(())
}