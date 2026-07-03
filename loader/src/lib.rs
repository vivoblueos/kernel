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

#![no_std]
#![feature(c_size_t)]

extern crate alloc;

mod allocator;
mod memory_mapper;
use goblin::elf::{reloc::R_RISCV_RELATIVE, Elf, Reloc};
use librs::string::memcpy;
pub use allocator::{DirectAllocator, MemoryAllocator};
pub use memory_mapper::MemoryMapper;

// Re-export goblin types needed by kernel callers.
pub use goblin::elf::Elf;

/// Zero the BSS region of any segment where `p_memsz > p_filesz`.
///
/// Must be called after [`copy_content_to_memory`] has written the
/// file-backed portions.
pub fn zero_bss_segments(binary: &Elf, alloc: &mut impl MemoryAllocator) -> Result {
    for ph in &binary.program_headers {
        if ph.p_type != goblin::elf::program_header::PT_LOAD {
            continue;
        }
        if ph.p_memsz > ph.p_filesz {
            let bss_start = ph.p_vaddr as usize + ph.p_filesz as usize;
            let bss_size = (ph.p_memsz - ph.p_filesz) as usize;
            // Use a temporary zeroed buffer to write through the allocator.
            let zeros = alloc::vec![0u8; bss_size];
            alloc.write_slice_at(bss_start, &zeros)?;
        }
    }
    Ok(())
}

/// Check for an INTERP segment and warn if one is found.
///
/// Phase 3 does not support dynamic linking, so we emit a warning and
/// continue.  The ELF may still be loaded as a static PIE if the entry
/// point is correct.
pub fn check_interp(binary: &Elf) {
    #[cfg(feature = "log")]
    for ph in &binary.program_headers {
        if ph.p_type == goblin::elf::program_header::PT_INTERP {
            log::warn!(
                "ELF has PT_INTERP (dynamic linker) — not supported; \
                 loading as static PIE"
            );
            return;
        }
    }
    #[cfg(not(feature = "log"))]
    let _ = binary;
}

pub type Result = core::result::Result<(), &'static str>;

fn build_memory_layout(binary: &Elf, mapper: &mut impl MemoryAllocator) -> Result {
    for ph in &binary.program_headers {
        match ph.p_type {
            goblin::elf::program_header::PT_LOAD => {
                // We're assuming loadable segments are compact.
                mapper
                    .update_start(ph.p_vaddr as usize)
                    .update_end((ph.p_vaddr + ph.p_memsz) as usize);
            }
            _ => continue,
        }
    }
    mapper.set_entry(binary.entry as usize);
    Ok(())
}

fn allocate_memory_for_segments(_binary: &Elf, mapper: &mut impl MemoryAllocator) -> Result {
    mapper.allocate()?;
    Ok(())
}

fn copy_content_to_memory(buffer: &[u8], binary: &Elf, mapper: &mut impl MemoryAllocator) -> Result {
    // FIXME: We are assuming if filesize < memsize, (memsize -
    // filesize) bits are .bss. I need to read more about ELF spec to
    // find out exceptions. Currently, it just works.
    for ph in &binary.program_headers {
        match ph.p_type {
            goblin::elf::program_header::PT_LOAD => {
                let Some(src) =
                    buffer.get(ph.p_offset as usize..(ph.p_offset + ph.p_filesz) as usize)
                else {
                    return Err("Invalid indices to the buffer");
                };
                mapper.write_slice_at(ph.p_vaddr as usize, src)?;
            }
            _ => continue,
        }
    }
    Ok(())
}

fn handle_riscv_relative_reloc(mapper: &mut impl MemoryAllocator, reloc: &Reloc) -> Result {
    let vaddr = reloc.r_offset as usize;
    let val = mapper.real_start()? + reloc.r_addend.unwrap_or(0) as usize;
    mapper.write_value_at(vaddr, val)?;
    Ok(())
}

#[allow(clippy::single_match)]
fn relocate(binary: &Elf, mapper: &mut impl MemoryAllocator) -> Result {
    let reloc_section = &binary.dynrelas;
    for reloc in reloc_section.iter() {
        match reloc.r_type {
            R_RISCV_RELATIVE => {
                handle_riscv_relative_reloc(mapper, &reloc)?;
            }
            _ => {}
        }
    }
    Ok(())
}

// FIXME: We should use lseek to parse ELF files to achieve low footprint.
pub fn load_elf(buffer: &[u8], mapper: &mut impl MemoryAllocator) -> Result {
    let Ok(binary) = goblin::elf::Elf::parse(buffer) else {
        return Err("Unable to parse the buffer");
    };
    build_memory_layout(&binary, mapper)?;
    allocate_memory_for_segments(&binary, mapper)?;
    copy_content_to_memory(buffer, &binary, mapper)?;
    relocate(&binary, mapper)?;
    mapper.real_entry()?;
    Ok(())
}