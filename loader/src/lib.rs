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

mod memory_mapper;
use goblin::elf::{
    header::{ET_DYN, ET_EXEC},
    reloc::R_RISCV_RELATIVE,
    Elf, Reloc,
};
use memory_mapper::MappingModeKind;
pub use memory_mapper::{MemoryMapper, MemoryPermissions, MemoryRegion};

pub type Result = core::result::Result<(), &'static str>;

fn build_memory_layout(binary: &Elf, mapper: &mut MemoryMapper) -> Result {
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

fn allocate_memory_for_segments(_binary: &Elf, mapper: &mut MemoryMapper) -> Result {
    mapper.allocate_memory()?;
    Ok(())
}

fn copy_content_to_memory(buffer: &[u8], binary: &Elf, mapper: &mut MemoryMapper) -> Result {
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

fn handle_riscv_relative_reloc(mapper: &mut MemoryMapper, reloc: &Reloc) -> Result {
    let vaddr = reloc.r_offset as usize;
    let val = mapper.real_start()? + reloc.r_addend.unwrap_or(0) as usize;
    mapper.write_value_at(vaddr, val)?;
    Ok(())
}

#[allow(clippy::single_match)]
fn relocate(binary: &Elf, mapper: &mut MemoryMapper) -> Result {
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

fn load_dyn_elf(buffer: &[u8], binary: &Elf, mapper: &mut MemoryMapper) -> Result {
    if mapper.mode_kind() != MappingModeKind::Allocated {
        return Err("ET_DYN requires Allocated mapping mode");
    }
    build_memory_layout(binary, mapper)?;
    allocate_memory_for_segments(binary, mapper)?;
    copy_content_to_memory(buffer, binary, mapper)?;
    relocate(binary, mapper)?;
    mapper.real_entry()?;
    Ok(())
}

fn load_exec_elf(buffer: &[u8], binary: &Elf, mapper: &mut MemoryMapper) -> Result {
    if mapper.mode_kind() != MappingModeKind::Fixed {
        return Err("ET_EXEC requires Fixed mapping mode");
    }
    build_memory_layout(binary, mapper)?;
    copy_content_to_memory(buffer, binary, mapper)?;
    mapper.real_entry()?;
    Ok(())
}

// FIXME: We should use lseek to parse ELF files to achieve low footprint.
pub fn load_elf(buffer: &[u8], mapper: &mut MemoryMapper) -> Result {
    let binary = Elf::parse(buffer).map_err(|_| "Unable to parse the buffer")?;
    match binary.header.e_type {
        ET_DYN => load_dyn_elf(buffer, &binary, mapper),
        ET_EXEC => load_exec_elf(buffer, &binary, mapper),
        _ => Err("Unsupported ELF type"),
    }
}
