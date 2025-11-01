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
use goblin::elf::{reloc::R_RISCV_RELATIVE, Elf, Reloc};
use librs::string::memcpy;
pub use memory_mapper::MemoryMapper;

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
    mapper.allocate_memory();
    Ok(())
}

fn copy_content_to_memory(buffer: &[u8], binary: &Elf, mapper: &mut MemoryMapper) -> Result {
    // FIXME: We are assuming if filesize < memsize, (memsize -
    // filesize) bits are .bss. I need to read more about ELF spec to
    // find out exceptions. Currently, it just works.
    let base = mapper.real_start_mut().unwrap();
    for ph in &binary.program_headers {
        match ph.p_type {
            goblin::elf::program_header::PT_LOAD => {
                let src =
                    buffer[ph.p_offset as usize..(ph.p_offset + ph.p_filesz) as usize].as_ptr();
                let dst = unsafe { base.add(ph.p_vaddr as usize - mapper.start()) };
                unsafe {
                    memcpy(
                        dst as *mut core::ffi::c_void,
                        src as *const core::ffi::c_void,
                        ph.p_filesz as core::ffi::c_size_t,
                    )
                };
            }
            _ => continue,
        }
    }
    Ok(())
}

fn handle_riscv_relative_reloc(base: *mut u8, reloc: &Reloc) -> Result {
    let target_address = unsafe { base.add(reloc.r_offset as usize) as *mut usize };
    let content = unsafe { base.offset(reloc.r_addend.unwrap_or(0) as isize) as usize };
    unsafe { target_address.write(content) };
    Ok(())
}

#[allow(clippy::single_match)]
fn relocate(binary: &Elf, mapper: &mut MemoryMapper) -> Result {
    let reloc_section = &binary.dynrelas;
    let base = mapper.real_start_mut().unwrap();
    for reloc in reloc_section.iter() {
        match reloc.r_type {
            R_RISCV_RELATIVE => {
                handle_riscv_relative_reloc(base, &reloc)?;
            }
            _ => {}
        }
    }
    Ok(())
}

// FIXME: We should use lseek to parse ELF files to achieve low footprint.
pub fn load_elf(buffer: &[u8], mapper: &mut MemoryMapper) -> Result {
    let Ok(binary) = goblin::elf::Elf::parse(buffer) else {
        return Err("Unable to parse the buffer");
    };
    build_memory_layout(&binary, mapper)?;
    allocate_memory_for_segments(&binary, mapper)?;
    copy_content_to_memory(buffer, &binary, mapper)?;
    relocate(&binary, mapper)
}
