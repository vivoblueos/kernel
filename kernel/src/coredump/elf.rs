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

//! ELF ET_CORE structure definitions and builder.
//!
//! Hand-written `#[repr(C)]` structs for ELF32/ELF64.
//! Zero third-party ELF dependencies.

use core::mem;

// ── ELF identification constants ──────────────────────────────────────

const ELFCLASS32: u8 = 1;
const ELFCLASS64: u8 = 2;
const ELFDATA2LSB: u8 = 1;
const EV_CURRENT: u8 = 1;

#[cfg(target_pointer_width = "32")]
const ELF_CLASS: u8 = ELFCLASS32;
#[cfg(target_pointer_width = "64")]
const ELF_CLASS: u8 = ELFCLASS64;

const ELF_IDENT: [u8; 16] = [
    0x7f, b'E', b'L', b'F', // magic
    ELF_CLASS,                // class
    ELFDATA2LSB,              // data encoding (little-endian)
    EV_CURRENT,               // version
    0,                        // OS/ABI
    0,                        // ABI version
    0, 0, 0, 0, 0, 0, 0,     // padding
];

const ET_CORE: u16 = 4;
const PT_LOAD: u32 = 1;
const PT_NOTE: u32 = 4;

pub const NT_PRSTATUS: u32 = 1;
pub const NT_PRPSINFO: u32 = 3;
pub const NT_SIGINFO: u32 = 0x53494749; // 'SIGI'

// ── ELF machine types ─────────────────────────────────────────────────
#[cfg(target_arch = "arm")]
const EM_MACHINE: u16 = 40; // EM_ARM
#[cfg(target_arch = "aarch64")]
const EM_MACHINE: u16 = 183; // EM_AARCH64
#[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
const EM_MACHINE: u16 = 243; // EM_RISCV

// ── ELF structures ────────────────────────────────────────────────────

/// ELF header. `usize` fields expand to 4 or 8 bytes matching ELFCLASS.
#[repr(C)]
pub struct ElfHeader {
    pub e_ident: [u8; 16],
    pub e_type: u16,
    pub e_machine: u16,
    pub e_version: u32,
    pub e_entry: usize,
    pub e_phoff: usize,
    pub e_shoff: usize,
    pub e_flags: u32,
    pub e_ehsize: u16,
    pub e_phentsize: u16,
    pub e_phnum: u16,
    pub e_shentsize: u16,
    pub e_shnum: u16,
    pub e_shstrndx: u16,
}

/// Program header (PT_LOAD or PT_NOTE).
#[repr(C)]
pub struct Phdr {
    pub p_type: u32,
    pub p_flags: u32,
    pub p_offset: usize,
    pub p_vaddr: usize,
    pub p_paddr: usize,
    pub p_filesz: usize,
    pub p_memsz: usize,
    pub p_align: usize,
}

/// ELF note header.
#[repr(C)]
pub struct Nhdr {
    pub n_namesz: u32,
    pub n_descsz: u32,
    pub n_type: u32,
}

// ── Memory segment descriptor ─────────────────────────────────────────

#[derive(Clone, Copy, Debug)]
pub struct MemSegment {
    pub vaddr: usize,
    pub size: usize,
    pub data: &'static [u8],
    pub flags: u32,
}

impl MemSegment {
    pub fn align(&self) -> usize {
        core::mem::size_of::<usize>()
    }
}

// ── Coredump reason ───────────────────────────────────────────────────

#[derive(Clone, Debug)]
#[repr(C)]
pub struct CoredumpReason {
    pub signo: i32,
    pub code: i32,
    pub fault_addr: usize,
    pub arch_specific: usize,
}

// ── Helpers ───────────────────────────────────────────────────────────

pub fn write_struct<T>(buf: &mut [u8], offset: &mut usize, val: &T) {
    let sz = mem::size_of::<T>();
    let ptr = val as *const T as *const u8;
    unsafe {
        buf[*offset..*offset + sz].copy_from_slice(core::slice::from_raw_parts(ptr, sz));
    }
    *offset += sz;
}

pub fn align4(offset: &mut usize) {
    *offset = (*offset + 3) & !3;
}

pub fn align_to(offset: &mut usize, align: usize) {
    *offset = (*offset + align - 1) & !(align - 1);
}

pub fn write_phdr_at(buf: &mut [u8], phoff: usize, phdr: Phdr) {
    let sz = mem::size_of::<Phdr>();
    let ptr = &phdr as *const Phdr as *const u8;
    unsafe {
        buf[phoff..phoff + sz].copy_from_slice(core::slice::from_raw_parts(ptr, sz));
    }
}

// ── ELF builder ───────────────────────────────────────────────────────

pub fn build_elf(notes: &[u8], segments: &[MemSegment], buf: &mut [u8]) -> Result<usize, ()> {
    let mut offset = 0;
    let phnum = 1 + segments.len();
    let ehdr_size = mem::size_of::<ElfHeader>();
    let phdr_size = mem::size_of::<Phdr>();

    // Phase 1: write ELF Header
    let total_needed = ehdr_size
        + phnum * phdr_size
        + notes.len()
        + segments.iter().map(|s| s.data.len() + s.align()).sum::<usize>();
    if buf.len() < total_needed {
        return Err(());
    }

    let ehdr = ElfHeader {
        e_ident: ELF_IDENT,
        e_type: ET_CORE,
        e_machine: EM_MACHINE,
        e_version: 1,
        e_entry: 0,
        e_phoff: ehdr_size as usize,
        e_shoff: 0,
        e_flags: 0,
        e_ehsize: ehdr_size as u16,
        e_phentsize: phdr_size as u16,
        e_phnum: phnum as u16,
        e_shentsize: 0,
        e_shnum: 0,
        e_shstrndx: 0,
    };
    write_struct(buf, &mut offset, &ehdr);

    // Phase 2: reserve space for Program Headers
    let phdr_notes_off = offset;
    offset += phdr_size;
    let mut load_phdr_offs = [0usize; 32];
    for i in 0..segments.len() {
        load_phdr_offs[i] = offset;
        offset += phdr_size;
    }

    // Phase 3: write Notes (4-byte aligned)
    align4(&mut offset);
    let notes_file_off = offset;
    buf[offset..offset + notes.len()].copy_from_slice(notes);
    offset += notes.len();

    // Phase 4: write Segment data
    let mut load_file_offs = [0usize; 32];
    for (i, seg) in segments.iter().enumerate() {
        align_to(&mut offset, seg.align());
        load_file_offs[i] = offset;
        buf[offset..offset + seg.data.len()].copy_from_slice(seg.data);
        offset += seg.data.len();
    }

    // Phase 5: backfill Program Headers
    write_phdr_at(
        buf,
        phdr_notes_off,
        Phdr {
            p_type: PT_NOTE,
            p_flags: 0,
            p_offset: notes_file_off,
            p_vaddr: 0,
            p_paddr: 0,
            p_filesz: notes.len(),
            p_memsz: 0,
            p_align: 4,
        },
    );
    for (i, seg) in segments.iter().enumerate() {
        write_phdr_at(
            buf,
            load_phdr_offs[i],
            Phdr {
                p_type: PT_LOAD,
                p_flags: seg.flags,
                p_offset: load_file_offs[i],
                p_vaddr: seg.vaddr,
                p_paddr: seg.vaddr,
                p_filesz: seg.data.len(),
                p_memsz: seg.size,
                p_align: seg.align(),
            },
        );
    }

    Ok(offset)
}
