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

//! A minimal, dependency-free ELF64 reader.
//!
//! The kernel already has `blueos_loader`, but that crate answers a different
//! question: it parses an ELF *and* decides where the image lands, because the
//! contiguous loader copies the whole image into one heap block. A paged
//! loader cannot reuse that decision — every segment has to land at its own
//! virtual address, on frames it allocates itself, with its own permissions.
//!
//! So this module keeps only the parsing half: what the file *says*. It has no
//! opinion about memory, which is also why it depends on nothing but `core` +
//! `alloc` and can be unit-tested on the host.
//!
//! # What is accepted
//!
//! * 64-bit, little-endian, `EM_RISCV`.
//! * `ET_EXEC` (fixed link address) and `ET_DYN` (position independent).
//! * `PT_LOAD` segments, `PT_INTERP` (reported so the caller can refuse it
//!   *deliberately* instead of jumping into a missing interpreter), and
//!   `PT_DYNAMIC` only far enough to find `R_RISCV_RELATIVE` relocations.
//!
//! Anything else is rejected rather than ignored: a dropped relocation or a
//! silently skipped segment turns into a wild jump at run time, which is far
//! harder to diagnose than a load error.

use alloc::{
    string::{String, ToString},
    vec::Vec,
};

/// `e_machine` of RISC-V.
pub const EM_RISCV: u16 = 243;

/// `p_flags` bits of a program header.
pub const PF_X: u32 = 1;
pub const PF_W: u32 = 2;
pub const PF_R: u32 = 4;

const PT_LOAD: u32 = 1;
const PT_DYNAMIC: u32 = 2;
const PT_INTERP: u32 = 3;

const ET_EXEC: u16 = 2;
const ET_DYN: u16 = 3;

const DT_NULL: u64 = 0;
const DT_RELA: u64 = 7;
const DT_RELASZ: u64 = 8;
const DT_RELAENT: u64 = 9;

/// `R_RISCV_RELATIVE`: `*(Elf64_Addr *)r_offset = load_bias + r_addend`.
const R_RISCV_RELATIVE: u32 = 3;

/// Why a byte slice is not a loadable image.
///
/// The payload is a static string: it ends up in a log line next to the file
/// name, which is the only context the caller has.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ParseError(pub &'static str);

/// One `PT_LOAD` segment, still described in the ELF's own terms.
///
/// `offset`/`filesz` say which file bytes to copy; `memsz` says how much
/// address space to reserve, and `memsz - filesz` must be zero-filled (the
/// `.bss` tail).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Segment {
    pub vaddr: usize,
    pub offset: usize,
    pub filesz: usize,
    pub memsz: usize,
    pub perms: u32,
}

/// A relocation the loader must apply before the image can run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Reloc {
    pub offset: usize,
    pub addend: i64,
}

/// The parsed form of an executable image.
#[derive(Debug, Clone, Default)]
pub struct Image {
    pub entry: usize,
    pub segments: Vec<Segment>,
    pub relocs: Vec<Reloc>,
    /// `ET_DYN`: the image may be placed anywhere, and every address in it is
    /// relative to the load bias the loader chooses.
    pub is_pie: bool,
    /// Virtual address the program header table will have once loaded.
    ///
    /// Only a dynamically linked program looks at it (`AT_PHDR`), but the
    /// kernel is the only party that knows the load bias, so it is the only
    /// party that can report it.
    pub phdr_vaddr: Option<usize>,
    pub phnum: usize,
    pub phentsize: usize,
    /// `PT_INTERP` payload, if the image asks for a program interpreter.
    pub interp: Option<String>,
}

impl Image {
    /// Lowest virtual address covered by a `PT_LOAD` segment.
    pub fn vaddr_min(&self) -> usize {
        self.segments.iter().map(|s| s.vaddr).min().unwrap_or(0)
    }

    /// One past the highest address covered by a `PT_LOAD` segment.
    pub fn vaddr_max(&self) -> usize {
        self.segments
            .iter()
            .map(|s| s.vaddr.saturating_add(s.memsz))
            .max()
            .unwrap_or(0)
    }
}

#[inline]
fn u16_at(b: &[u8], off: usize) -> Option<u16> {
    Some(u16::from_le_bytes(b.get(off..off + 2)?.try_into().ok()?))
}

#[inline]
fn u32_at(b: &[u8], off: usize) -> Option<u32> {
    Some(u32::from_le_bytes(b.get(off..off + 4)?.try_into().ok()?))
}

#[inline]
fn u64_at(b: &[u8], off: usize) -> Option<u64> {
    Some(u64::from_le_bytes(b.get(off..off + 8)?.try_into().ok()?))
}

/// A file offset widened into `usize`, refusing values this target cannot
/// address (a 32-bit kernel reading a 64-bit image, mostly).
#[inline]
fn as_usize(v: u64) -> Option<usize> {
    usize::try_from(v).ok()
}

/// Parse `bytes` as an ELF64 image.
pub fn parse(bytes: &[u8]) -> Result<Image, ParseError> {
    // e_ident(16) + e_type(2) + e_machine(2) + e_version(4) + e_entry(8)
    // + e_phoff(8) + e_shoff(8) + e_flags(4) + e_ehsize(2) + e_phentsize(2)
    // + e_phnum(2) + e_shentsize(2) + e_shnum(2) + e_shstrndx(2)
    if bytes.len() < 64 {
        return Err(ParseError("file too short for an ELF64 header"));
    }
    if &bytes[..4] != b"\x7fELF" {
        return Err(ParseError("not an ELF file"));
    }
    if bytes[4] != 2 {
        return Err(ParseError("not a 64-bit ELF"));
    }
    if bytes[5] != 1 {
        return Err(ParseError("not little-endian"));
    }
    if u16_at(bytes, 18).ok_or(ParseError("truncated header"))? != EM_RISCV {
        return Err(ParseError("not a RISC-V image"));
    }
    let e_type = u16_at(bytes, 16).ok_or(ParseError("truncated header"))?;
    let is_pie = match e_type {
        ET_EXEC => false,
        ET_DYN => true,
        _ => return Err(ParseError("neither ET_EXEC nor ET_DYN")),
    };
    let entry = as_usize(u64_at(bytes, 24).ok_or(ParseError("truncated header"))?)
        .ok_or(ParseError("entry point does not fit this address width"))?;
    let phoff = as_usize(u64_at(bytes, 32).ok_or(ParseError("truncated header"))?)
        .ok_or(ParseError("program header offset out of range"))?;
    let phentsize = u16_at(bytes, 54).ok_or(ParseError("truncated header"))? as usize;
    let phnum = u16_at(bytes, 56).ok_or(ParseError("truncated header"))? as usize;

    if phnum == 0 {
        return Err(ParseError("no program headers"));
    }
    // 56 bytes is `sizeof(Elf64_Phdr)`; a larger stride is legal (padding) but
    // a smaller one cannot hold the fields read below.
    if phentsize < 56 {
        return Err(ParseError("program header entries are too small"));
    }
    let ph_end = phoff
        .checked_add(phnum.saturating_mul(phentsize))
        .filter(|&end| end <= bytes.len())
        .ok_or(ParseError("program header table runs past end of file"))?;
    let _ = ph_end;

    let mut image = Image {
        entry,
        relocs: Vec::new(),
        segments: Vec::new(),
        is_pie,
        phdr_vaddr: None,
        phnum,
        phentsize,
        interp: None,
    };
    let mut dynamic: Option<(usize, usize)> = None;

    for i in 0..phnum {
        let ph = phoff + i * phentsize;
        let p_type = u32_at(bytes, ph).ok_or(ParseError("truncated program header"))?;
        let p_offset = as_usize(u64_at(bytes, ph + 8).ok_or(ParseError("truncated ph"))?)
            .ok_or(ParseError("segment offset out of range"))?;
        let p_vaddr = as_usize(u64_at(bytes, ph + 16).ok_or(ParseError("truncated ph"))?)
            .ok_or(ParseError("segment address out of range"))?;
        let p_filesz = as_usize(u64_at(bytes, ph + 32).ok_or(ParseError("truncated ph"))?)
            .ok_or(ParseError("segment size out of range"))?;
        let p_memsz = as_usize(u64_at(bytes, ph + 40).ok_or(ParseError("truncated ph"))?)
            .ok_or(ParseError("segment size out of range"))?;
        let p_flags = u32_at(bytes, ph + 4).ok_or(ParseError("truncated ph"))?;

        match p_type {
            PT_LOAD => {
                // The bytes must actually be in the file. `memsz < filesz` is
                // malformed: there would be more to copy than to reserve.
                if p_offset.checked_add(p_filesz).is_none_or(|e| e > bytes.len()) {
                    return Err(ParseError("PT_LOAD file range runs past end of file"));
                }
                if p_memsz < p_filesz {
                    return Err(ParseError("PT_LOAD memsz < filesz"));
                }
                if p_memsz == 0 {
                    continue;
                }
                if image
                    .segments
                    .iter()
                    .any(|s: &Segment| s.vaddr == p_vaddr)
                {
                    return Err(ParseError("two PT_LOAD segments start at one address"));
                }
                image.segments.push(Segment {
                    vaddr: p_vaddr,
                    offset: p_offset,
                    filesz: p_filesz,
                    memsz: p_memsz,
                    perms: p_flags,
                });
            }
            PT_INTERP => {
                let end = p_offset
                    .checked_add(p_filesz)
                    .filter(|&e| e <= bytes.len())
                    .ok_or(ParseError("PT_INTERP runs past end of file"))?;
                let raw = &bytes[p_offset..end];
                let nul = raw
                    .iter()
                    .position(|&b| b == 0)
                    .ok_or(ParseError("PT_INTERP is not NUL-terminated"))?;
                let s = core::str::from_utf8(&raw[..nul])
                    .map_err(|_| ParseError("PT_INTERP is not UTF-8"))?;
                image.interp = Some(s.to_string());
            }
            PT_DYNAMIC => {
                let end = p_offset
                    .checked_add(p_filesz)
                    .filter(|&e| e <= bytes.len())
                    .ok_or(ParseError("PT_DYNAMIC runs past end of file"))?;
                dynamic = Some((p_offset, end));
            }
            _ => {}
        }
    }

    if image.segments.is_empty() {
        return Err(ParseError("no PT_LOAD segments"));
    }

    // Where the program headers themselves land: the segment that contains
    // them says it, because the ELF gives no direct mapping for `e_phoff`.
    image.phdr_vaddr = image.segments.iter().find_map(|s| {
        let off_in_seg = phoff.checked_sub(s.offset)?;
        // The whole table must fit inside this one segment for the answer to
        // be meaningful.
        if off_in_seg.checked_add(phnum * phentsize)? > s.memsz {
            return None;
        }
        s.vaddr.checked_add(off_in_seg)
    });

    if let Some((start, end)) = dynamic {
        parse_relocs(bytes, start, end, &mut image)?;
    }

    Ok(image)
}

/// Collect `R_RISCV_RELATIVE` entries from a `PT_DYNAMIC` range.
///
/// The dynamic array is a list of `(d_tag, d_val)` pairs terminated by
/// `DT_NULL`. Only the three tags needed to locate `.rela.dyn` are interpreted;
/// everything else (symbols, hash tables, the GOT's shape) belongs to a dynamic
/// linker this kernel does not have.
fn parse_relocs(bytes: &[u8], start: usize, end: usize, image: &mut Image) -> Result<(), ParseError> {
    let mut rela_at: Option<usize> = None;
    let mut rela_size = 0usize;
    let mut rela_ent = 24usize;

    let mut at = start;
    while at + 16 <= end {
        let tag = u64_at(bytes, at).ok_or(ParseError("truncated dynamic entry"))?;
        let val = as_usize(u64_at(bytes, at + 8).ok_or(ParseError("truncated dynamic entry"))?)
            .ok_or(ParseError("dynamic value out of range"))?;
        if tag == DT_NULL {
            break;
        }
        match tag {
            DT_RELA => rela_at = Some(val),
            DT_RELASZ => rela_size = val,
            DT_RELAENT => rela_ent = val,
            _ => {}
        }
        at += 16;
    }

    let Some(rela_at) = rela_at else {
        return Ok(());
    };
    if rela_ent < 24 {
        return Err(ParseError("DT_RELAENT is smaller than Elf64_Rela"));
    }
    if rela_size == 0 {
        return Ok(());
    }
    let rela_end = rela_at
        .checked_add(rela_size)
        .filter(|&e| e <= bytes.len())
        .ok_or(ParseError("relocation table runs past end of file"))?;

    let mut at = rela_at;
    while at + 24 <= rela_end {
        let r_offset = as_usize(u64_at(bytes, at).ok_or(ParseError("truncated rela"))?)
            .ok_or(ParseError("relocation offset out of range"))?;
        let r_info = u64_at(bytes, at + 8).ok_or(ParseError("truncated rela"))?;
        let r_addend = u64_at(bytes, at + 16).ok_or(ParseError("truncated rela"))? as i64;
        let kind = (r_info & 0xffff_ffff) as u32;
        if kind != R_RISCV_RELATIVE {
            // Refusing beats dropping: a skipped relocation becomes a wrong
            // pointer somewhere else entirely.
            return Err(ParseError("unsupported relocation type"));
        }
        image.relocs.push(Reloc {
            offset: r_offset,
            addend: r_addend,
        });
        at += rela_ent;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    // The kernel's own harness, not the std one: a plain `#[test]` attribute
    // pulls `extern crate test` (and therefore `std`) into `kernel_unittest`,
    // which conflicts with the crate's own `panic_handler`.
    use blueos_test_macro::test;

    /// Hand-build a minimal ELF64 with one `PT_LOAD` segment at `vaddr`.
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
        b[16..18].copy_from_slice(&ET_EXEC.to_le_bytes());
        b[18..20].copy_from_slice(&EM_RISCV.to_le_bytes());
        b[20..24].copy_from_slice(&1u32.to_le_bytes());
        b[24..32].copy_from_slice(&vaddr.to_le_bytes()); // e_entry
        b[32..40].copy_from_slice(&phoff.to_le_bytes());
        b[52..54].copy_from_slice(&64u16.to_le_bytes()); // e_ehsize
        b[54..56].copy_from_slice(&phentsize.to_le_bytes());
        b[56..58].copy_from_slice(&phnum.to_le_bytes());
        let ph = phoff as usize;
        b[ph..ph + 4].copy_from_slice(&PT_LOAD.to_le_bytes());
        b[ph + 4..ph + 8].copy_from_slice(&(PF_R | PF_X).to_le_bytes());
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
    fn parses_a_minimal_image() {
        let b = tiny_elf(0x1_0000, 16, 64);
        let img = parse(&b).expect("parse failed");
        assert_eq!(img.entry, 0x1_0000);
        assert!(!img.is_pie);
        assert_eq!(img.segments.len(), 1);
        assert_eq!(img.segments[0].vaddr, 0x1_0000);
        assert_eq!(img.segments[0].filesz, 16);
        assert_eq!(img.segments[0].memsz, 64, "bss tail must be preserved");
        assert_eq!(img.vaddr_min(), 0x1_0000);
        assert_eq!(img.vaddr_max(), 0x1_0000 + 64);
        assert!(img.relocs.is_empty());
        assert!(img.interp.is_none());
        // The program headers sit at file offset 64, which is *not* inside the
        // loadable segment (it starts at payload_off), so there is no AT_PHDR.
        assert_eq!(img.phdr_vaddr, None);
    }

    #[test]
    fn rejects_truncated_and_foreign_files() {
        assert_eq!(parse(b"").unwrap_err(), ParseError("file too short for an ELF64 header"));
        assert_eq!(parse(&[0u8; 64]).unwrap_err(), ParseError("not an ELF file"));
        let mut b = tiny_elf(0x1_0000, 8, 8);
        b[4] = 1; // 32-bit
        assert_eq!(parse(&b).unwrap_err(), ParseError("not a 64-bit ELF"));
        let mut b = tiny_elf(0x1_0000, 8, 8);
        b[5] = 2; // big-endian
        assert_eq!(parse(&b).unwrap_err(), ParseError("not little-endian"));
        let mut b = tiny_elf(0x1_0000, 8, 8);
        b[18..20].copy_from_slice(&62u16.to_le_bytes()); // x86-64
        assert_eq!(parse(&b).unwrap_err(), ParseError("not a RISC-V image"));
        let mut b = tiny_elf(0x1_0000, 8, 8);
        b[16..18].copy_from_slice(&1u16.to_le_bytes()); // ET_REL
        assert_eq!(parse(&b).unwrap_err(), ParseError("neither ET_EXEC nor ET_DYN"));
    }

    #[test]
    fn rejects_segment_past_end_of_file() {
        let mut b = tiny_elf(0x1_0000, 8, 8);
        // Claim more file bytes than exist.
        let ph = 64 + 32;
        b[ph..ph + 8].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(parse(&b).is_err());
    }

    #[test]
    fn rejects_memsz_below_filesz() {
        let mut b = tiny_elf(0x1_0000, 16, 8);
        let ph = 64 + 40;
        b[ph..ph + 8].copy_from_slice(&8u64.to_le_bytes());
        assert_eq!(parse(&b).unwrap_err(), ParseError("PT_LOAD memsz < filesz"));
    }

    #[test]
    fn parses_interp_and_reports_it() {
        // Same image, but with a PT_INTERP header appended.
        let mut b = tiny_elf(0x1_0000, 8, 8);
        let phnum_at = 56;
        // Grow the table by one entry: reuse the payload area as the second
        // program header, which is fine because nothing loads it here.
        b[phnum_at..phnum_at + 2].copy_from_slice(&2u16.to_le_bytes());
        let payload_off = 64 + 56 + 56;
        b.resize(payload_off + 8, 0);
        b[payload_off..payload_off + 8].copy_from_slice(b"/ld.so\0\0");
        let ph = 64 + 56;
        b[ph..ph + 4].copy_from_slice(&PT_INTERP.to_le_bytes());
        b[ph + 8..ph + 16].copy_from_slice(&(payload_off as u64).to_le_bytes());
        b[ph + 32..ph + 40].copy_from_slice(&8u64.to_le_bytes());
        b[ph + 40..ph + 48].copy_from_slice(&8u64.to_le_bytes());
        let img = parse(&b).expect("parse failed");
        assert_eq!(img.interp.as_deref(), Some("/ld.so"));
        // The loadable segment's file range was fixed at 8 bytes; the interp
        // bytes live past it, which is exactly what a real image looks like.
        assert_eq!(img.segments.len(), 1);
    }
}
