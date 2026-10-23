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

use alloc::vec::Vec;
use blueos_test_macro::test;
use core::cell::Cell;
use goblin::elf::{
    header::{
        EI_ABIVERSION, EI_CLASS, EI_DATA, EI_OSABI, EI_VERSION, ELFDATA2MSB, EM_AARCH64, EM_RISCV,
        ET_DYN, ET_EXEC, ET_REL,
    },
    program_header::{
        PF_R, PF_W, PF_X, PT_DYNAMIC, PT_GNU_EH_FRAME, PT_GNU_RELRO, PT_GNU_STACK, PT_INTERP,
        PT_LOAD, PT_NOTE, PT_NULL, PT_PHDR, PT_SHLIB, PT_TLS,
    },
    Elf,
};

use super::fixture::{ElfFixtureBuilder, ProgramHeaderFixture, SliceElfReader};
use crate::{
    error::{ErrorContext, HeaderField, LimitKind, LoadErrorKind, LoadStage, ProgramHeaderField},
    image::ImageLoader,
    profile::{
        ElfClass, ElfData, ElfMachine, LoadLimits, LoadProfile, LoadRequest, ProgramHeaderPolicy,
    },
    reader::ElfReader,
    LoadError, LoadResult,
};

const PROFILES: [LoadProfile; 3] = [
    LoadProfile::riscv32(),
    LoadProfile::riscv64(),
    LoadProfile::aarch64(),
];

fn fixture(profile: LoadProfile, elf_type: u16) -> ElfFixtureBuilder {
    let machine = match profile.machine() {
        ElfMachine::Riscv => EM_RISCV,
        ElfMachine::Aarch64 => EM_AARCH64,
        ElfMachine::Other(machine) => machine,
    };
    match profile.class() {
        ElfClass::Elf32 => ElfFixtureBuilder::elf32(machine, elf_type),
        ElfClass::Elf64 => ElfFixtureBuilder::elf64(machine, elf_type),
    }
}

fn loader(bytes: &[u8], profile: LoadProfile) -> ImageLoader<SliceElfReader<'_>> {
    ImageLoader::new(
        SliceElfReader::new(bytes),
        LoadRequest::new(profile, LoadLimits::DEFAULT),
    )
}

fn failure<T>(result: LoadResult<T>) -> LoadError {
    match result {
        Err(error) => error,
        Ok(_) => panic!("invalid ELF accepted"),
    }
}

fn assert_error(error: &LoadError, stage: LoadStage, kind: LoadErrorKind) {
    assert_eq!(error.stage(), Some(stage), "{error:?}");
    assert_eq!(error.kind(), kind, "{error:?}");
}

fn assert_header_error(
    bytes: &[u8],
    profile: LoadProfile,
    kind: LoadErrorKind,
    expected: HeaderField,
) {
    let error = failure(loader(bytes, profile).admit());
    assert_error(&error, LoadStage::Admit, kind);
    assert!(
        matches!(error.context(), ErrorContext::HeaderField { field, .. } if *field == expected),
        "{error:?}"
    );
}

#[test]
fn admission_accepts_dyn_and_exec_for_all_public_profiles() {
    for profile in PROFILES {
        for elf_type in [ET_DYN, ET_EXEC] {
            let bytes = fixture(profile, elf_type).with_entry(0x8123_4560).build();
            let admitted = loader(&bytes, profile).admit().unwrap();
            let header = admitted.header();
            assert_eq!(header.class(), profile.class());
            assert_eq!(header.endian(), profile.endian());
            assert_eq!(header.machine(), profile.machine());
            assert_eq!(u64::from(header.r#type()), u64::from(elf_type));
            assert_eq!(header.entry(), 0x8123_4560);
            assert_eq!(header.program_header_count(), 0);
            assert!(admitted.inspect().unwrap().program_headers().is_empty());
        }
    }
}

#[test]
fn admission_reports_invalid_ident_fields() {
    for (offset, value, kind, field) in [
        (0, 0, LoadErrorKind::BadElf, HeaderField::Magic),
        (EI_CLASS, 0, LoadErrorKind::BadElf, HeaderField::Class),
        (EI_DATA, 0, LoadErrorKind::BadElf, HeaderField::Endian),
        (EI_VERSION, 0, LoadErrorKind::BadElf, HeaderField::Version),
        (
            EI_OSABI,
            3,
            LoadErrorKind::UnsupportedByProfile,
            HeaderField::OsAbi,
        ),
        (
            EI_ABIVERSION,
            1,
            LoadErrorKind::UnsupportedByProfile,
            HeaderField::AbiVersion,
        ),
    ] {
        let mut bytes = fixture(LoadProfile::riscv64(), ET_DYN).build();
        bytes[offset] = value;
        assert_header_error(&bytes, LoadProfile::riscv64(), kind, field);
    }
}

#[test]
fn admission_rejects_truncated_ident_and_headers() {
    for profile in PROFILES {
        let bytes = fixture(profile, ET_DYN).build();
        for len in [0, 15, 16, bytes.len() - 1] {
            let error = failure(loader(&bytes[..len], profile).admit());
            assert_error(&error, LoadStage::Admit, LoadErrorKind::OutOfBounds);
            assert!(
                matches!(error.context(), ErrorContext::FileRange { offset: 0, file_len, .. } if *file_len == len as u64)
            );
        }
    }
}

#[test]
fn admission_rejects_extended_program_header_numbering() {
    for profile in PROFILES {
        let mut bytes = fixture(profile, ET_DYN).build();
        let count_offset = if profile.class() == ElfClass::Elf32 {
            44
        } else {
            56
        };
        bytes[count_offset..count_offset + 2].copy_from_slice(&u16::MAX.to_le_bytes());
        // Even a permissive count limit must not interpret PN_XNUM literally.
        let request = LoadRequest::new(profile, LoadLimits::new(u64::MAX, u16::MAX));
        let error = failure(ImageLoader::new(SliceElfReader::new(&bytes), request).admit());
        assert_error(
            &error,
            LoadStage::Admit,
            LoadErrorKind::UnsupportedByProfile,
        );
        assert!(matches!(
            error.context(),
            ErrorContext::HeaderField {
                field: HeaderField::ProgramHeaderCount,
                value: 65535
            }
        ));
    }
}

#[test]
fn admission_checks_version_and_structure_sizes_for_both_classes() {
    for profile in [LoadProfile::riscv32(), LoadProfile::riscv64()] {
        let size_offset = if profile.class() == ElfClass::Elf32 {
            40
        } else {
            52
        };
        for (offset, field) in [
            (20, HeaderField::Version),
            (size_offset, HeaderField::HeaderSize),
            (size_offset + 2, HeaderField::ProgramHeaderSize),
        ] {
            let mut bytes = fixture(profile, ET_DYN).build();
            bytes[offset] = 0;
            assert_header_error(&bytes, profile, LoadErrorKind::BadElf, field);
        }
    }
}

#[test]
fn admission_rejects_mismatched_class_machine_and_type() {
    let bytes = fixture(LoadProfile::riscv32(), ET_DYN).build();
    assert_header_error(
        &bytes,
        LoadProfile::riscv64(),
        LoadErrorKind::UnsupportedByProfile,
        HeaderField::Class,
    );
    let bytes = fixture(LoadProfile::riscv64(), ET_DYN).build();
    assert_header_error(
        &bytes,
        LoadProfile::aarch64(),
        LoadErrorKind::UnsupportedByProfile,
        HeaderField::Machine,
    );
    let mut bytes = fixture(LoadProfile::aarch64(), ET_DYN).build();
    bytes[18..20].copy_from_slice(&62u16.to_le_bytes()); // EM_X86_64
    assert_header_error(
        &bytes,
        LoadProfile::aarch64(),
        LoadErrorKind::UnsupportedByProfile,
        HeaderField::Machine,
    );
    let bytes = fixture(LoadProfile::riscv64(), ET_REL).build();
    assert_header_error(
        &bytes,
        LoadProfile::riscv64(),
        LoadErrorKind::UnsupportedByProfile,
        HeaderField::Type,
    );
}

#[test]
fn admission_applies_the_machine_specific_flags_policy() {
    for profile in PROFILES {
        let rejected: &[u32] = if profile == LoadProfile::aarch64() {
            &[1, u32::MAX]
        } else {
            &[2, 4, 6, 8, 9]
        };
        for &flags in rejected {
            let bytes = fixture(profile, ET_DYN).with_flags(flags).build();
            assert_header_error(
                &bytes,
                profile,
                LoadErrorKind::UnsupportedByProfile,
                HeaderField::Flags,
            );
        }
    }
    for profile in [LoadProfile::riscv32(), LoadProfile::riscv64()] {
        let bytes = fixture(profile, ET_DYN).with_flags(1).build();
        assert_eq!(loader(&bytes, profile).admit().unwrap().header().flags(), 1);
    }
}

/// Change numeric fields of this one-program-header fixture to big endian.
fn big_endian(mut bytes: Vec<u8>) -> Vec<u8> {
    bytes[EI_DATA] = ELFDATA2MSB;
    let is32 = bytes[EI_CLASS] == 1;
    let fields: &[(usize, usize)] = if is32 {
        &[
            (16, 2),
            (18, 2),
            (20, 4),
            (24, 4),
            (28, 4),
            (32, 4),
            (36, 4),
            (40, 2),
            (42, 2),
            (44, 2),
            (46, 2),
            (48, 2),
            (50, 2),
        ]
    } else {
        &[
            (16, 2),
            (18, 2),
            (20, 4),
            (24, 8),
            (32, 8),
            (40, 8),
            (48, 4),
            (52, 2),
            (54, 2),
            (56, 2),
            (58, 2),
            (60, 2),
            (62, 2),
        ]
    };
    for &(offset, size) in fields {
        bytes[offset..offset + size].reverse();
    }
    if is32 {
        for field in bytes[52..].chunks_exact_mut(4) {
            field.reverse();
        }
    } else {
        bytes[64..68].reverse();
        bytes[68..72].reverse();
        for field in bytes[72..].chunks_exact_mut(8) {
            field.reverse();
        }
    }
    bytes
}

#[test]
fn endian_decoding_is_independent_of_the_native_profiles() {
    for native in [LoadProfile::riscv32(), LoadProfile::riscv64()] {
        let bytes = big_endian(
            fixture(native, ET_DYN)
                .with_entry(0x1234_5678)
                .with_program_header(ProgramHeaderFixture::load())
                .build(),
        );
        assert_header_error(
            &bytes,
            native,
            LoadErrorKind::UnsupportedByProfile,
            HeaderField::Endian,
        );
        let profile = LoadProfile::new(
            native.class(),
            ElfData::Big,
            native.machine(),
            native.header_flags(),
            native.entry_mode(),
        );
        let image = loader(&bytes, profile).admit().unwrap().inspect().unwrap();
        assert_eq!(image.header().entry(), 0x1234_5678);
        assert_eq!(image.program_headers()[0].vaddr(), 0x1000);
        assert_eq!(image.program_headers()[0].file_size(), 4);
        assert_eq!(image.program_headers()[0].flags(), PF_R | PF_X);
    }
}

struct ProbeReader<'a> {
    bytes: &'a [u8],
    file_len: u64,
    reads: &'a Cell<usize>,
    fail_at: Option<usize>,
}

impl ElfReader for ProbeReader<'_> {
    fn len(&self) -> LoadResult<u64> {
        if self.fail_at == Some(0) {
            return Err(LoadError::new(LoadErrorKind::Io, ErrorContext::None));
        }
        Ok(self.file_len)
    }

    fn read_exact_at(&self, offset: u64, dst: &mut [u8]) -> LoadResult<()> {
        let call = self.reads.get() + 1;
        self.reads.set(call);
        if self.fail_at == Some(call) {
            return Err(LoadError::new(
                LoadErrorKind::Io,
                ErrorContext::FileRange {
                    offset,
                    len: dst.len() as u64,
                    file_len: self.file_len,
                },
            ));
        }
        SliceElfReader::new(self.bytes).read_exact_at(offset, dst)
    }
}

#[test]
fn file_and_header_count_limits_precede_further_reads() {
    let profile = LoadProfile::riscv64();
    let bytes = fixture(profile, ET_DYN)
        .with_program_header(ProgramHeaderFixture::load())
        .build();
    for (limits, expected_reads, resource) in [
        (LoadLimits::new(0, 128), 0, LimitKind::FileLength),
        (LoadLimits::new(1024, 0), 2, LimitKind::ProgramHeaderCount),
    ] {
        let reads = Cell::new(0);
        let reader = ProbeReader {
            bytes: &bytes,
            file_len: bytes.len() as u64,
            reads: &reads,
            fail_at: None,
        };
        let error = failure(ImageLoader::new(reader, LoadRequest::new(profile, limits)).admit());
        assert_error(&error, LoadStage::Admit, LoadErrorKind::ResourceLimit);
        assert_eq!(reads.get(), expected_reads);
        assert!(matches!(
            (error.context(), resource),
            (
                ErrorContext::Limit {
                    resource: LimitKind::FileLength,
                    actual: 120,
                    maximum: 0
                },
                LimitKind::FileLength
            ) | (
                ErrorContext::Limit {
                    resource: LimitKind::ProgramHeaderCount,
                    actual: 1,
                    maximum: 0
                },
                LimitKind::ProgramHeaderCount
            )
        ));
    }
    let exact_limits = LoadLimits::new(bytes.len() as u64, 1);
    ImageLoader::new(
        SliceElfReader::new(&bytes),
        LoadRequest::new(profile, exact_limits),
    )
    .admit()
    .unwrap()
    .inspect()
    .unwrap();
}

#[test]
fn admission_rejects_overlapping_truncated_and_overflowing_header_tables() {
    let profile = LoadProfile::riscv64();
    for (offset, file_len, kind) in [
        (63, 120, LoadErrorKind::BadElf),
        (100, 120, LoadErrorKind::OutOfBounds),
        (u64::MAX - 4, u64::MAX, LoadErrorKind::IntegerOverflow),
    ] {
        let mut bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture::load())
            .build();
        bytes[32..40].copy_from_slice(&offset.to_le_bytes());
        let reads = Cell::new(0);
        let reader = ProbeReader {
            bytes: &bytes,
            file_len,
            reads: &reads,
            fail_at: None,
        };
        let error = failure(
            ImageLoader::new(
                reader,
                LoadRequest::new(profile, LoadLimits::new(u64::MAX, 128)),
            )
            .admit(),
        );
        assert_error(&error, LoadStage::Admit, kind);
        assert_eq!(reads.get(), 2); // No program header is read after an invalid table extent.
    }
    let mut bytes = fixture(LoadProfile::riscv32(), ET_DYN)
        .with_program_header(ProgramHeaderFixture::load())
        .build();
    bytes.pop();
    let error = failure(loader(&bytes, LoadProfile::riscv32()).admit());
    assert_error(&error, LoadStage::Admit, LoadErrorKind::OutOfBounds);
}

#[test]
fn reader_failures_keep_their_context_and_acquire_the_correct_stage() {
    let profile = LoadProfile::riscv64();
    let bytes = fixture(profile, ET_DYN)
        .with_program_header(ProgramHeaderFixture::load())
        .build();
    for call in 0..=3 {
        let reads = Cell::new(0);
        let reader = ProbeReader {
            bytes: &bytes,
            file_len: bytes.len() as u64,
            reads: &reads,
            fail_at: Some(call),
        };
        let error = failure(
            ImageLoader::new(reader, LoadRequest::new(profile, LoadLimits::DEFAULT))
                .admit()
                .and_then(|image| image.inspect()),
        );
        assert_error(
            &error,
            if call == 3 {
                LoadStage::Inspect
            } else {
                LoadStage::Admit
            },
            LoadErrorKind::Io,
        );
        if call != 0 {
            let expected_offset = if call == 3 { 64 } else { 0 };
            assert!(
                matches!(error.context(), ErrorContext::FileRange { offset, file_len: 120, .. } if *offset == expected_offset)
            );
        }
        assert_eq!(reads.get(), call);
    }
}

#[test]
fn inspection_reads_only_headers_without_following_sections_or_payload() {
    for profile in PROFILES {
        let mut bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture::load())
            .build();
        // Section metadata is deliberately inaccessible; loading uses segments.
        if profile.class() == ElfClass::Elf32 {
            bytes[32..36].copy_from_slice(&u32::MAX.to_le_bytes());
            bytes[48..50].copy_from_slice(&1u16.to_le_bytes());
        } else {
            bytes[40..48].copy_from_slice(&u64::MAX.to_le_bytes());
            bytes[60..62].copy_from_slice(&1u16.to_le_bytes());
        }
        let reads = Cell::new(0);
        let reader = ProbeReader {
            bytes: &bytes,
            file_len: bytes.len() as u64,
            reads: &reads,
            fail_at: Some(4),
        };
        let image = ImageLoader::new(reader, LoadRequest::new(profile, LoadLimits::DEFAULT))
            .admit()
            .unwrap()
            .inspect()
            .unwrap();
        assert_eq!(image.program_headers().len(), 1);
        assert_eq!(reads.get(), 3); // Ident, full ELF header, one program header.
    }
}

#[test]
fn inspected_program_headers_match_an_independent_parser() {
    for profile in PROFILES {
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture {
                vaddr: 0x8123_4560,
                flags: PF_R | PF_W,
                ..ProgramHeaderFixture::load()
            })
            .with_program_header(ProgramHeaderFixture {
                kind: PT_NOTE,
                ..ProgramHeaderFixture::load()
            })
            .build();
        let image = loader(&bytes, profile).admit().unwrap().inspect().unwrap();
        let parsed = Elf::parse(&bytes).unwrap();
        assert_eq!(image.program_headers().len(), parsed.program_headers.len());
        for (actual, expected) in image.program_headers().iter().zip(&parsed.program_headers) {
            assert_eq!(actual.r#type(), expected.p_type);
            assert_eq!(actual.flags(), expected.p_flags);
            assert_eq!(actual.file_offset(), expected.p_offset);
            assert_eq!(actual.vaddr(), expected.p_vaddr);
            assert_eq!(actual.file_size(), expected.p_filesz);
            assert_eq!(actual.memory_size(), expected.p_memsz);
            assert_eq!(actual.align(), expected.p_align);
        }
    }
}

#[test]
fn inspection_rejects_file_sizes_larger_than_memory_sizes() {
    for profile in PROFILES {
        for kind in [PT_LOAD, PT_DYNAMIC] {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    kind,
                    filesz: 4,
                    memsz: 3,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let error = failure(loader(&bytes, profile).admit().unwrap().inspect());
            assert_error(&error, LoadStage::Inspect, LoadErrorKind::BadElf);
            assert!(matches!(
                error.context(),
                ErrorContext::ProgramHeader {
                    index: 0,
                    field: ProgramHeaderField::FileRange,
                    value: 4
                }
            ));
        }
    }
}

#[test]
fn inspection_rejects_segment_file_and_virtual_range_errors() {
    let profile = LoadProfile::riscv64();
    for (offset, vaddr, kind) in [
        (119, 0x1000, LoadErrorKind::OutOfBounds),
        (u64::MAX - 1, 0x1000, LoadErrorKind::IntegerOverflow),
        (0, u64::MAX - 1, LoadErrorKind::IntegerOverflow),
    ] {
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture {
                offset,
                vaddr,
                ..ProgramHeaderFixture::load()
            })
            .build();
        let error = failure(loader(&bytes, profile).admit().unwrap().inspect());
        assert_error(&error, LoadStage::Inspect, kind);
        if offset != 0 {
            assert!(
                matches!(error.context(), ErrorContext::FileRange { offset: actual, len: 4, file_len: 120 } if *actual == offset)
            );
        } else {
            assert!(matches!(
                error.context(),
                ErrorContext::ProgramHeader {
                    index: 0,
                    field: ProgramHeaderField::VirtualRange,
                    ..
                }
            ));
        }
    }
}

#[test]
fn inspection_accepts_bss_only_and_file_end_ranges() {
    for profile in PROFILES {
        let file_len = if profile.class() == ElfClass::Elf32 {
            84
        } else {
            120
        };
        for filesz in [0, 4] {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    offset: file_len - filesz,
                    filesz,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let image = loader(&bytes, profile).admit().unwrap().inspect().unwrap();
            assert_eq!(image.program_headers()[0].file_size(), filesz);
        }
    }
}

#[test]
fn inspection_rejects_duplicate_singleton_headers() {
    const KINDS: [u32; 7] = [
        PT_DYNAMIC,
        PT_LOAD,
        PT_PHDR,
        PT_NOTE,
        PT_GNU_RELRO,
        PT_NULL,
        PT_GNU_STACK,
    ];
    for profile in PROFILES {
        for duplicate in [
            None,
            Some(PT_DYNAMIC),
            Some(PT_PHDR),
            Some(PT_GNU_RELRO),
            Some(PT_GNU_STACK),
        ] {
            let mut builder = fixture(profile, ET_DYN);
            for kind in KINDS {
                builder = builder.with_program_header(ProgramHeaderFixture {
                    kind,
                    flags: PF_R,
                    ..ProgramHeaderFixture::load()
                });
            }
            if let Some(kind) = duplicate {
                builder = builder.with_program_header(ProgramHeaderFixture {
                    kind,
                    flags: PF_R,
                    ..ProgramHeaderFixture::load()
                });
            }
            let bytes = builder.build();
            let result = loader(&bytes, profile).admit().unwrap().inspect();
            if let Some(kind) = duplicate {
                let error = failure(result);
                assert_error(&error, LoadStage::Inspect, LoadErrorKind::BadElf);
                assert!(matches!(
                    error.context(),
                    ErrorContext::ProgramHeader {
                        index: 7,
                        field,
                        value,
                    } if *value == u64::from(kind) && matches!(
                        (kind, field),
                        (PT_DYNAMIC, ProgramHeaderField::DuplicateDynamic)
                            | (PT_PHDR, ProgramHeaderField::DuplicatePhdr)
                            | (PT_GNU_RELRO, ProgramHeaderField::DuplicateRelro)
                            | (PT_GNU_STACK, ProgramHeaderField::DuplicateStack)
                    )
                ));
            } else {
                // Distinct singleton types must not share a seen flag.
                assert_eq!(result.unwrap().program_headers().len(), KINDS.len());
            }
        }
    }
}

#[test]
fn inspection_accepts_repeated_load_and_note_headers() {
    let profile = LoadProfile::riscv64();
    for kind in [PT_LOAD, PT_NOTE, PT_GNU_EH_FRAME] {
        let header = ProgramHeaderFixture {
            kind,
            ..ProgramHeaderFixture::load()
        };
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(header)
            .with_program_header(header)
            .build();
        assert_eq!(
            loader(&bytes, profile)
                .admit()
                .unwrap()
                .inspect()
                .unwrap()
                .program_headers()
                .len(),
            2
        );
    }
}

#[test]
fn inspection_rejects_interpreter_tls_and_unknown_segment_types() {
    for profile in PROFILES {
        for kind in [PT_INTERP, PT_TLS, PT_SHLIB, 0x1234_5678] {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    kind,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let error = failure(loader(&bytes, profile).admit().unwrap().inspect());
            assert_error(
                &error,
                LoadStage::Inspect,
                LoadErrorKind::UnsupportedByProfile,
            );
            assert!(
                matches!(error.context(), ErrorContext::ProgramHeader { index: 0, value, .. } if *value == u64::from(kind))
            );
            let expected_context = match kind {
                PT_INTERP => matches!(
                    error.context(),
                    ErrorContext::ProgramHeader {
                        field: ProgramHeaderField::UnsupportedInterpreter,
                        ..
                    }
                ),
                PT_TLS => matches!(
                    error.context(),
                    ErrorContext::ProgramHeader {
                        field: ProgramHeaderField::UnsupportedTls,
                        ..
                    }
                ),
                _ => matches!(
                    error.context(),
                    ErrorContext::ProgramHeader {
                        field: ProgramHeaderField::Type,
                        ..
                    }
                ),
            };
            assert!(expected_context, "{error:?}");
        }
    }
}

#[test]
fn inspection_checks_stack_execution_policy() {
    for profile in PROFILES {
        for flags in [PF_R | PF_W, PF_R | PF_W | PF_X] {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    kind: PT_GNU_STACK,
                    flags,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let result = loader(&bytes, profile).admit().unwrap().inspect();
            if flags & PF_X == 0 {
                assert!(result.is_ok());
            } else {
                let error = failure(result);
                assert_error(
                    &error,
                    LoadStage::Inspect,
                    LoadErrorKind::UnsupportedByProfile,
                );
                assert!(matches!(
                    error.context(),
                    ErrorContext::ProgramHeader {
                        field: ProgramHeaderField::ExecutableStack,
                        ..
                    }
                ));
            }
        }
    }
}

#[test]
fn inspection_uses_the_callers_program_header_whitelist() {
    const CUSTOM_HEADER: u32 = 0x6000_0042;
    const ALLOWED: &[u32] = &[PT_NOTE, PT_INTERP, PT_TLS, CUSTOM_HEADER];
    for base in PROFILES {
        let profile = base.with_program_header_policy(ProgramHeaderPolicy::new(ALLOWED, false));
        for &kind in ALLOWED {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    kind,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let image = loader(&bytes, profile).admit().unwrap().inspect().unwrap();
            assert_eq!(image.program_headers()[0].r#type(), kind);
        }
        // The caller's whitelist replaces the defaults instead of adding to them.
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture::load())
            .build();
        let error = failure(loader(&bytes, profile).admit().unwrap().inspect());
        assert_error(
            &error,
            LoadStage::Inspect,
            LoadErrorKind::UnsupportedByProfile,
        );
        assert!(matches!(
            error.context(),
            ErrorContext::ProgramHeader {
                index: 0,
                field: ProgramHeaderField::Type,
                value,
            } if *value == u64::from(PT_LOAD)
        ));
    }
}

#[test]
fn additional_program_headers_extend_one_profile_without_replacing_defaults() {
    for base in PROFILES {
        let mut profile = base;
        profile.set_additional_program_headers(&[PT_TLS]);
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture::load())
            .with_program_header(ProgramHeaderFixture {
                kind: PT_TLS,
                ..ProgramHeaderFixture::load()
            })
            .build();
        assert_eq!(
            loader(&bytes, profile)
                .admit()
                .unwrap()
                .inspect()
                .unwrap()
                .program_headers()
                .len(),
            2
        );
        // Updating this profile must not change another copy's default policy.
        let error = failure(loader(&bytes, base).admit().unwrap().inspect());
        assert_error(
            &error,
            LoadStage::Inspect,
            LoadErrorKind::UnsupportedByProfile,
        );
        assert!(matches!(
            error.context(),
            ErrorContext::ProgramHeader {
                index: 1,
                field: ProgramHeaderField::UnsupportedTls,
                ..
            }
        ));
        profile.set_additional_program_headers(&[]);
        let error = failure(loader(&bytes, profile).admit().unwrap().inspect());
        assert_error(
            &error,
            LoadStage::Inspect,
            LoadErrorKind::UnsupportedByProfile,
        );
    }
}

#[test]
fn additional_program_header_configuration_preserves_other_policy_settings() {
    const CUSTOM_HEADER: u32 = 0x6000_0042;
    for base in PROFILES {
        let profile = base
            .with_program_header_policy(ProgramHeaderPolicy::new(&[PT_GNU_STACK], true))
            .with_additional_program_headers(&[CUSTOM_HEADER, PT_TLS]);
        let mut builder = fixture(profile, ET_DYN);
        for kind in [PT_GNU_STACK, CUSTOM_HEADER, PT_TLS] {
            builder = builder.with_program_header(ProgramHeaderFixture {
                kind,
                flags: PF_R | PF_W | PF_X,
                ..ProgramHeaderFixture::load()
            });
        }
        let bytes = builder.build();
        assert_eq!(
            loader(&bytes, profile)
                .admit()
                .unwrap()
                .inspect()
                .unwrap()
                .program_headers()
                .len(),
            3
        );
        // Extra types must not restore types excluded by a custom base policy.
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture::load())
            .build();
        let error = failure(loader(&bytes, profile).admit().unwrap().inspect());
        assert_error(
            &error,
            LoadStage::Inspect,
            LoadErrorKind::UnsupportedByProfile,
        );
    }
}

#[test]
fn inspection_uses_the_callers_executable_stack_policy() {
    for base in PROFILES {
        for allowed in [false, true] {
            let profile = base.with_program_header_policy(
                base.program_header_policy().with_executable_stack(allowed),
            );
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    kind: PT_NOTE,
                    ..ProgramHeaderFixture::load()
                })
                .with_program_header(ProgramHeaderFixture {
                    kind: PT_GNU_STACK,
                    flags: PF_R | PF_W | PF_X,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let result = loader(&bytes, profile).admit().unwrap().inspect();
            if allowed {
                assert_eq!(result.unwrap().program_headers().len(), 2);
            } else {
                let error = failure(result);
                assert_error(
                    &error,
                    LoadStage::Inspect,
                    LoadErrorKind::UnsupportedByProfile,
                );
                assert!(matches!(
                    error.context(),
                    ErrorContext::ProgramHeader {
                        index: 1,
                        field: ProgramHeaderField::ExecutableStack,
                        ..
                    }
                ));
            }
        }
    }
}

#[test]
fn custom_program_header_policies_preserve_structural_checks() {
    for base in PROFILES {
        let profile = base.with_program_header_policy(ProgramHeaderPolicy::new(
            &[PT_LOAD, PT_TLS, PT_GNU_STACK],
            true,
        ));
        for (kind, offset, filesz, memsz, expected) in [
            (PT_LOAD, 0, 2, 1, LoadErrorKind::BadElf),
            (PT_TLS, 0x1000, 4, 4, LoadErrorKind::OutOfBounds),
        ] {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    kind,
                    offset,
                    filesz,
                    memsz,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let error = failure(loader(&bytes, profile).admit().unwrap().inspect());
            assert_error(&error, LoadStage::Inspect, expected);
        }
        let stack = ProgramHeaderFixture {
            kind: PT_GNU_STACK,
            flags: PF_R | PF_W | PF_X,
            ..ProgramHeaderFixture::load()
        };
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(stack)
            .with_program_header(stack)
            .build();
        let error = failure(loader(&bytes, profile).admit().unwrap().inspect());
        assert_error(&error, LoadStage::Inspect, LoadErrorKind::BadElf);
        assert!(matches!(
            error.context(),
            ErrorContext::ProgramHeader {
                index: 1,
                field: ProgramHeaderField::DuplicateStack,
                ..
            }
        ));
    }
}

#[test]
fn inspection_ignores_undefined_fields_in_null_entries() {
    let profile = LoadProfile::riscv64();
    let bytes = fixture(profile, ET_DYN)
        .with_program_header(ProgramHeaderFixture {
            kind: PT_NULL,
            offset: u64::MAX,
            vaddr: u64::MAX,
            filesz: u64::MAX,
            memsz: u64::MAX,
            ..ProgramHeaderFixture::load()
        })
        .build();
    assert_eq!(
        loader(&bytes, profile)
            .admit()
            .unwrap()
            .inspect()
            .unwrap()
            .program_headers()[0]
            .r#type(),
        PT_NULL
    );
}

#[test]
fn inspection_interprets_processor_specific_headers_by_machine() {
    for profile in PROFILES {
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture {
                kind: 0x7000_0003,
                ..ProgramHeaderFixture::load()
            })
            .build();
        let result = loader(&bytes, profile).admit().unwrap().inspect();
        if profile == LoadProfile::aarch64() {
            assert_error(
                &failure(result),
                LoadStage::Inspect,
                LoadErrorKind::UnsupportedByProfile,
            );
        } else {
            assert!(result.is_ok());
        }
    }
}
