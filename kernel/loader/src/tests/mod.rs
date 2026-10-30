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

//! Reader, ABI-policy and staged ELF-inspection tests.

mod fixture;
mod image;

use blueos_test_macro::test;
use goblin::elf::{
    header::{EM_AARCH64, EM_RISCV, ET_DYN},
    Elf,
};

use crate::{
    error::{ErrorContext, LoadErrorKind, LoadStage},
    profile::LoadProfile,
    reader::ElfReader,
    LoadError,
};
use fixture::{ElfFixtureBuilder, SliceElfReader};

#[test]
fn fixture_builder_emits_a_parseable_elf32_header() {
    let bytes = ElfFixtureBuilder::elf32(EM_RISCV, ET_DYN).build();
    let elf = Elf::parse(&bytes).expect("valid ELF32 fixture");
    assert_eq!(elf.header.e_machine, EM_RISCV);
    assert_eq!(elf.header.e_type, ET_DYN);
    assert!(!elf.is_64);
    assert!(elf.little_endian);
}

#[test]
fn fixture_builder_emits_parseable_elf64_headers() {
    for machine in [EM_RISCV, EM_AARCH64] {
        let bytes = ElfFixtureBuilder::elf64(machine, ET_DYN).build();
        let elf = Elf::parse(&bytes).expect("valid ELF64 fixture");
        assert_eq!(elf.header.e_machine, machine);
        assert_eq!(elf.header.e_type, ET_DYN);
        assert!(elf.is_64);
        assert!(elf.little_endian);
    }
}

#[test]
fn reader_supports_independent_positional_reads() {
    let bytes = ElfFixtureBuilder::elf64(EM_RISCV, ET_DYN).build();
    let reader = SliceElfReader::new(&bytes);
    assert_eq!(reader.len().unwrap(), bytes.len() as u64);
    assert!(!reader.is_empty().unwrap());
    let mut machine = [0; 2];
    let mut magic = [0; 4];
    reader.read_exact_at(18, &mut machine).unwrap();
    reader.read_exact_at(0, &mut magic).unwrap();
    assert_eq!(u16::from_le_bytes(machine), EM_RISCV);
    assert_eq!(&magic, b"\x7fELF");
}

#[test]
fn reader_allows_empty_reads_at_the_end() {
    let bytes = [1, 2, 3];
    let reader = SliceElfReader::new(&bytes);
    reader.read_exact_at(3, &mut []).unwrap();
    let empty = SliceElfReader::new(&[]);
    assert!(empty.is_empty().unwrap());
    empty.read_exact_at(0, &mut []).unwrap();
}

#[test]
fn reader_rejects_truncated_and_outside_ranges_without_copying() {
    let reader = SliceElfReader::new(&[1, 2, 3]);
    for offset in [2, 4, u64::MAX - 2] {
        let mut dst = [0xaa; 2];
        let error = reader.read_exact_at(offset, &mut dst).unwrap_err();
        assert!(matches!(error.kind(), LoadErrorKind::OutOfBounds));
        assert!(matches!(error.context(), ErrorContext::FileRange {
            offset: actual, len: 2, file_len: 3,
        } if *actual == offset));
        assert_eq!(dst, [0xaa; 2]);
    }
    assert!(reader.read_exact_at(4, &mut []).is_err());
}

#[test]
fn reader_reports_range_overflow_without_copying() {
    let reader = SliceElfReader::new(&[1]);
    let mut dst = [0xaa; 2];
    let error = reader.read_exact_at(u64::MAX, &mut dst).unwrap_err();
    assert!(matches!(error.kind(), LoadErrorKind::IntegerOverflow));
    assert!(matches!(
        error.context(),
        ErrorContext::FileRange {
            offset: u64::MAX,
            len: 2,
            file_len: 1,
        }
    ));
    assert_eq!(dst, [0xaa; 2]);
}

#[test]
fn error_wrapping_preserves_original_stage_and_range() {
    let error = LoadError::new(
        LoadErrorKind::Io,
        ErrorContext::FileRange {
            offset: 7,
            len: 4,
            file_len: 8,
        },
    )
    .at_stage(LoadStage::Admit)
    .at_stage(LoadStage::Beginning)
    .with_context(ErrorContext::FileRange {
        offset: 0,
        len: 1,
        file_len: 1,
    });
    assert!(matches!(error.kind(), LoadErrorKind::Io));
    assert!(matches!(error.stage(), Some(LoadStage::Admit)));
    assert!(matches!(
        error.context(),
        ErrorContext::FileRange {
            offset: 7,
            len: 4,
            file_len: 8,
        }
    ));
}

#[test]
fn error_wrapping_attaches_missing_context() {
    let error = LoadError::new(LoadErrorKind::Io, ErrorContext::None).with_context(
        ErrorContext::FileRange {
            offset: 1,
            len: 2,
            file_len: 3,
        },
    );
    assert!(error.stage().is_none());
    assert!(matches!(
        error.context(),
        ErrorContext::FileRange {
            offset: 1,
            len: 2,
            file_len: 3,
        }
    ));
}

#[test]
fn riscv_profiles_reject_incompatible_abi_flags() {
    for profile in [LoadProfile::riscv32(), LoadProfile::riscv64()] {
        // RVC and the unrelated TSO flag do not change the soft-float ABI.
        for flags in [0, 1, 0x10, 0x11] {
            assert!(profile.header_flags().accepts(flags));
        }
        for flags in [2, 4, 6, 8, 9] {
            assert!(!profile.header_flags().accepts(flags));
        }
    }
}

#[test]
fn aarch64_profile_rejects_reserved_flags() {
    let profile = LoadProfile::aarch64();
    assert!(profile.header_flags().accepts(0));
    for flags in [1, 0x8000_0000, u32::MAX] {
        assert!(!profile.header_flags().accepts(flags));
    }
}
