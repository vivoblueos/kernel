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

//! Read-only layout, resource bounds, permission policy and reader ownership.

use super::fixture::{ElfFixtureBuilder, ProgramHeaderFixture, SliceElfReader};
use crate::{
    error::{ErrorContext, HeaderField, LimitKind, LoadErrorKind, LoadStage, ProgramHeaderField},
    image::{ImageLoader, LoadRequest, PlannedImage},
    memory::{MemoryPermissions, TargetAddress},
    profile::{ElfClass, ElfMachine, LoadLimits, LoadProfile, SegmentPermissionPolicy},
    reader::ElfReader,
    LoadError, LoadResult,
};
use blueos_test_macro::test;
use core::cell::Cell;
use goblin::elf::{
    header::{EM_AARCH64, EM_RISCV, ET_DYN, ET_EXEC},
    program_header::{PF_R, PF_W, PF_X, PT_GNU_RELRO, PT_GNU_STACK, PT_LOAD, PT_NOTE, PT_NULL},
};

const PROFILES: [LoadProfile; 3] = [
    LoadProfile::riscv32(),
    LoadProfile::riscv64(),
    LoadProfile::aarch64(),
];

fn fixture(profile: LoadProfile, kind: u16) -> ElfFixtureBuilder {
    let machine = match profile.machine() {
        ElfMachine::Riscv => EM_RISCV,
        ElfMachine::Aarch64 => EM_AARCH64,
        ElfMachine::Other(machine) => machine,
    };
    match profile.class() {
        ElfClass::Elf32 => ElfFixtureBuilder::elf32(machine, kind),
        ElfClass::Elf64 => ElfFixtureBuilder::elf64(machine, kind),
    }
    .with_entry(0x1000)
}

fn plan(
    bytes: &[u8],
    profile: LoadProfile,
    limits: LoadLimits,
) -> LoadResult<PlannedImage<SliceElfReader<'_>>> {
    ImageLoader::new(
        SliceElfReader::new(bytes),
        LoadRequest::new(profile, limits),
    )
    .admit()?
    .inspect()?
    .plan()
}

fn failure<T>(result: LoadResult<T>) -> LoadError {
    match result {
        Err(error) => error,
        Ok(_) => panic!("invalid layout accepted"),
    }
}

fn assert_plan_error(error: &LoadError, kind: LoadErrorKind) {
    assert_eq!(error.stage(), Some(LoadStage::Plan), "{error:?}");
    assert_eq!(error.kind(), kind, "{error:?}");
}

#[must_use = "the observed reader tracks the owned input lifetime"]
struct ObservedReader<'a> {
    bytes: &'a [u8],
    reads: &'a Cell<usize>,
    drops: &'a Cell<usize>,
}
impl ElfReader for ObservedReader<'_> {
    fn len(&self) -> LoadResult<u64> {
        Ok(self.bytes.len() as u64)
    }
    fn read_exact_at(&self, offset: u64, dst: &mut [u8]) -> LoadResult<()> {
        self.reads.set(self.reads.get() + 1);
        SliceElfReader::new(self.bytes).read_exact_at(offset, dst)
    }
}
impl Drop for ObservedReader<'_> {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

#[test]
fn planning_sorts_segments_and_preserves_header_indices() {
    for profile in PROFILES {
        for kind in [ET_DYN, ET_EXEC] {
            let bytes = fixture(profile, kind)
                .with_program_header(ProgramHeaderFixture {
                    vaddr: TargetAddress::new(0x1100),
                    flags: PF_R | PF_W,
                    ..ProgramHeaderFixture::load()
                })
                .with_program_header(ProgramHeaderFixture {
                    kind: PT_NOTE,
                    ..ProgramHeaderFixture::load()
                })
                .with_program_header(ProgramHeaderFixture::load())
                .build();
            let image = plan(&bytes, profile, LoadLimits::DEFAULT).unwrap();
            assert_eq!(image.segments().len(), 2);
            assert_eq!(image.segments()[0].index(), 2);
            assert_eq!(image.segments()[1].index(), 0);
            assert_eq!(image.image_range().start().get(), 0x1000);
            assert_eq!(image.image_range().len(), 0x200);
            assert_eq!(image.entry().get(), 0x1000);
            assert_eq!(image.segments()[0].file_range().offset(), 0);
            assert_eq!(image.segments()[0].file_range().len(), 4);
        }
    }
}

#[test]
fn planning_uses_normalized_segment_alignment() {
    for profile in PROFILES {
        for (align, expected) in [(0, 1), (1, 1), (4, 4)] {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    align,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let image = plan(&bytes, profile, LoadLimits::DEFAULT).unwrap();
            assert_eq!(image.max_alignment(), expected);
            assert_eq!(image.segments()[0].align(), expected);
            assert_eq!(image.image_range().len(), 0x100);
        }
    }
}

#[test]
fn planning_accepts_matching_alignment_remainders() {
    for profile in PROFILES {
        let bytes = fixture(profile, ET_DYN)
            .with_entry(0x1004)
            .with_program_header(ProgramHeaderFixture {
                offset: 4,
                vaddr: TargetAddress::new(0x1004),
                align: 0x1000,
                ..ProgramHeaderFixture::load()
            })
            .build();
        let image = plan(&bytes, profile, LoadLimits::DEFAULT).unwrap();
        assert_eq!(image.image_range().start().get(), 0x1000);
        assert_eq!(image.image_range().len(), 0x1000);
        assert_eq!(image.max_alignment(), 0x1000);
    }
}

#[test]
fn planning_rejects_invalid_segment_alignment() {
    for profile in PROFILES {
        for (align, vaddr, kind) in [
            (3, 0x1000, LoadErrorKind::InvalidAlignment),
            (4, 0x1002, LoadErrorKind::BadElf),
        ] {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    align,
                    vaddr: TargetAddress::new(vaddr),
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let error = failure(plan(&bytes, profile, LoadLimits::DEFAULT));
            assert_plan_error(&error, kind);
            assert!(
                matches!(error.context(), ErrorContext::ProgramHeader { index: 0, field: ProgramHeaderField::Align, value } if *value == align)
            );
        }
    }
}

#[test]
fn planning_ignores_empty_segments_in_layout_geometry() {
    for profile in PROFILES {
        for (vaddr, align) in [(0, 3), (0x1080, 0), (0x8000_0000, 0x8000_0000)] {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    vaddr: TargetAddress::new(vaddr),
                    align,
                    filesz: 0,
                    memsz: 0,
                    flags: PF_W | PF_X,
                    ..ProgramHeaderFixture::load()
                })
                .with_program_header(ProgramHeaderFixture::load())
                .build();
            let image = plan(&bytes, profile, LoadLimits::DEFAULT).unwrap();
            assert_eq!(image.segments().len(), 1);
            assert_eq!(image.segments()[0].index(), 1);
            assert_eq!(image.image_range().start().get(), 0x1000);
            assert_eq!(image.image_range().len(), 0x100);
            assert_eq!(image.max_alignment(), 4);
        }
    }
}

#[test]
fn planning_rejects_missing_and_empty_load_segments() {
    for profile in PROFILES {
        for bytes in [
            fixture(profile, ET_EXEC).build(),
            fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    kind: PT_NOTE,
                    ..ProgramHeaderFixture::load()
                })
                .build(),
            fixture(profile, ET_EXEC)
                .with_program_header(ProgramHeaderFixture {
                    filesz: 0,
                    memsz: 0,
                    ..ProgramHeaderFixture::load()
                })
                .build(),
        ] {
            assert_plan_error(
                &failure(plan(&bytes, profile, LoadLimits::DEFAULT)),
                LoadErrorKind::BadElf,
            );
        }
    }
}

#[test]
fn planning_detects_overlap_across_empty_segments() {
    for profile in PROFILES {
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture {
                memsz: 0x200,
                ..ProgramHeaderFixture::load()
            })
            .with_program_header(ProgramHeaderFixture {
                vaddr: TargetAddress::new(0x1080),
                filesz: 0,
                memsz: 0,
                ..ProgramHeaderFixture::load()
            })
            .with_program_header(ProgramHeaderFixture {
                vaddr: TargetAddress::new(0x1100),
                ..ProgramHeaderFixture::load()
            })
            .build();
        let error = failure(plan(&bytes, profile, LoadLimits::DEFAULT));
        assert_plan_error(&error, LoadErrorKind::BadElf);
        assert!(matches!(
            error.context(),
            ErrorContext::ProgramHeader {
                index: 2,
                field: ProgramHeaderField::VirtualRange,
                value: 0x1100
            }
        ));
    }
}

#[test]
fn metadata_headers_do_not_consume_load_segment_budget() {
    for profile in PROFILES {
        for count in [33, 128, 129] {
            let mut builder =
                fixture(profile, ET_DYN).with_program_header(ProgramHeaderFixture::load());
            for index in 1..count {
                builder = builder.with_program_header(ProgramHeaderFixture {
                    kind: if index % 2 == 0 { PT_NOTE } else { PT_NULL },
                    ..ProgramHeaderFixture::load()
                });
            }
            let bytes = builder.build();
            let result = plan(
                &bytes,
                profile,
                LoadLimits::DEFAULT.with_max_load_segments(1),
            );
            if count <= 128 {
                assert_eq!(result.unwrap().segments().len(), 1);
            } else {
                let error = failure(result);
                assert_eq!(error.stage(), Some(LoadStage::Admit));
                assert!(matches!(
                    error.context(),
                    ErrorContext::Limit {
                        resource: LimitKind::ProgramHeaderCount,
                        actual: 129,
                        maximum: 128
                    }
                ));
            }
        }
    }
}

#[test]
fn inspection_counts_empty_load_segments_and_stops_at_budget() {
    for profile in PROFILES {
        for maximum in [0, 1, 2, 32] {
            let mut builder = fixture(profile, ET_DYN).with_program_header(ProgramHeaderFixture {
                kind: PT_NOTE,
                ..ProgramHeaderFixture::load()
            });
            for _index in 0..maximum + 2 {
                builder = builder.with_program_header(ProgramHeaderFixture {
                    filesz: 0,
                    memsz: 0,
                    ..ProgramHeaderFixture::load()
                });
            }
            let bytes = builder.build();
            let reads = Cell::new(0);
            let drops = Cell::new(0);
            let reader = ObservedReader {
                bytes: &bytes,
                reads: &reads,
                drops: &drops,
            };
            let error = failure(
                ImageLoader::new(
                    reader,
                    LoadRequest::new(profile, LoadLimits::DEFAULT.with_max_load_segments(maximum)),
                )
                .admit()
                .unwrap()
                .inspect(),
            );
            assert_eq!(error.stage(), Some(LoadStage::Inspect));
            assert_eq!(error.kind(), LoadErrorKind::ResourceLimit);
            assert!(
                matches!(error.context(), ErrorContext::Limit { resource: LimitKind::LoadSegmentCount, actual, maximum: reported } if *actual == u64::from(maximum) + 1 && *reported == u64::from(maximum))
            );
            assert_eq!(reads.get(), usize::from(maximum) + 4);
            assert_eq!(drops.get(), 1);
        }
    }
}

#[test]
fn planning_budgets_include_holes_and_alignment_padding() {
    for profile in PROFILES {
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture {
                align: 0x1000,
                ..ProgramHeaderFixture::load()
            })
            .with_program_header(ProgramHeaderFixture {
                vaddr: TargetAddress::new(0x3000),
                align: 0x1000,
                ..ProgramHeaderFixture::load()
            })
            .build();
        let limits = LoadLimits::new(64 * 1024 * 1024, 128, 32, 0x3000, 0x1000);
        assert_eq!(LoadLimits::DEFAULT, LoadLimits::default());
        assert_eq!(
            plan(&bytes, profile, limits).unwrap().image_range().len(),
            0x3000
        );
        for (limits, resource) in [
            (limits.with_max_image_span(0x2fff), LimitKind::ImageSpan),
            (
                limits.with_max_segment_alignment(0xfff),
                LimitKind::SegmentAlignment,
            ),
        ] {
            let error = failure(plan(&bytes, profile, limits));
            assert_plan_error(&error, LoadErrorKind::ResourceLimit);
            assert!(matches!(
                (error.context(), resource),
                (
                    ErrorContext::Limit {
                        resource: LimitKind::ImageSpan,
                        actual: 0x3000,
                        maximum: 0x2fff
                    },
                    LimitKind::ImageSpan
                ) | (
                    ErrorContext::Limit {
                        resource: LimitKind::SegmentAlignment,
                        actual: 0x1000,
                        maximum: 0xfff
                    },
                    LimitKind::SegmentAlignment
                )
            ));
        }
    }
}

#[test]
fn planning_checks_elf32_endpoints_independently_of_host_width() {
    let profile = LoadProfile::riscv32();
    for (memsz, align, valid) in [(0xfff, 1, true), (0x1000, 1, false), (0xfff, 0x1000, false)] {
        let bytes = fixture(profile, ET_EXEC)
            .with_entry(0xffff_f000)
            .with_program_header(ProgramHeaderFixture {
                vaddr: TargetAddress::new(0xffff_f000),
                memsz,
                align,
                ..ProgramHeaderFixture::load()
            })
            .build();
        let result = plan(&bytes, profile, LoadLimits::DEFAULT);
        if valid {
            assert_eq!(
                result.unwrap().image_range().end().unwrap().get(),
                u64::from(u32::MAX)
            );
        } else {
            assert_plan_error(&failure(result), LoadErrorKind::OutOfBounds);
        }
    }
}

#[test]
fn planning_rejects_alignment_overflow_at_elf64_endpoint() {
    for profile in [LoadProfile::riscv64(), LoadProfile::aarch64()] {
        let start = u64::MAX - 0xff;
        let bytes = fixture(profile, ET_EXEC)
            .with_entry(start)
            .with_program_header(ProgramHeaderFixture {
                vaddr: TargetAddress::new(start),
                memsz: 0x80,
                align: 0x100,
                ..ProgramHeaderFixture::load()
            })
            .build();
        assert_plan_error(
            &failure(plan(&bytes, profile, LoadLimits::DEFAULT)),
            LoadErrorKind::IntegerOverflow,
        );
    }
}

#[test]
fn planning_requires_a_nonzero_aligned_executable_entry() {
    for profile in PROFILES {
        for (entry, flags, kind) in [
            (0, PF_R | PF_X, LoadErrorKind::BadElf),
            (0x1001, PF_R | PF_X, LoadErrorKind::InvalidAlignment),
            (0x2000, PF_R | PF_X, LoadErrorKind::PermissionConflict),
            (0x1000, PF_R, LoadErrorKind::PermissionConflict),
        ] {
            let bytes = fixture(profile, ET_EXEC)
                .with_entry(entry)
                .with_program_header(ProgramHeaderFixture {
                    flags,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let error = failure(plan(&bytes, profile, LoadLimits::DEFAULT));
            assert_plan_error(&error, kind);
            if entry == 0 {
                assert!(matches!(
                    error.context(),
                    ErrorContext::HeaderField {
                        field: HeaderField::Entry,
                        value: 0
                    }
                ));
            }
        }
    }
}

#[test]
fn planning_requires_a_whole_instruction_in_one_segment() {
    for profile in PROFILES {
        let size = u64::from(profile.entry_mode().minimum_instruction_size());
        for (memsz, valid) in [(size - 1, false), (size, true)] {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture {
                    memsz,
                    filesz: 0,
                    align: 1,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let result = plan(&bytes, profile, LoadLimits::DEFAULT);
            if valid {
                assert_eq!(result.unwrap().entry().get(), 0x1000);
            } else {
                assert_plan_error(&failure(result), LoadErrorKind::PermissionConflict);
            }
        }
        let half = size / 2;
        let bytes = fixture(profile, ET_DYN)
            .with_program_header(ProgramHeaderFixture {
                memsz: half,
                filesz: 0,
                align: 1,
                ..ProgramHeaderFixture::load()
            })
            .with_program_header(ProgramHeaderFixture {
                vaddr: TargetAddress::new(0x1000 + half),
                memsz: half,
                filesz: 0,
                align: 1,
                ..ProgramHeaderFixture::load()
            })
            .build();
        assert_plan_error(
            &failure(plan(&bytes, profile, LoadLimits::DEFAULT)),
            LoadErrorKind::PermissionConflict,
        );
    }
}

fn image_with_data(profile: LoadProfile, flags: u32) -> alloc::vec::Vec<u8> {
    fixture(profile, ET_DYN)
        .with_program_header(ProgramHeaderFixture::load())
        .with_program_header(ProgramHeaderFixture {
            vaddr: TargetAddress::new(0x2000),
            flags,
            ..ProgramHeaderFixture::load()
        })
        .build()
}

#[test]
fn planning_applies_default_exact_permission_combinations() {
    for profile in PROFILES {
        for (flags, valid) in [
            (PF_R, true),
            (PF_R | PF_W, true),
            (PF_R | PF_X, true),
            (0, false),
            (PF_W, false),
            (PF_X, false),
            (PF_W | PF_X, false),
            (PF_R | PF_W | PF_X, false),
        ] {
            let bytes = image_with_data(profile, flags);
            let result = plan(&bytes, profile, LoadLimits::DEFAULT);
            if valid {
                assert_eq!(result.unwrap().segments().len(), 2);
            } else {
                let error = failure(result);
                let kind = if flags & PF_W != 0 && flags & PF_X != 0 {
                    LoadErrorKind::PermissionConflict
                } else {
                    LoadErrorKind::UnsupportedByProfile
                };
                assert_plan_error(&error, kind);
                assert!(
                    matches!(error.context(), ErrorContext::ProgramHeader { index: 1, field: ProgramHeaderField::Permissions, value } if *value == u64::from(flags))
                );
            }
        }
    }
}

#[test]
fn permission_extensions_preserve_other_combinations_and_profiles() {
    let wx = MemoryPermissions::WRITE.bitor(MemoryPermissions::EXECUTE);
    for base in PROFILES {
        let policy = SegmentPermissionPolicy::DEFAULT.with_permissions(wx, true);
        let profile = base.with_segment_permission_policy(policy);
        let bytes = image_with_data(profile, PF_W | PF_X);
        assert!(plan(&bytes, profile, LoadLimits::DEFAULT).is_ok());
        for rejected in [
            base,
            profile.with_segment_permission_policy(policy.with_permissions(wx, false)),
        ] {
            assert_plan_error(
                &failure(plan(&bytes, rejected, LoadLimits::DEFAULT)),
                LoadErrorKind::PermissionConflict,
            );
        }
        let bytes = image_with_data(profile, PF_R | PF_W | PF_X);
        assert_plan_error(
            &failure(plan(&bytes, profile, LoadLimits::DEFAULT)),
            LoadErrorKind::PermissionConflict,
        );
        let restricted = base.with_segment_permission_policy(SegmentPermissionPolicy::new(&[
            MemoryPermissions::READ.bitor(MemoryPermissions::EXECUTE),
            wx,
        ]));
        assert!(plan(
            &image_with_data(restricted, PF_W | PF_X),
            restricted,
            LoadLimits::DEFAULT
        )
        .is_ok());
        assert_plan_error(
            &failure(plan(
                &image_with_data(restricted, PF_R | PF_W),
                restricted,
                LoadLimits::DEFAULT,
            )),
            LoadErrorKind::UnsupportedByProfile,
        );
    }
}

#[test]
fn stack_and_segment_permission_policies_are_independent() {
    let rwx = MemoryPermissions::READ
        .bitor(MemoryPermissions::WRITE)
        .bitor(MemoryPermissions::EXECUTE);
    for base in PROFILES {
        let segment_allowed = base.with_segment_permission_policy(
            SegmentPermissionPolicy::DEFAULT.with_permissions(rwx, true),
        );
        let bytes = fixture(base, ET_DYN)
            .with_program_header(ProgramHeaderFixture {
                flags: PF_R | PF_W | PF_X,
                ..ProgramHeaderFixture::load()
            })
            .with_program_header(ProgramHeaderFixture {
                kind: PT_GNU_STACK,
                flags: PF_R | PF_W | PF_X,
                ..ProgramHeaderFixture::load()
            })
            .build();
        let error = failure(plan(&bytes, segment_allowed, LoadLimits::DEFAULT));
        assert_eq!(error.stage(), Some(LoadStage::Inspect));
        assert!(matches!(
            error.context(),
            ErrorContext::ProgramHeader {
                field: ProgramHeaderField::ExecutableStack,
                ..
            }
        ));
        let stack_allowed = base
            .with_program_header_policy(base.program_header_policy().with_executable_stack(true));
        assert_plan_error(
            &failure(plan(&bytes, stack_allowed, LoadLimits::DEFAULT)),
            LoadErrorKind::PermissionConflict,
        );
        let both = segment_allowed
            .with_program_header_policy(base.program_header_policy().with_executable_stack(true));
        assert!(plan(&bytes, both, LoadLimits::DEFAULT).is_ok());
    }
}

#[test]
fn planning_requires_relro_within_one_writable_segment() {
    for profile in PROFILES {
        for (vaddr, len, valid) in [
            (0x2000, 0x100, true),
            (0x2040, 0x40, true),
            (0x1000, 0x40, false),
            (0x20f0, 0x20, false),
            (0x3000, 1, false),
        ] {
            let bytes = fixture(profile, ET_DYN)
                .with_program_header(ProgramHeaderFixture::load())
                .with_program_header(ProgramHeaderFixture {
                    vaddr: TargetAddress::new(0x2000),
                    flags: PF_R | PF_W,
                    ..ProgramHeaderFixture::load()
                })
                .with_program_header(ProgramHeaderFixture {
                    kind: PT_GNU_RELRO,
                    vaddr: TargetAddress::new(vaddr),
                    filesz: 0,
                    memsz: len,
                    ..ProgramHeaderFixture::load()
                })
                .build();
            let result = plan(&bytes, profile, LoadLimits::DEFAULT);
            if valid {
                assert!(result.is_ok());
            } else {
                assert_plan_error(&failure(result), LoadErrorKind::PermissionConflict);
            }
        }
    }
}

#[test]
fn planning_retains_reader_without_further_io() {
    for profile in PROFILES {
        for valid in [true, false] {
            let bytes = fixture(profile, ET_DYN)
                .with_entry(if valid { 0x1000 } else { 0 })
                .with_program_header(ProgramHeaderFixture::load())
                .build();
            let reads = Cell::new(0);
            let drops = Cell::new(0);
            let reader = ObservedReader {
                bytes: &bytes,
                reads: &reads,
                drops: &drops,
            };
            let inspected =
                ImageLoader::new(reader, LoadRequest::new(profile, LoadLimits::DEFAULT))
                    .admit()
                    .unwrap()
                    .inspect()
                    .unwrap();
            let previous_reads = reads.get();
            assert_eq!(drops.get(), 0);
            let result = inspected.plan();
            assert_eq!(reads.get(), previous_reads);
            if valid {
                let image = result.expect("valid layout");
                assert_eq!(drops.get(), 0);
                drop(image);
            } else {
                assert_plan_error(&failure(result), LoadErrorKind::BadElf);
            }
            assert_eq!(drops.get(), 1);
        }
    }
}
