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

use goblin::elf::{
    header::{EM_ARM, EM_RISCV, ET_DYN},
    Elf,
};

use crate::tests::fixture::ElfFixtureBuilder;

mod fixture;

#[test]
fn fixture_builder_emits_a_parseable_elf64_header() {
    let bytes = ElfFixtureBuilder::elf64(EM_RISCV, ET_DYN).build();
    let elf = Elf::parse(&bytes).expect("fixture must contain a valid ELF header");

    assert_eq!(elf.header.e_machine, EM_RISCV);
    assert_eq!(elf.header.e_type, ET_DYN);
    assert!(elf.is_64);
    assert!(elf.little_endian);
}

/// SONAME relaxation: a shared object without `DT_SONAME` is a normal
/// dependency; a root or static PIE without one always was. The remaining
/// hard requirement is `PT_DYNAMIC` for a shared object.
mod soname_relaxation {
    use std::vec::Vec;

    use goblin::elf::header::{EM_RISCV, ET_DYN};

    use crate::{
        dynamic_linker::ArtifactRole,
        error::{LoadErrorKind, ProgramHeaderField},
        identity::{ElfType, LoadLimits, LoadProfile, LoadRequest},
        image::ImageLoader,
        reader::SliceElfReader,
        tests::fixture::ElfFixtureBuilder,
    };

    fn dyn_request() -> LoadRequest {
        LoadRequest::new(LoadProfile::riscv64(ElfType::Dyn), LoadLimits::DEFAULT)
    }

    /// One PT_LOAD (r-x, entry inside) plus a PT_DYNAMIC with a single
    /// DT_NULL entry: a valid shared object that declares no SONAME and no
    /// dependencies. The load segment must cover the dynamic table's file
    /// range (the builder appends the PT_DYNAMIC after the PT_LOAD header).
    fn no_soname_dso_bytes() -> Vec<u8> {
        ElfFixtureBuilder::elf64(EM_RISCV, ET_DYN)
            .with_load_segment(0x1000, 0x200, 0x200, 0x4)
            .with_dynamic_segment(0x1000)
            .build()
    }

    #[test]
    fn shared_object_without_soname_passes_inspect() {
        let bytes = no_soname_dso_bytes();
        let result = ImageLoader::new(SliceElfReader::new(&bytes), dyn_request())
            .admit()
            .expect("admit")
            .with_role(ArtifactRole::SharedObject)
            .inspect();
        assert!(
            result.is_ok(),
            "a SharedObject without DT_SONAME must pass inspect: {:?}",
            result.err()
        );
    }

    #[test]
    fn root_without_dynamic_table_passes_inspect() {
        // A static PIE root: one PT_LOAD, no PT_DYNAMIC, no SONAME, no
        // DT_NEEDED — inspect must accept it.
        let bytes = ElfFixtureBuilder::elf64(EM_RISCV, ET_DYN)
            .with_load_segment(0x1000, 0x100, 0x100, 0x4)
            .with_entry(0x1000)
            .build();
        let result = ImageLoader::new(SliceElfReader::new(&bytes), dyn_request())
            .admit()
            .expect("admit")
            .inspect();
        assert!(
            result.is_ok(),
            "a root without PT_DYNAMIC must pass inspect: {:?}",
            result.err()
        );
    }

    #[test]
    fn shared_object_without_dynamic_table_is_bad_elf() {
        // PT_DYNAMIC is still required for a shared object — its symbols and
        // relocations live there — but the error is a plain program-header
        // BadElf, not SONAME-flavored.
        let bytes = ElfFixtureBuilder::elf64(EM_RISCV, ET_DYN)
            .with_load_segment(0x1000, 0x100, 0x100, 0x4)
            .build();
        let error = match ImageLoader::new(SliceElfReader::new(&bytes), dyn_request())
            .admit()
            .expect("admit")
            .with_role(ArtifactRole::SharedObject)
            .inspect()
        {
            Ok(_) => panic!("a SharedObject without PT_DYNAMIC must be rejected"),
            Err(error) => error,
        };
        assert!(matches!(error.kind(), LoadErrorKind::BadElf));
        assert!(matches!(
            error.context(),
            crate::error::ErrorContext::ProgramHeader { .. }
        ));
        let _ = ProgramHeaderField::Type;
    }
}

/// read-only dependency scan: the scanner must see the same SONAME and
/// `DT_NEEDED` set the real pipeline would decode, without any allocation.
mod dependency_scan {
    use goblin::elf::{
        dynamic::{DT_NEEDED, DT_SONAME, DT_STRSZ, DT_STRTAB},
        header::{EM_RISCV, ET_DYN},
    };

    use crate::{
        dynamic_linker::ArtifactRole,
        identity::{ElfType, LoadLimits, LoadProfile},
        image::scan::scan_artifact,
        reader::SliceElfReader,
        tests::fixture::ElfFixtureBuilder,
    };

    fn profile() -> LoadProfile {
        LoadProfile::riscv64(ElfType::Dyn)
    }

    /// A dynamic-area convention shared by these fixtures: one PT_LOAD (r-x,
    /// vaddr 0x1000) whose 0x100-byte file range starts right after the ELF
    /// header, so the dynamic table and dynstr — appended after the program
    /// headers — land inside it with `vaddr = 0x1000 + (file - 0x40)`.
    fn scanned_dso(entries: &[(u64, u64)], dynstr: &[u8]) -> std::vec::Vec<u8> {
        // File layout: ehdr (0x40) | PT_LOAD phdr | PT_DYNAMIC phdr | dynamic
        // table | dynstr. The single PT_LOAD maps file offset 0x40 (its own
        // phdr) to vaddr 0x1000 with 0x100 bytes, so vaddr = 0x1000 + (x -
        // 0x40) for every covered file offset x, and the dynamic table and
        // dynstr — appended after the phdrs — land inside that range.
        const EHDR: u64 = 0x40;
        const PHDR: u64 = 0x38;
        const LOAD_BASE: u64 = 0x1000;
        let dyn_file = EHDR + 2 * PHDR;
        // strtab/strsz entries + the caller's entries + the DT_NULL terminator
        let table_len = (2 + entries.len() + 1) as u64 * 16;
        let strtab_file = dyn_file + table_len;
        let to_vaddr = |file: u64| LOAD_BASE + file - EHDR;

        let mut all_entries: std::vec::Vec<(u32, u64)> = std::vec![
            (DT_STRTAB as u32, to_vaddr(strtab_file)),
            (DT_STRSZ as u32, dynstr.len() as u64),
        ];
        all_entries.extend(entries.iter().map(|&(tag, value)| (tag as u32, value)));
        let bytes = ElfFixtureBuilder::elf64(EM_RISCV, ET_DYN)
            .with_load_segment(LOAD_BASE, 0x100, 0x100, 0x4)
            .with_dynamic_entries(to_vaddr(dyn_file), &all_entries)
            .with_dynstr(strtab_file as usize, dynstr)
            .build();
        debug_assert!(strtab_file as usize + dynstr.len() <= bytes.len());
        bytes
    }

    #[test]
    fn scan_reads_soname_and_needed_in_order() {
        // dynstr: "libc.so.1\0libfoo.so.1\0self.so\0" — offsets 0, 10, 22
        let dynstr: &[u8] = b"libc.so.1\0libfoo.so.1\0self.so\0";
        let bytes = scanned_dso(&[(DT_NEEDED, 0), (DT_NEEDED, 10), (DT_SONAME, 22)], dynstr);
        let scanned = scan_artifact(
            &SliceElfReader::new(&bytes),
            profile(),
            ArtifactRole::SharedObject,
            LoadLimits::DEFAULT,
        )
        .expect("scan");
        assert_eq!(
            scanned.declared_soname.as_ref().unwrap().as_bytes(),
            b"self.so"
        );
        assert_eq!(scanned.needed.len(), 2);
        assert_eq!(scanned.needed[0].as_bytes(), b"libc.so.1");
        assert_eq!(scanned.needed[1].as_bytes(), b"libfoo.so.1");
    }

    #[test]
    fn scan_accepts_dso_without_soname() {
        let dynstr: &[u8] = b"libc.so.1\0";
        let bytes = scanned_dso(&[(DT_NEEDED, 0)], dynstr);
        let scanned = scan_artifact(
            &SliceElfReader::new(&bytes),
            profile(),
            ArtifactRole::SharedObject,
            LoadLimits::DEFAULT,
        )
        .expect("scan");
        assert!(scanned.declared_soname.is_none());
        assert_eq!(scanned.needed.len(), 1);
        assert_eq!(scanned.needed[0].as_bytes(), b"libc.so.1");
    }

    #[test]
    fn scan_returns_empty_for_root_without_dynamic() {
        // A static PIE root: one PT_LOAD, no PT_DYNAMIC.
        let bytes = ElfFixtureBuilder::elf64(EM_RISCV, ET_DYN)
            .with_load_segment(0x1000, 0x100, 0x100, 0x4)
            .with_entry(0x1000)
            .build();
        let scanned = scan_artifact(
            &SliceElfReader::new(&bytes),
            profile(),
            ArtifactRole::ExecutableRoot,
            LoadLimits::DEFAULT,
        )
        .expect("scan");
        assert!(scanned.declared_soname.is_none());
        assert!(scanned.needed.is_empty());
    }

    #[test]
    fn scan_rejects_dso_without_dynamic() {
        let bytes = ElfFixtureBuilder::elf64(EM_RISCV, ET_DYN)
            .with_load_segment(0x1000, 0x100, 0x100, 0x4)
            .build();
        let result = scan_artifact(
            &SliceElfReader::new(&bytes),
            profile(),
            ArtifactRole::SharedObject,
            LoadLimits::DEFAULT,
        );
        assert!(
            result.is_err(),
            "a SharedObject without PT_DYNAMIC must fail the scan"
        );
    }

    #[test]
    fn scan_fails_on_unterminated_dependency_name() {
        // dynstr with no NUL after the offset: the shared NUL-scan must
        // reject it (BadElf,  length rules).
        let dynstr: &[u8] = b"libc.so.1"; // no terminator
        let bytes = scanned_dso(&[(DT_NEEDED, 0)], dynstr);
        let result = scan_artifact(
            &SliceElfReader::new(&bytes),
            profile(),
            ArtifactRole::SharedObject,
            LoadLimits::DEFAULT,
        );
        assert!(
            result.is_err(),
            "an unterminated DT_NEEDED string must fail"
        );
    }

    #[test]
    fn scan_fails_on_needed_offset_past_dynstr() {
        // DT_NEEDED offset 0xff points past the end of the 10-byte dynstr.
        let dynstr: &[u8] = b"libc.so.1\0";
        let bytes = scanned_dso(&[(DT_NEEDED, 0xff)], dynstr);
        let result = scan_artifact(
            &SliceElfReader::new(&bytes),
            profile(),
            ArtifactRole::SharedObject,
            LoadLimits::DEFAULT,
        );
        assert!(
            result.is_err(),
            "an out-of-range DT_NEEDED offset must fail"
        );
    }

    #[test]
    fn scan_fails_when_needed_has_no_strtab() {
        // A dynamic table with DT_NEEDED but no DT_STRTAB/DT_STRSZ pair: the
        // same BadElf the decode reports for the unpaired tags.
        const EHDR: u64 = 0x40;
        const PHDR: u64 = 0x38;
        let dyn_vaddr = 0x1000 + EHDR + PHDR - EHDR; // after the two phdrs
        let bytes = ElfFixtureBuilder::elf64(EM_RISCV, ET_DYN)
            .with_load_segment(0x1000, 0x100, 0x100, 0x4)
            .with_dynamic_entries(dyn_vaddr, &[(DT_NEEDED as u32, 0)])
            .build();
        let result = scan_artifact(
            &SliceElfReader::new(&bytes),
            profile(),
            ArtifactRole::SharedObject,
            LoadLimits::DEFAULT,
        );
        assert!(result.is_err(), "DT_NEEDED without DT_STRTAB must fail");
    }
}

#[test]
fn fixture_builder_emits_a_parseable_elf32_header() {
    let bytes = ElfFixtureBuilder::elf32(EM_ARM, ET_DYN).build();
    let elf = Elf::parse(&bytes).expect("fixture must contain a valid ELF header");

    assert_eq!(elf.header.e_machine, EM_ARM);
    assert_eq!(elf.header.e_type, ET_DYN);
    assert!(!elf.is_64);
    assert!(elf.little_endian);
}

mod placement {
    use crate::{
        address::{TargetAddress, TargetRange},
        memory::{AllocationRequest, Placement},
    };

    #[test]
    fn anywhere_request_reports_no_fixed_range() {
        let request = AllocationRequest::new(Placement::Anywhere, 0x1000, 0x100);
        assert!(matches!(request.placement(), Placement::Anywhere));
        assert_eq!(request.size(), 0x1000);
        assert_eq!(request.align(), 0x100);
    }

    #[test]
    fn fixed_request_carries_its_range() {
        let range = TargetRange::new(TargetAddress::new(0x5000_0000), 0x2000);
        let request = AllocationRequest::new(Placement::Fixed(range), 0x2000, 0x100);
        match request.placement() {
            Placement::Fixed(actual) => {
                assert_eq!(actual.start(), TargetAddress::new(0x5000_0000));
                assert_eq!(actual.len(), 0x2000);
            }
            other => panic!("expected fixed placement, got {other:?}"),
        }
        assert_eq!(request.size(), 0x2000);
    }
}

mod exec_plan {
    use std::{cell::RefCell, rc::Rc, vec::Vec};

    use crate::{
        identity::{ElfType, LoadLimits, LoadProfile, LoadRequest},
        image::ImageLoader,
        memory::Placement,
        reader::SliceElfReader,
        tests::fixture::{ElfFixtureBuilder, RecordingMemory},
    };

    fn build_exec_request() -> LoadRequest {
        let profile = LoadProfile::riscv64(ElfType::Exec);
        LoadRequest::new(profile, LoadLimits::DEFAULT)
    }

    fn exec_bytes() -> Vec<u8> {
        // Single PT_LOAD r-x segment at 0x5000_0000. p_offset matches p_vaddr
        // mod p_align (4) so inspect's alignment check passes. Entry lives
        // inside the only segment so plan() accepts it.
        ElfFixtureBuilder::elf64(goblin::elf::header::EM_RISCV, goblin::elf::header::ET_EXEC)
            .with_load_segment(0x5000_0000, 0x100, 0x100, 0x4)
            .with_entry(0x5000_0000)
            .build()
    }

    #[test]
    fn exec_image_records_fixed_placement() {
        let bytes = exec_bytes();
        let planned = ImageLoader::new(SliceElfReader::new(&bytes), build_exec_request())
            .admit()
            .expect("admit")
            .inspect()
            .expect("inspect")
            .plan()
            .expect("plan must accept ET_EXEC with fixed placement");

        let sink = Rc::new(RefCell::new(None));
        let recording = RecordingMemory::new(Rc::clone(&sink));
        let _ = planned.allocate(recording).expect("allocate");

        let recorded = RecordingMemory::recorded(&sink).expect("request was recorded");
        match recorded.placement() {
            Placement::Fixed(range) => {
                assert_eq!(range.start().get(), 0x5000_0000);
                assert_eq!(range.len(), 0x100);
            }
            other => panic!("expected fixed placement, got {other:?}"),
        }
        assert_eq!(recorded.size(), 0x100);
    }
}

mod fixed_mapper {
    use crate::{
        address::{TargetAddress, TargetRange},
        memory::{AllocationRequest, ImageMemory, Placement},
        memory_mapper::{MemoryMapper, MemoryPermissions, MemoryRegion},
    };

    // SAFETY: test-only static region. Unit tests only exercise the
    // allocate/validate paths; the span 0x5000_0000..0x5000_2000 is never
    // dereferenced on the host.
    static REGIONS: [MemoryRegion; 1] = [unsafe {
        MemoryRegion::new(
            0x5000_0000,
            0x5000_2000,
            MemoryPermissions::READ
                .bitor(MemoryPermissions::WRITE)
                .bitor(MemoryPermissions::EXECUTE),
        )
    }];

    fn fixed_request(start: u64, len: u64) -> AllocationRequest {
        AllocationRequest::new(
            Placement::Fixed(TargetRange::new(TargetAddress::new(start), len)),
            len,
            4,
        )
    }

    #[test]
    fn fixed_mapper_allocates_borrowed_span() {
        let mut mapper = MemoryMapper::new(Some(&REGIONS));
        let lease = mapper
            .allocate_image(fixed_request(0x5000_0000, 0x1000))
            .expect("allocate");
        let allocation = lease.allocation();
        assert_eq!(allocation.base().get(), 0x5000_0000);
        assert_eq!(allocation.len(), 0x1000);
        assert_eq!(allocation.align(), 4);
        mapper.abort_image(lease, crate::memory::MutationProgress::Reserved);
    }

    #[test]
    fn fixed_mapper_rejects_span_exceeding_regions() {
        let mut mapper = MemoryMapper::new(Some(&REGIONS));
        // The region ends at 0x5000_2000; a span of 0x3000 overruns it.
        assert!(mapper
            .allocate_image(fixed_request(0x5000_0000, 0x3000))
            .is_err());
    }

    #[test]
    fn fixed_mapper_rejects_span_outside_regions() {
        let mut mapper = MemoryMapper::new(Some(&REGIONS));
        assert!(mapper
            .allocate_image(fixed_request(0x6000_0000, 0x1000))
            .is_err());
    }

    #[test]
    fn allocated_mapper_rejects_fixed_request() {
        let mut mapper = MemoryMapper::new(None);
        assert!(mapper
            .allocate_image(fixed_request(0x5000_0000, 0x1000))
            .is_err());
    }

    #[test]
    fn fixed_mapper_rejects_anywhere_request() {
        let mut mapper = MemoryMapper::new(Some(&REGIONS));
        let request = AllocationRequest::new(Placement::Anywhere, 0x1000, 4);
        assert!(mapper.allocate_image(request).is_err());
    }
}

mod entry_dispatch {
    use std::vec::Vec;

    use crate::{load_elf, memory_mapper::MemoryMapper, tests::fixture::ElfFixtureBuilder};

    #[test]
    fn exec_image_on_allocated_mapper_is_rejected() {
        // An ET_EXEC image must only be given to a Fixed mapper; the entry
        // dispatch notices the mismatch before any segment is copied.
        let bytes =
            ElfFixtureBuilder::elf64(goblin::elf::header::EM_RISCV, goblin::elf::header::ET_EXEC)
                .with_load_segment(0x5000_0000, 0x100, 0x100, 0x4)
                .with_entry(0x5000_0000)
                .build();
        let mut mapper = MemoryMapper::new(None);
        let result = load_elf(&bytes, &mut mapper);
        assert!(result.is_err());
    }
}

mod arm_admission {
    use goblin::elf::header::{EM_ARM, ET_DYN};

    use crate::{
        error::{ErrorContext, HeaderField, LoadErrorKind},
        identity::{ElfType, LoadLimits, LoadProfile, LoadRequest},
        image::ImageLoader,
        reader::SliceElfReader,
        tests::fixture::ElfFixtureBuilder,
    };

    // EF_ARM_EABI_VER5 | EF_ARM_ABI_FLOAT_SOFT, as produced for
    // `thumbv7m-none-eabi` soft-float images.
    const SOFT_EABI5: u32 = 0x0500_0200;
    const HARD_EABI5: u32 = 0x0500_0400;
    const EABI4: u32 = 0x0400_0200;

    fn arm_request() -> LoadRequest {
        LoadRequest::new(
            LoadProfile::arm_thumb_soft_float(ElfType::Dyn),
            LoadLimits::DEFAULT,
        )
    }

    fn admit(bytes: &[u8]) -> crate::error::LoadResult<()> {
        ImageLoader::new(SliceElfReader::new(bytes), arm_request())
            .admit()
            .map(|_| ())
    }

    #[test]
    fn soft_float_eabi5_flags_are_accepted() {
        let bytes = ElfFixtureBuilder::elf32(EM_ARM, ET_DYN)
            .with_flags(SOFT_EABI5)
            .build();
        assert!(admit(&bytes).is_ok());
    }

    #[test]
    fn hard_float_flags_are_rejected_by_soft_float_profile() {
        let bytes = ElfFixtureBuilder::elf32(EM_ARM, ET_DYN)
            .with_flags(HARD_EABI5)
            .build();
        let error = match admit(&bytes) {
            Ok(()) => panic!("hard-float e_flags must be rejected"),
            Err(error) => error,
        };
        assert!(matches!(error.kind(), LoadErrorKind::UnsupportedByProfile));
        assert!(matches!(
            error.context(),
            ErrorContext::HeaderField {
                field: HeaderField::Flags,
                ..
            }
        ));
    }

    #[test]
    fn wrong_eabi_version_is_rejected() {
        let bytes = ElfFixtureBuilder::elf32(EM_ARM, ET_DYN)
            .with_flags(EABI4)
            .build();
        assert!(admit(&bytes).is_err());
    }

    #[test]
    fn thumb_entry_requires_bit_zero() {
        // Entry with bit 0 clear (even) is not a valid Thumb entry.
        let bytes = ElfFixtureBuilder::elf32(EM_ARM, ET_DYN)
            .with_flags(SOFT_EABI5)
            .with_load_segment(0x1000, 0x10, 0x10, 0x4)
            .with_entry(0x1000) // even -> not Thumb
            .build();
        let result = ImageLoader::new(SliceElfReader::new(&bytes), arm_request())
            .admit()
            .expect("admit")
            .inspect()
            .expect("inspect")
            .plan();
        let error = match result {
            Ok(_) => panic!("even ARM entry must be rejected"),
            Err(error) => error,
        };
        assert!(matches!(error.kind(), LoadErrorKind::BadElf));
        assert!(matches!(
            error.context(),
            ErrorContext::HeaderField {
                field: HeaderField::Entry,
                ..
            }
        ));
    }

    #[test]
    fn thumb_entry_min_instruction_span_must_fall_in_x_segment() {
        // A single-byte segment cannot hold a whole 2-byte Thumb instruction;
        // the canonical entry span must lie fully inside an X segment.
        let bytes = ElfFixtureBuilder::elf32(EM_ARM, ET_DYN)
            .with_flags(SOFT_EABI5)
            .with_load_segment(0x1000, 0x1, 0x1, 0x1)
            .with_entry(0x1001) // bit 0 set; canonical 0x1000, span 2 > segment len 1
            .build();
        let result = ImageLoader::new(SliceElfReader::new(&bytes), arm_request())
            .admit()
            .expect("admit")
            .inspect()
            .expect("inspect")
            .plan();
        let error = match result {
            Ok(_) => panic!("entry min-instruction span must be rejected"),
            Err(error) => error,
        };
        assert!(matches!(error.kind(), LoadErrorKind::PermissionConflict));
    }

    #[test]
    fn thumb_entry_with_valid_span_is_accepted() {
        let bytes = ElfFixtureBuilder::elf32(EM_ARM, ET_DYN)
            .with_flags(SOFT_EABI5)
            .with_load_segment(0x1000, 0x10, 0x10, 0x4)
            .with_entry(0x1001) // canonical 0x1000, within the 0x10-byte segment
            .build();
        ImageLoader::new(SliceElfReader::new(&bytes), arm_request())
            .admit()
            .expect("admit")
            .inspect()
            .expect("inspect")
            .plan()
            .expect("valid Thumb entry must be planned");
    }
}
