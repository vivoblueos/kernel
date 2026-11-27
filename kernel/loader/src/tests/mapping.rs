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

//! Backend-mediated mapping, ownership, malformed results and partial failure.

use super::fixture::{ElfFixtureBuilder, ProgramHeaderFixture, SliceElfReader};
use crate::{
    error::{ErrorContext, LoadErrorKind, LoadStage},
    image::{ImageLoader, LoadRequest, PlannedImage},
    memory::{
        AllocationOffset, ImageLayout, MemoryMapper, MemoryPermissions, MemoryRegion, Placement,
        SegmentLayout, TargetAddress, TargetRange,
    },
    profile::{ElfClass, LoadLimits, LoadProfile},
    ElfReader, ImageAllocator, ImageMapping, LoadError, LoadResult,
};
use alloc::{boxed::Box, rc::Rc, vec, vec::Vec};
use blueos_test_macro::test;
use core::{cell::RefCell, ops::Range};
use goblin::elf::{
    header::{EM_AARCH64, EM_RISCV, ET_DYN, ET_EXEC},
    program_header::{PF_R, PF_W, PT_NOTE},
};

const PROFILES: [LoadProfile; 3] = [
    LoadProfile::riscv32(),
    LoadProfile::riscv64(),
    LoadProfile::aarch64(),
];
const PAYLOAD: usize = 0x200;

fn fixture(
    profile: LoadProfile,
    kind: u16,
    vaddr: u64,
    file_len: usize,
    memory_len: u64,
) -> Vec<u8> {
    let builder = match profile.class() {
        ElfClass::Elf32 => ElfFixtureBuilder::elf32(EM_RISCV, kind),
        ElfClass::Elf64 => ElfFixtureBuilder::elf64(
            if profile == LoadProfile::aarch64() {
                EM_AARCH64
            } else {
                EM_RISCV
            },
            kind,
        ),
    };
    let mut bytes = builder
        .with_entry(vaddr + 4)
        .with_program_header(ProgramHeaderFixture {
            vaddr: TargetAddress::new(vaddr),
            offset: PAYLOAD as u64,
            filesz: file_len as u64,
            memsz: memory_len,
            align: 16,
            ..ProgramHeaderFixture::load()
        })
        .build();
    bytes.resize(PAYLOAD + file_len, 0);
    for (index, byte) in bytes[PAYLOAD..].iter_mut().enumerate() {
        *byte = (index % 251) as u8;
    }
    bytes
}

fn planned(bytes: &[u8], profile: LoadProfile) -> PlannedImage<SliceElfReader<'_>> {
    ImageLoader::new(
        SliceElfReader::new(bytes),
        LoadRequest::new(profile, LoadLimits::DEFAULT),
    )
    .admit()
    .unwrap()
    .inspect()
    .unwrap()
    .plan()
    .unwrap()
}

fn failure<T>(result: LoadResult<T>) -> LoadError {
    match result {
        Err(error) => error,
        Ok(_) => panic!("expected failure"),
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Fault {
    None,
    Prepare,
    Write(usize),
    Zero,
    Short,
    WrongAlignment,
    Unaligned,
    FixedBase,
}

#[derive(Default)]
struct State {
    layout: Option<ImageLayout>,
    // Kept by the observer after Drop to inspect partial writes on failure.
    bytes: Vec<u8>,
    prepares: usize,
    writes: usize,
    zeros: usize,
    live: usize,
    drops: usize,
    factory_drops: usize,
}

struct MockMemory {
    state: Rc<RefCell<State>>,
    base: u64,
    fault: Fault,
}

impl MockMemory {
    fn new(base: u64) -> Self {
        Self {
            state: Rc::new(RefCell::new(State::default())),
            base,
            fault: Fault::None,
        }
    }
}

impl Drop for MockMemory {
    fn drop(&mut self) {
        self.state.borrow_mut().factory_drops += 1;
    }
}

#[must_use = "the mock allocation owns its image lifetime"]
struct MockAllocation {
    state: Rc<RefCell<State>>,
    base: TargetAddress,
    len: u64,
    align: u64,
    fault: Fault,
}

impl Drop for MockAllocation {
    fn drop(&mut self) {
        let mut state = self.state.borrow_mut();
        assert_eq!(state.live, 1);
        state.live = 0;
        state.drops += 1;
    }
}

impl MockAllocation {
    fn range(&self, state: &State, offset: AllocationOffset, len: u64) -> LoadResult<Range<usize>> {
        let end = offset
            .value()
            .checked_add(len)
            .filter(|end| *end <= self.len && *end <= state.bytes.len() as u64)
            .ok_or_else(|| LoadError::new(LoadErrorKind::OutOfBounds, ErrorContext::None))?;
        Ok(offset.value() as usize..end as usize)
    }
}

impl ImageAllocator for MockMemory {
    type Allocation = MockAllocation;

    fn prepare_image(&mut self, layout: &ImageLayout) -> LoadResult<Self::Allocation> {
        let mut state = self.state.borrow_mut();
        state.prepares += 1;
        state.layout = Some(layout.clone());
        if self.fault == Fault::Prepare {
            return Err(LoadError::new(
                LoadErrorKind::OutOfMemory,
                ErrorContext::None,
            ));
        }
        assert_eq!(state.live, 0);
        let mut base = match layout.placement() {
            Placement::Anywhere => self.base,
            Placement::Fixed(range) => range.start().get(),
        };
        let mut len = layout.size();
        let mut align = layout.align();
        match self.fault {
            Fault::Short => len -= 1,
            Fault::WrongAlignment => align *= 2,
            Fault::Unaligned => base += 1,
            Fault::FixedBase => base += align,
            _ => {}
        }
        state.bytes = vec![0xa5; layout.size() as usize];
        state.live = 1;
        Ok(MockAllocation {
            state: self.state.clone(),
            base: TargetAddress::new(base),
            len,
            align,
            fault: self.fault,
        })
    }
}

impl ImageMapping for MockAllocation {
    fn base(&self) -> TargetAddress {
        self.base
    }
    fn len(&self) -> u64 {
        self.len
    }
    fn align(&self) -> u64 {
        self.align
    }

    fn write(&mut self, offset: AllocationOffset, data: &[u8]) -> LoadResult<()> {
        let mut state = self.state.borrow_mut();
        let range = self.range(&state, offset, data.len() as u64)?;
        state.writes += 1;
        if self.fault == Fault::Write(state.writes) {
            // Simulate a backend that partially mutates before reporting failure.
            state.bytes[range.start] = data[0];
            return Err(LoadError::new(LoadErrorKind::Backend, ErrorContext::None));
        }
        state.bytes[range].copy_from_slice(data);
        Ok(())
    }

    fn zero(&mut self, offset: AllocationOffset, len: u64) -> LoadResult<()> {
        let mut state = self.state.borrow_mut();
        let range = self.range(&state, offset, len)?;
        state.zeros += 1;
        if self.fault == Fault::Zero {
            state.bytes[range.start] = 0;
            return Err(LoadError::new(LoadErrorKind::Backend, ErrorContext::None));
        }
        state.bytes[range].fill(0);
        Ok(())
    }

    fn read(&self, offset: AllocationOffset, dst: &mut [u8]) -> LoadResult<()> {
        let state = self.state.borrow();
        let range = self.range(&state, offset, dst.len() as u64)?;
        dst.copy_from_slice(&state.bytes[range]);
        Ok(())
    }
}

#[derive(Default)]
struct ReadState {
    payload: Vec<(u64, usize)>,
    drops: usize,
    fail_on: Option<usize>,
}

#[must_use = "the reader tracks input lifetime and payload reads"]
struct ObservedReader<'a> {
    bytes: &'a [u8],
    state: Rc<RefCell<ReadState>>,
}

impl ElfReader for ObservedReader<'_> {
    fn len(&self) -> LoadResult<u64> {
        Ok(self.bytes.len() as u64)
    }
    fn read_exact_at(&self, offset: u64, dst: &mut [u8]) -> LoadResult<()> {
        if offset >= PAYLOAD as u64 {
            let mut state = self.state.borrow_mut();
            state.payload.push((offset, dst.len()));
            if state.fail_on == Some(state.payload.len()) {
                dst.fill(0xff);
                return Err(LoadError::new(
                    LoadErrorKind::Io,
                    ErrorContext::FileRange {
                        offset,
                        len: dst.len() as u64,
                        file_len: self.bytes.len() as u64,
                    },
                ));
            }
        }
        SliceElfReader::new(self.bytes).read_exact_at(offset, dst)
    }
}
impl Drop for ObservedReader<'_> {
    fn drop(&mut self) {
        self.state.borrow_mut().drops += 1;
    }
}

#[test]
fn mapping_copies_bounded_chunks_and_zeros_only_bss() {
    for profile in PROFILES {
        let bytes = fixture(profile, ET_DYN, 0x1000, 1200, 1221);
        let reads = Rc::new(RefCell::new(ReadState::default()));
        let reader = ObservedReader {
            bytes: &bytes,
            state: reads.clone(),
        };
        let memory = MockMemory::new(0x8000);
        let state = memory.state.clone();
        let allocated = ImageLoader::new(reader, LoadRequest::new(profile, LoadLimits::DEFAULT))
            .admit()
            .unwrap()
            .inspect()
            .unwrap()
            .plan()
            .unwrap()
            .allocate(memory)
            .unwrap();
        assert!(reads.borrow().payload.is_empty());
        assert_eq!(reads.borrow().drops, 0);
        assert_eq!(state.borrow().factory_drops, 1);
        assert_eq!(state.borrow().live, 1);
        let mapped = allocated.map().unwrap();
        assert_eq!(mapped.entry().get(), 0x8004);
        assert_eq!(mapped.load_bias(), 0x7000);
        assert_eq!(
            reads.borrow().payload,
            [(0x200, 512), (0x400, 512), (0x600, 176)]
        );
        assert_eq!(reads.borrow().drops, 1);
        let mut contents = vec![0; 1232];
        mapped
            .read(AllocationOffset::new(0), &mut contents)
            .unwrap();
        assert_eq!(&contents[..1200], &bytes[PAYLOAD..]);
        assert!(contents[1200..1221].iter().all(|byte| *byte == 0));
        assert!(contents[1221..].iter().all(|byte| *byte == 0xa5));
        assert_eq!(state.borrow().drops, 0);
        drop(mapped);
        assert_eq!(state.borrow().drops, 1);
        assert_eq!(state.borrow().live, 0);
    }
}

#[test]
fn allocation_passes_complete_sorted_layout_and_normalized_alignment() {
    for profile in PROFILES {
        let mut builder = match profile.class() {
            ElfClass::Elf32 => ElfFixtureBuilder::elf32(EM_RISCV, ET_DYN),
            ElfClass::Elf64 => ElfFixtureBuilder::elf64(
                if profile == LoadProfile::aarch64() {
                    EM_AARCH64
                } else {
                    EM_RISCV
                },
                ET_DYN,
            ),
        }
        .with_entry(0x1000);
        for header in [
            ProgramHeaderFixture {
                vaddr: TargetAddress::new(0x3000),
                flags: PF_R | PF_W,
                align: 0,
                ..ProgramHeaderFixture::load()
            },
            ProgramHeaderFixture {
                kind: PT_NOTE,
                ..ProgramHeaderFixture::load()
            },
            ProgramHeaderFixture {
                filesz: 0,
                memsz: 0,
                align: 0x8000_0000,
                ..ProgramHeaderFixture::load()
            },
            ProgramHeaderFixture {
                align: 0,
                ..ProgramHeaderFixture::load()
            },
        ] {
            builder = builder.with_program_header(header);
        }
        let bytes = builder.build();
        let memory = MockMemory::new(0x8000);
        let state = memory.state.clone();
        let allocated = planned(&bytes, profile).allocate(memory).unwrap();
        {
            let state = state.borrow();
            let layout = state.layout.as_ref().unwrap();
            assert_eq!(state.prepares, 1);
            assert_eq!(state.writes, 0);
            assert_eq!(layout.placement(), Placement::Anywhere);
            assert_eq!(layout.align(), 1);
            assert_eq!(layout.size(), 0x2100);
            assert_eq!(layout.segments().len(), 2);
            assert_eq!(layout.segments()[0].allocation_offset().value(), 0);
            assert_eq!(layout.segments()[1].allocation_offset().value(), 0x2000);
            assert_eq!(layout.segments()[1].memory_size(), 0x100);
            assert_eq!(
                layout.segments()[1].permissions(),
                MemoryPermissions::READ.bitor(MemoryPermissions::WRITE)
            );
        }
        drop(allocated);
        assert_eq!(state.borrow().drops, 1);
    }
}

#[test]
fn mapping_keeps_gaps_untouched() {
    let profile = LoadProfile::riscv32();
    let bytes = ElfFixtureBuilder::elf32(EM_RISCV, ET_DYN)
        .with_entry(0x1000)
        .with_program_header(ProgramHeaderFixture::load())
        .with_program_header(ProgramHeaderFixture {
            vaddr: TargetAddress::new(0x2000),
            flags: PF_R | PF_W,
            ..ProgramHeaderFixture::load()
        })
        .build();
    let memory = MockMemory::new(0x8000);
    let mapped = planned(&bytes, profile)
        .allocate(memory)
        .unwrap()
        .map()
        .unwrap();
    let mut gap = [0; 16];
    mapped.read(AllocationOffset::new(0x100), &mut gap).unwrap();
    assert_eq!(gap, [0xa5; 16]);
    mapped
        .read(AllocationOffset::new(0x1000), &mut gap[..4])
        .unwrap();
    assert_eq!(&gap[..4], b"\x7fELF");
}

#[test]
fn mapping_bss_only_segments_does_not_read_payload() {
    for profile in PROFILES {
        let bytes = fixture(profile, ET_DYN, 0x1000, 0, 32);
        let reads = Rc::new(RefCell::new(ReadState::default()));
        let reader = ObservedReader {
            bytes: &bytes,
            state: reads.clone(),
        };
        let memory = MockMemory::new(0x8000);
        let mapped = ImageLoader::new(reader, LoadRequest::new(profile, LoadLimits::DEFAULT))
            .admit()
            .unwrap()
            .inspect()
            .unwrap()
            .plan()
            .unwrap()
            .allocate(memory)
            .unwrap()
            .map()
            .unwrap();
        assert!(reads.borrow().payload.is_empty());
        let mut contents = [0xff; 32];
        mapped
            .read(AllocationOffset::new(0), &mut contents)
            .unwrap();
        assert_eq!(contents, [0; 32]);
    }
}

#[test]
fn mapping_supports_fixed_placement_and_downward_relocation() {
    for profile in PROFILES {
        for kind in [ET_DYN, ET_EXEC] {
            let bytes = fixture(profile, kind, 0x1000, 17, 48);
            let memory = MockMemory::new(0x100);
            let state = memory.state.clone();
            let mapped = planned(&bytes, profile)
                .allocate(memory)
                .unwrap()
                .map()
                .unwrap();
            let fixed = kind == ET_EXEC;
            assert_eq!(mapped.entry().get(), if fixed { 0x1004 } else { 0x104 });
            assert_eq!(mapped.load_bias(), if fixed { 0 } else { -0xf00 });
            assert_eq!(
                state.borrow().layout.as_ref().unwrap().placement(),
                if fixed {
                    Placement::Fixed(TargetRange::new(TargetAddress::new(0x1000), 48))
                } else {
                    Placement::Anywhere
                }
            );
        }
    }
}

#[test]
fn allocation_rejects_malformed_backend_handles_before_io() {
    for profile in PROFILES {
        for fault in [
            Fault::Short,
            Fault::WrongAlignment,
            Fault::Unaligned,
            Fault::FixedBase,
        ] {
            let kind = if fault == Fault::FixedBase {
                ET_EXEC
            } else {
                ET_DYN
            };
            let bytes = fixture(profile, kind, 0x1000, 17, 48);
            let mut memory = MockMemory::new(0x8000);
            memory.fault = fault;
            let state = memory.state.clone();
            let error = failure(planned(&bytes, profile).allocate(memory));
            assert_eq!(error.stage(), Some(LoadStage::Allocate));
            assert_eq!(error.kind(), LoadErrorKind::Backend);
            assert!(matches!(error.context(), ErrorContext::Allocation { .. }));
            assert_eq!(state.borrow().drops, 1);
            assert_eq!(state.borrow().writes, 0);
        }
    }
}

#[test]
fn allocation_checks_target_width_without_host_pointer_restrictions() {
    for profile in PROFILES {
        let bytes = fixture(profile, ET_DYN, 0x1000, 17, 48);
        for base in [0x1_0000_0000, u64::MAX - 15] {
            let memory = MockMemory::new(base);
            let state = memory.state.clone();
            let result = planned(&bytes, profile).allocate(memory);
            if base == 0x1_0000_0000 && profile.class() == ElfClass::Elf64 {
                let mapped = result.unwrap().map().unwrap();
                assert_eq!(mapped.entry().get(), base + 4);
            } else {
                let error = failure(result);
                assert_eq!(error.stage(), Some(LoadStage::Allocate));
                assert_eq!(error.kind(), LoadErrorKind::Backend);
                assert_eq!(state.borrow().drops, 1);
            }
        }
    }
}

#[test]
fn allocation_prepare_failure_releases_input_without_an_allocation_handle() {
    let profile = LoadProfile::riscv32();
    let bytes = fixture(profile, ET_DYN, 0x1000, 17, 48);
    let reads = Rc::new(RefCell::new(ReadState::default()));
    let reader = ObservedReader {
        bytes: &bytes,
        state: reads.clone(),
    };
    let mut memory = MockMemory::new(0x8000);
    memory.fault = Fault::Prepare;
    let state = memory.state.clone();
    let error = failure(
        ImageLoader::new(reader, LoadRequest::new(profile, LoadLimits::DEFAULT))
            .admit()
            .unwrap()
            .inspect()
            .unwrap()
            .plan()
            .unwrap()
            .allocate(memory),
    );
    assert_eq!(error.kind(), LoadErrorKind::OutOfMemory);
    assert_eq!(error.stage(), Some(LoadStage::Allocate));
    assert_eq!(state.borrow().drops, 0);
    assert_eq!(state.borrow().live, 0);
    assert_eq!(reads.borrow().drops, 1);
}

#[test]
fn mapping_reader_failures_keep_context_and_discard_partial_scratch() {
    for fail_on in [1, 2] {
        let profile = LoadProfile::riscv32();
        let bytes = fixture(profile, ET_DYN, 0x1000, 1200, 1221);
        let reads = Rc::new(RefCell::new(ReadState {
            fail_on: Some(fail_on),
            ..ReadState::default()
        }));
        let reader = ObservedReader {
            bytes: &bytes,
            state: reads.clone(),
        };
        let memory = MockMemory::new(0x8000);
        let state = memory.state.clone();
        let error = failure(
            ImageLoader::new(reader, LoadRequest::new(profile, LoadLimits::DEFAULT))
                .admit()
                .unwrap()
                .inspect()
                .unwrap()
                .plan()
                .unwrap()
                .allocate(memory)
                .unwrap()
                .map(),
        );
        assert_eq!(error.stage(), Some(LoadStage::Map));
        assert_eq!(error.kind(), LoadErrorKind::Io);
        assert!(
            matches!(error.context(), ErrorContext::FileRange { offset, len: 512, .. } if *offset == (PAYLOAD + 512 * (fail_on - 1)) as u64)
        );
        assert_eq!(state.borrow().writes, fail_on - 1);
        assert_eq!(state.borrow().drops, 1);
        assert!(state.borrow().bytes[512 * (fail_on - 1)..]
            .iter()
            .all(|byte| *byte == 0xa5));
        assert_eq!(reads.borrow().drops, 1);
    }
}

#[test]
fn mapping_partial_backend_failures_drop_allocation_once() {
    for fault in [Fault::Write(1), Fault::Write(2), Fault::Zero] {
        let profile = LoadProfile::riscv32();
        let bytes = fixture(profile, ET_DYN, 0x1000, 1200, 1221);
        let mut memory = MockMemory::new(0x8000);
        memory.fault = fault;
        let state = memory.state.clone();
        let error = failure(planned(&bytes, profile).allocate(memory).unwrap().map());
        assert_eq!(error.stage(), Some(LoadStage::Map));
        assert_eq!(error.kind(), LoadErrorKind::Backend);
        assert_eq!(state.borrow().drops, 1);
        assert_eq!(state.borrow().live, 0);
    }
}

#[test]
fn dropping_allocated_and_mapped_images_releases_each_allocation_once() {
    let profile = LoadProfile::riscv32();
    let bytes = fixture(profile, ET_DYN, 0x1000, 17, 48);
    let mut memory = MockMemory::new(0x8000);
    let state = memory.state.clone();
    let allocated = planned(&bytes, profile).allocate(&mut memory).unwrap();
    assert_eq!(state.borrow().drops, 0);
    drop(allocated);
    assert_eq!(state.borrow().drops, 1);
    let mapped = planned(&bytes, profile)
        .allocate(&mut memory)
        .unwrap()
        .map()
        .unwrap();
    drop(mapped);
    assert_eq!(state.borrow().drops, 2);
}

fn fixed_test_layout(base: u64, len: u64) -> ImageLayout {
    ImageLayout::new(
        Placement::Fixed(TargetRange::new(TargetAddress::new(base), len)),
        len,
        16,
        vec![SegmentLayout::new(
            AllocationOffset::new(0),
            len,
            MemoryPermissions::READ,
        )],
    )
    .unwrap()
}

#[test]
fn mapping_runs_with_flat_owned_and_fixed_backends() {
    let profile = if usize::BITS == 32 {
        LoadProfile::riscv32()
    } else {
        LoadProfile::riscv64()
    };
    let bytes = fixture(profile, ET_DYN, 0x1000, 17, 48);
    let mut memory = MemoryMapper::new(None);
    let mapped = planned(&bytes, profile)
        .allocate(&mut memory)
        .unwrap()
        .map()
        .unwrap();
    let mut contents = [0xff; 48];
    mapped
        .read(AllocationOffset::new(0), &mut contents)
        .unwrap();
    assert_eq!(&contents[..17], &bytes[PAYLOAD..]);
    assert_eq!(&contents[17..], &[0; 31]);
    let base = mapped.allocation().base();
    assert_eq!(mapped.entry(), base.checked_add(4).unwrap());
    drop(mapped);

    let storage = Box::leak(Box::new(
        blueos_infra::storage::Storage::try_from_layout(
            core::alloc::Layout::from_size_align(128, 16).unwrap(),
        )
        .unwrap(),
    ));
    let base = storage.base() as usize;
    // SAFETY: static storage owns this writable range. Tests access its bytes
    // through the mapper while the allocation is live, and never execute it.
    let region = unsafe {
        MemoryRegion::new(
            base,
            base + 128,
            MemoryPermissions::READ.bitor(MemoryPermissions::WRITE),
        )
    };
    let regions = Box::leak(Box::new([region]));
    let mut memory = MemoryMapper::new(Some(regions));
    let bytes = fixture(profile, ET_EXEC, base as u64, 17, 48);
    let allocated = planned(&bytes, profile).allocate(&mut memory).unwrap();
    drop(allocated);
    let mapped = planned(&bytes, profile)
        .allocate(&mut memory)
        .unwrap()
        .map()
        .unwrap();
    assert_eq!(mapped.entry().get(), base as u64 + 4);
    assert_eq!(mapped.load_bias(), 0);
    mapped
        .read(AllocationOffset::new(0), &mut contents)
        .unwrap();
    assert_eq!(&contents[..17], &bytes[PAYLOAD..]);
    assert_eq!(&contents[17..], &[0; 31]);
    drop(mapped);
    let next = memory
        .prepare_image(&fixed_test_layout(base as u64, 48))
        .unwrap();
    next.read(AllocationOffset::new(0), &mut contents).unwrap();
    assert_eq!(contents, [0; 48]);
}

#[test]
fn mapping_checks_runtime_entry_alignment_before_payload_access() {
    for profile in PROFILES {
        let bytes = match profile.class() {
            ElfClass::Elf32 => ElfFixtureBuilder::elf32(EM_RISCV, ET_DYN),
            ElfClass::Elf64 => ElfFixtureBuilder::elf64(
                if profile == LoadProfile::aarch64() {
                    EM_AARCH64
                } else {
                    EM_RISCV
                },
                ET_DYN,
            ),
        }
        .with_entry(0x1000)
        .with_program_header(ProgramHeaderFixture {
            align: 1,
            ..ProgramHeaderFixture::load()
        })
        .build();
        let memory = MockMemory::new(0x8001);
        let state = memory.state.clone();
        let error = failure(planned(&bytes, profile).allocate(memory).unwrap().map());
        assert_eq!(error.stage(), Some(LoadStage::Map));
        assert_eq!(error.kind(), LoadErrorKind::InvalidAlignment);
        assert_eq!(state.borrow().writes, 0);
        assert_eq!(state.borrow().drops, 1);
    }
}

#[test]
fn mapping_fixed_input_failure_releases_region_for_a_fresh_load() {
    let profile = if usize::BITS == 32 {
        LoadProfile::riscv32()
    } else {
        LoadProfile::riscv64()
    };
    for fail_on in [1, 2] {
        let storage = Box::leak(Box::new(
            blueos_infra::storage::Storage::try_from_layout(
                core::alloc::Layout::from_size_align(1536, 16).unwrap(),
            )
            .unwrap(),
        ));
        let base = storage.base() as usize;
        // SAFETY: static backing owns this writable region. The test neither
        // executes it nor accesses it through aliases while a handle is live.
        let region = unsafe {
            MemoryRegion::new(
                base,
                base + 1536,
                MemoryPermissions::READ.bitor(MemoryPermissions::WRITE),
            )
        };
        let regions = Box::leak(Box::new([region]));
        let mut memory = MemoryMapper::new(Some(regions));
        let bytes = fixture(profile, ET_EXEC, base as u64, 1200, 1221);
        let reads = Rc::new(RefCell::new(ReadState {
            fail_on: Some(fail_on),
            ..ReadState::default()
        }));
        let reader = ObservedReader {
            bytes: &bytes,
            state: reads.clone(),
        };
        let error = failure(
            ImageLoader::new(reader, LoadRequest::new(profile, LoadLimits::DEFAULT))
                .admit()
                .unwrap()
                .inspect()
                .unwrap()
                .plan()
                .unwrap()
                .allocate(&mut memory)
                .unwrap()
                .map(),
        );
        assert_eq!(error.kind(), LoadErrorKind::Io);
        assert_eq!(error.stage(), Some(LoadStage::Map));
        assert_eq!(reads.borrow().drops, 1);
        // Preparation resets partial bytes from either failure point.
        let allocation = memory
            .prepare_image(&fixed_test_layout(base as u64, 1232))
            .unwrap();
        let mut contents = [0xff; 1232];
        allocation
            .read(AllocationOffset::new(0), &mut contents)
            .unwrap();
        assert_eq!(contents, [0; 1232]);
        drop(allocation);
        let mapped = planned(&bytes, profile)
            .allocate(&mut memory)
            .unwrap()
            .map()
            .unwrap();
        mapped
            .read(AllocationOffset::new(0), &mut contents)
            .unwrap();
        assert_eq!(&contents[..1200], &bytes[PAYLOAD..]);
        assert_eq!(&contents[1200..1221], &[0; 21]);
    }
}
