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

//! Read-only dependency scan (namespace-replacement plan ).
//!
//! [`scan_artifact`] answers one question — what does this ELF declare as its
//! `DT_SONAME` and its `DT_NEEDED` entries — without allocating target memory,
//! copying segments, relocating, sealing or publishing anything. It reuses the
//! same parsing code as the full pipeline: the admit/inspect stages for the
//! header, program headers and the dynamic feature summary, and the shared
//! [`decode_dependency_name_at`] for resolving dynstr offsets. There is no
//! second ELF parser to drift out of agreement with the real loader.
//!
//! The scan output feeds the BFS launch planner and the runtime system
//! batch acquire: knowing the whole system closure up front lets one
//! session acquire every system permit atomically instead of taking them
//! one-by-one and risking an ABBA deadlock with a concurrent session.

use alloc::vec::Vec;

use goblin::elf::dynamic::{DT_NEEDED, DT_SONAME, DT_STRSZ, DT_STRTAB};

use crate::{
    address::{FileRange, TargetAddress, TargetRange},
    dynamic_linker::{ArtifactRole, DependencyName},
    elf::LoadSegmentInfo,
    error::{LoadError, LoadErrorKind, LoadResult, LoadStage},
    identity::{LoadLimits, LoadProfile, LoadRequest, DYNAMIC_LINK_LOAD_POLICY},
    image::{image_loader::ImageLoader, map::decode_dependency_name_at},
    reader::ElfReader,
};

/// What one artifact's dynamic table declares.
///
/// `declared_soname` is `None` for a DSO without `DT_SONAME` — legal since the
/// SONAME relaxation — and for a root without a dynamic table (a static PIE).
#[derive(Clone, Debug, Default)]
pub struct ScannedArtifact {
    /// The declared `DT_SONAME`, when present.
    pub declared_soname: Option<DependencyName>,
    /// Every `DT_NEEDED`, in encounter order.
    pub needed: Vec<DependencyName>,
}

/// Scan one artifact's metadata without any target allocation.
///
/// The scan runs the same admit/inspect validation as a full load, so a file
/// that fails here would also fail during the real pipeline: header and
/// program-header structure, load policy, `PT_DYNAMIC` presence for a shared
/// object, and dynamic-tag checks. Only the *resolved* names are produced; no
/// symbol tables, relocation tables or lifecycle arrays are decoded.
///
/// A root without `PT_DYNAMIC` scans to an empty result; a shared object
/// without `PT_DYNAMIC` fails, exactly as during a real load.
pub fn scan_artifact<R: ElfReader>(
    reader: &R,
    profile: LoadProfile,
    role: ArtifactRole,
    limits: LoadLimits,
) -> LoadResult<ScannedArtifact> {
    let request = LoadRequest::new(profile, limits);
    // Admit and inspect read only through `reader`: the header, the program
    // header table and the file-backed PT_DYNAMIC all go through
    // read_exact_at, never through a memory transaction.
    let inspected = ImageLoader::new(ReadRef::new(reader), request)
        .admit()
        .map_err(|error| error.at_stage(LoadStage::Discover))?
        .inspect_with_policy(DYNAMIC_LINK_LOAD_POLICY)
        .with_role(role)
        .inspect()
        .map_err(|error| error.at_stage(LoadStage::Discover))?;

    let (dynamic, summary, load_segments) = inspected.scan_parts();
    let Some(dynamic) = dynamic else {
        // A root without a dynamic table: no SONAME, no NEEDED.
        return Ok(ScannedArtifact::default());
    };

    // Resolve the raw offsets against the file-backed `.dynstr` using the
    // summary's DT_STRTAB/DT_STRSZ — the same pairing rules the decode
    // stage enforces on the mapped copy.
    let needed_offsets = summary.needed();
    let soname_offset = summary.soname();
    if needed_offsets.is_empty() && soname_offset.is_none() {
        return Ok(ScannedArtifact::default());
    }
    let (strtab, strsz) = match (summary.strtab(), summary.strsz()) {
        (Some(strtab), Some(strsz)) => (strtab, strsz),
        _ => {
            // A dynamic table that declares dependencies but no string table
            // cannot resolve them: the same BadElf the decode reports.
            return Err(LoadError::new(
                LoadErrorKind::BadElf,
                crate::error::ErrorContext::DynamicTag {
                    tag: DT_STRTAB,
                    value: 0,
                },
            )
            .at_stage(LoadStage::Discover));
        }
    };
    limits.check_string_table_bytes(strsz)?;
    let dynstr = read_dynstr_from_file(reader, load_segments, strtab, strsz)?;

    let max_len = limits.max_dependency_name_len();
    let mut needed = Vec::new();
    needed
        .try_reserve_exact(needed_offsets.len())
        .map_err(|_| {
            LoadError::new(LoadErrorKind::OutOfMemory, crate::error::ErrorContext::None)
        })?;
    for &offset in needed_offsets {
        needed.push(
            decode_dependency_name_at(offset, &dynstr, DT_NEEDED, max_len)
                .map_err(|error| error.at_stage(LoadStage::Discover))?,
        );
    }
    let declared_soname = match soname_offset {
        Some(offset) => Some(
            decode_dependency_name_at(offset, &dynstr, DT_SONAME, max_len)
                .map_err(|error| error.at_stage(LoadStage::Discover))?,
        ),
        None => None,
    };
    Ok(ScannedArtifact {
        declared_soname,
        needed,
    })
}

/// Read the `.dynstr` byte range from the *file* side of a `PT_LOAD` segment.
///
/// The mapped pipeline locates `strtab` in the already-copied segment memory
///; the scanner locates the same vaddr in the load segment's file range
/// instead — the identical mapping the `PT_DYNAMIC` itself uses
/// (`locate_file_backed_dynamic`): `file_offset = segment.file_offset +
/// (vaddr - segment.vaddr)`. A vaddr outside every segment's *file-backed*
/// range is the same OutOfBounds the real load would raise.
fn read_dynstr_from_file<R: ElfReader>(
    reader: &R,
    load_segments: &[LoadSegmentInfo],
    strtab: u64,
    strsz: u64,
) -> LoadResult<Vec<u8>> {
    if strsz == 0 {
        return Err(LoadError::new(
            LoadErrorKind::BadElf,
            crate::error::ErrorContext::DynamicTag {
                tag: DT_STRSZ,
                value: strsz,
            },
        )
        .at_stage(LoadStage::Discover));
    }
    let start = TargetAddress::new(strtab);
    let span = TargetRange::new(start, strsz);
    let segment = load_segments
        .iter()
        .find(|segment| {
            TargetRange::new(segment.vaddr(), segment.memory_size())
                .contains_span(span.start(), span.len())
        })
        .ok_or_else(|| {
            LoadError::new(
                LoadErrorKind::OutOfBounds,
                crate::error::ErrorContext::TargetRange {
                    start: span.start(),
                    len: span.len(),
                    align: 0,
                },
            )
            .at_stage(LoadStage::Discover)
        })?;
    let offset = span
        .start()
        .checked_sub(segment.vaddr())
        .map_err(|error| error.at_stage(LoadStage::Discover))
        .and_then(|delta| {
            segment
                .file_range()
                .offset()
                .checked_add(delta)
                .ok_or_else(|| {
                    LoadError::new(
                        LoadErrorKind::IntegerOverflow,
                        crate::error::ErrorContext::DynamicTag {
                            tag: DT_STRTAB,
                            value: strtab,
                        },
                    )
                    .at_stage(LoadStage::Discover)
                })
        })?;
    let file_range = FileRange::new(offset, strsz);
    // The straddling case — vaddr inside the segment but the string table
    // reaching past its file-backed extent into BSS — is malformed, exactly
    // as the mapped pipeline's `locate_file_backed_dynamic` treats it.
    if file_range.offset() + file_range.len()
        > segment.file_range().offset() + segment.file_range().len()
    {
        return Err(LoadError::new(
            LoadErrorKind::OutOfBounds,
            crate::error::ErrorContext::FileRange {
                offset: file_range.offset(),
                len: file_range.len(),
                file_len: u64::MAX,
            },
        )
        .at_stage(LoadStage::Discover));
    }
    let len = usize::try_from(strsz).map_err(|_| {
        LoadError::new(
            LoadErrorKind::IntegerOverflow,
            crate::error::ErrorContext::DynamicTag {
                tag: DT_STRSZ,
                value: strsz,
            },
        )
        .at_stage(LoadStage::Discover)
    })?;
    let mut buffer = Vec::new();
    buffer.try_reserve_exact(len).map_err(|_| {
        LoadError::new(LoadErrorKind::OutOfMemory, crate::error::ErrorContext::None)
    })?;
    buffer.resize(len, 0);
    reader
        .read_exact_at(offset, &mut buffer)
        .map_err(|error| error.at_stage(LoadStage::Discover))?;
    Ok(buffer)
}

/// A borrowing `ElfReader` adapter so `ImageLoader` can drive a scan over a
/// caller-owned reader without taking ownership of it.
struct ReadRef<'a, R: ElfReader> {
    inner: &'a R,
}

impl<'a, R: ElfReader> ReadRef<'a, R> {
    const fn new(inner: &'a R) -> Self {
        Self { inner }
    }
}

impl<R: ElfReader> ElfReader for ReadRef<'_, R> {
    fn len(&self) -> LoadResult<u64> {
        self.inner.len()
    }

    fn read_exact_at(&self, offset: u64, dst: &mut [u8]) -> LoadResult<()> {
        self.inner.read_exact_at(offset, dst)
    }
}
