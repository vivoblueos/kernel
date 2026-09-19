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

use crate::{
    address::{FileRange, TargetAddress, TargetRange},
    dynamic_linker::{ArtifactRole, ProgramHeaderGeometry},
    elf::{DynamicSegmentInfo, ElfHeaderInfo, LoadSegmentInfo},
    error::{
        ErrorContext, HeaderField, LoadError, LoadErrorKind, LoadResult, LoadStage,
        ProgramHeaderField,
    },
    identity::{EntryMode, LoadPolicy, LoadRequest, SINGLE_IMAGE_LOAD_POLICY},
    image::{admit::program_header_error, plan::PlannedImage, DynamicFeatureSummary},
    reader::ElfReader,
    MemoryPermissions,
};

#[derive(PartialEq)]
pub(crate) enum StackKind {
    NotDeclared,
    NonExecutable,
    Executable,
}

pub(crate) struct InspectedImage<R: ElfReader> {
    reader: R,
    request: LoadRequest,
    header: ElfHeaderInfo,
    load_segments: Vec<LoadSegmentInfo>,
    dynamic: Option<DynamicSegmentInfo>,
    relro: Option<TargetRange>,
    stack: StackKind,
    interpreter: Option<FileRange>,
    tls: Option<TargetRange>,
    policy: LoadPolicy,
    role: ArtifactRole,
    summary: DynamicFeatureSummary,
    phdr_geometry: ProgramHeaderGeometry,
}

impl<R: ElfReader> InspectedImage<R> {
    #[inline]
    #[allow(clippy::too_many_arguments)]
    pub const fn new(
        reader: R,
        request: LoadRequest,
        header: ElfHeaderInfo,
        load_segments: Vec<LoadSegmentInfo>,
        dynamic: Option<DynamicSegmentInfo>,
        relro: Option<TargetRange>,
        stack: StackKind,
        interpreter: Option<FileRange>,
        tls: Option<TargetRange>,
        summary: DynamicFeatureSummary,
        phdr_geometry: ProgramHeaderGeometry,
    ) -> Self {
        Self {
            reader,
            request,
            header,
            load_segments,
            dynamic,
            relro,
            stack,
            interpreter,
            tls,
            policy: SINGLE_IMAGE_LOAD_POLICY,
            role: ArtifactRole::ExecutableRoot,
            summary,
            phdr_geometry,
        }
    }

    #[inline]
    pub(crate) fn with_policy(mut self, policy: LoadPolicy) -> Self {
        self.policy = policy;
        self
    }

    #[inline]
    pub(crate) const fn with_role(mut self, role: ArtifactRole) -> Self {
        self.role = role;
        self
    }

    /// The file-scanning view of an inspected image: the dynamic
    /// segment (if any), the dynamic feature summary and the load segments, for
    /// the read-only dependency scanner to resolve dynstr offsets against the
    /// file instead of a mapped copy.
    #[inline]
    pub(crate) fn scan_parts(
        &self,
    ) -> (
        Option<&DynamicSegmentInfo>,
        &DynamicFeatureSummary,
        &[LoadSegmentInfo],
    ) {
        (self.dynamic.as_ref(), &self.summary, &self.load_segments)
    }

    pub fn plan(mut self) -> LoadResult<PlannedImage<R>> {
        let mut r = 0;
        for segment in self.load_segments.iter() {
            if segment.memory_size() == 0 {
                continue;
            }
            r += 1;
            let align = normalize_alignment(segment.align(), segment.index())
                .map_err(|error| error.at_stage(LoadStage::Plan))?;
            self.request
                .limits()
                .check_segment_alignment(align)
                .map_err(|error| error.at_stage(LoadStage::Plan))?;
            if segment.file_range().offset() % align != segment.vaddr().get() % align {
                return Err(program_header_error(
                    segment.index(),
                    ProgramHeaderField::Align,
                    align,
                )
                .at_stage(LoadStage::Plan));
            }
            if segment.permissions().contains(MemoryPermissions::WRITE)
                && segment.permissions().contains(MemoryPermissions::EXECUTE)
            {
                return Err(LoadError::new(
                    LoadErrorKind::PermissionConflict,
                    ErrorContext::ProgramHeader {
                        index: segment.index(),
                        field: ProgramHeaderField::VirtualRange,
                        value: segment.vaddr().get(),
                    },
                )
                .at_stage(LoadStage::Plan));
            }
            if !self
                .policy
                .allows_segment_permissions(segment.permissions())
            {
                return Err(LoadError::new(
                    LoadErrorKind::UnsupportedByProfile,
                    ErrorContext::ProgramHeader {
                        index: segment.index(),
                        field: ProgramHeaderField::Permissions,
                        value: u64::from(segment.permissions().bits()),
                    },
                )
                .at_stage(LoadStage::Plan));
            }
        }
        if r == 0 {
            return Err(
                LoadError::new(LoadErrorKind::BadElf, ErrorContext::None).at_stage(LoadStage::Plan)
            );
        }

        self.load_segments
            .sort_unstable_by_key(|segment| segment.vaddr().get());
        for pair in self.load_segments.windows(2) {
            let vaddr_range1 = TargetRange::new(pair[0].vaddr(), pair[0].memory_size());
            let vaddr_range2 = TargetRange::new(pair[1].vaddr(), pair[1].memory_size());
            if vaddr_range1.overlaps(vaddr_range2) {
                return Err(program_header_error(
                    pair[1].index(),
                    ProgramHeaderField::VirtualRange,
                    pair[1].vaddr().get(),
                )
                .at_stage(LoadStage::Plan));
            }
        }
        let segment_max_align = self
            .load_segments
            .iter()
            .map(|segment| segment.align())
            .max()
            .unwrap_or(1);
        let min_vaddr = self.load_segments[0].vaddr();
        let max_vaddr = self
            .load_segments
            .iter()
            .map(|segment| segment.vaddr().checked_add(segment.memory_size()))
            .try_fold(TargetAddress::new(0), |current, next| {
                let next = next.map_err(|e| e.at_stage(LoadStage::Plan))?;
                Ok::<_, LoadError>(core::cmp::max(current, next))
            })?;
        let aligned_min_vaddr = min_vaddr
            .align_down(segment_max_align)
            .map_err(|e| e.at_stage(LoadStage::Plan))?;
        let aligned_max_vaddr = max_vaddr
            .align_up(segment_max_align)
            .map_err(|e| e.at_stage(LoadStage::Plan))?;
        let image_span = aligned_max_vaddr
            .checked_sub(aligned_min_vaddr)
            .map_err(|e| e.at_stage(LoadStage::Plan))?;
        self.request
            .limits()
            .check_image_span(image_span)
            .map_err(|error| error.at_stage(LoadStage::Plan))?;

        let entry_vaddr = TargetAddress::new(self.header.entry());
        let entry_mode = self.request.profile().entry_mode();
        let instruction_alignment = u64::from(entry_mode.instruction_alignment());
        let minimum_instruction_size = u64::from(entry_mode.minimum_instruction_size());
        // The executable root must carry a canonical entry fully inside an
        // executable segment. A shared object is not entered through its ELF
        // entry, so `e_entry == 0` is accepted; a non-zero DSO entry still gets
        // the same format and range checks but is never published as the
        // application entry point.
        let canonical_entry_vaddr =
            if self.role == ArtifactRole::SharedObject && self.header.entry() == 0 {
                entry_vaddr
            } else {
                let canonical = canonical_entry(entry_vaddr, entry_mode)
                    .map_err(|error| error.at_stage(LoadStage::Plan))?;
                // A whole instruction must lie inside an executable segment, and
                // the canonical entry must satisfy the profile's instruction
                // alignment.
                if instruction_alignment != 0 && canonical.get() % instruction_alignment != 0 {
                    return Err(LoadError::new(
                        LoadErrorKind::InvalidAlignment,
                        ErrorContext::TargetRange {
                            start: canonical,
                            len: minimum_instruction_size,
                            align: instruction_alignment,
                        },
                    )
                    .at_stage(LoadStage::Plan));
                }
                let executable = self.load_segments.iter().any(|segment| {
                    segment.permissions().contains(MemoryPermissions::EXECUTE)
                        && TargetRange::new(segment.vaddr(), segment.memory_size())
                            .contains_span(canonical, minimum_instruction_size)
                });
                if !executable {
                    return Err(LoadError::new(
                        LoadErrorKind::PermissionConflict,
                        ErrorContext::TargetRange {
                            start: canonical,
                            len: minimum_instruction_size,
                            align: instruction_alignment,
                        },
                    )
                    .at_stage(LoadStage::Plan));
                }
                canonical
            };

        if let Some(relro) = self.relro {
            let valid_relro = self.load_segments.iter().any(|segment| {
                TargetRange::new(segment.vaddr(), segment.memory_size())
                    .contains_span(relro.start(), relro.len())
                    && segment.permissions().contains(MemoryPermissions::WRITE)
            });
            if !valid_relro {
                return Err(LoadError::new(
                    LoadErrorKind::PermissionConflict,
                    ErrorContext::TargetRange {
                        start: relro.start(),
                        len: relro.len(),
                        align: 0,
                    },
                )
                .at_stage(LoadStage::Plan));
            }
        }

        Ok(PlannedImage::new(
            self.reader,
            self.request,
            aligned_min_vaddr,
            image_span,
            segment_max_align,
            entry_vaddr,
            canonical_entry_vaddr,
            self.load_segments,
            self.dynamic,
            self.relro,
            self.stack,
            self.interpreter,
            self.tls,
            self.phdr_geometry,
        ))
    }
}

fn canonical_entry(entry: TargetAddress, mode: EntryMode) -> LoadResult<TargetAddress> {
    match mode {
        EntryMode::Direct { .. } => Ok(entry),
        EntryMode::Thumb { .. } => {
            // ARM Thumb entry: bit 0 must be set (Thumb state marker) and is
            // cleared to obtain the canonical instruction address.
            if entry.get() & 1 == 0 {
                return Err(LoadError::new(
                    LoadErrorKind::BadElf,
                    ErrorContext::HeaderField {
                        field: HeaderField::Entry,
                        value: entry.get(),
                    },
                ));
            }
            Ok(TargetAddress::new(entry.get() & !1))
        }
    }
}

fn normalize_alignment(align: u64, index: u16) -> LoadResult<u64> {
    match align {
        0 | 1 => Ok(1),
        value if value.is_power_of_two() => Ok(value),
        value => Err(LoadError::new(
            LoadErrorKind::InvalidAlignment,
            ErrorContext::ProgramHeader {
                index,
                field: ProgramHeaderField::Align,
                value,
            },
        )),
    }
}
