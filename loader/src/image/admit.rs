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
use goblin::{
    elf::program_header::{
        PF_R, PF_W, PF_X, PT_ARM_EXIDX, PT_DYNAMIC, PT_GNU_EH_FRAME, PT_GNU_RELRO, PT_GNU_STACK,
        PT_INTERP, PT_LOAD, PT_NOTE, PT_PHDR, PT_TLS,
    },
    elf64,
};

const PT_RISCV_ATTRIBUTES: u32 = 0x7000_0003;

use crate::{
    address::{FileRange, TargetAddress, TargetRange},
    dynamic_linker::{ArtifactRole, ProgramHeaderGeometry},
    elf::{DynamicSegmentInfo, ElfHeaderInfo, LoadSegmentInfo, ProgramHeaderInfo},
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult, LoadStage, ProgramHeaderField},
    identity::{ElfMachine, LoadPolicy, LoadRequest, SINGLE_IMAGE_LOAD_POLICY},
    image::{
        features::validate_dynamic_features,
        inspect::{InspectedImage, StackKind},
        DynamicFeatureSummary,
    },
    reader::ElfReader,
    MemoryPermissions,
};

/// A dependency shared object without a `PT_DYNAMIC` has nowhere to keep its
/// dynamic symbols or relocations: malformed ELF, reported without implying a
/// `DT_SONAME` requirement.
fn missing_dynamic_error() -> LoadError {
    LoadError::new(
        LoadErrorKind::BadElf,
        ErrorContext::ProgramHeader {
            index: 0,
            field: ProgramHeaderField::Type,
            value: u64::from(PT_DYNAMIC),
        },
    )
}

pub(crate) struct AdmittedImage<R: ElfReader> {
    reader: R,
    header: ElfHeaderInfo,
    request: LoadRequest,
    file_len: u64,
    policy: LoadPolicy,
    role: ArtifactRole,
}

impl<R: ElfReader> AdmittedImage<R> {
    #[inline]
    pub const fn new(
        reader: R,
        header: ElfHeaderInfo,
        request: LoadRequest,
        file_len: u64,
    ) -> Self {
        Self {
            reader,
            header,
            request,
            file_len,
            policy: SINGLE_IMAGE_LOAD_POLICY,
            role: ArtifactRole::ExecutableRoot,
        }
    }

    /// Override the policy used by `inspect`/`plan` and later decode. The
    /// public `prepare_image`/`load_elf` entry stays on [`SINGLE_IMAGE_LOAD_POLICY`];
    /// only the crate-internal `DynamicLinker` may pass
    /// [`crate::identity::DYNAMIC_LINK_LOAD_POLICY`].
    #[inline]
    pub(crate) fn inspect_with_policy(mut self, policy: LoadPolicy) -> Self {
        self.policy = policy;
        self
    }

    /// Mark this artifact as a shared object rather than the executable root.
    /// A shared object may have `e_entry == 0` and may omit `DT_SONAME`; it
    /// still requires a `PT_DYNAMIC` (checked during `inspect`).
    #[inline]
    pub(crate) const fn with_role(mut self, role: ArtifactRole) -> Self {
        self.role = role;
        self
    }

    pub fn inspect(self) -> LoadResult<InspectedImage<R>> {
        let count = self.header.program_header_count();
        self.request
            .limits()
            .check_load_segment_count(count.into())
            .map_err(|error| error.at_stage(LoadStage::Inspect))?;
        let mut load_segments = Vec::new();
        load_segments
            .try_reserve_exact(usize::from(count))
            .map_err(|_| {
                LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
                    .at_stage(LoadStage::Inspect)
            })?;

        let entry_size = usize::from(self.header.program_header_entry_size());
        let mut raw = [0; elf64::program_header::SIZEOF_PHDR];
        let mut dynamic = None;
        let mut relro = None;
        let mut stack = StackKind::NotDeclared;
        let mut interpreter = None;
        let mut tls = None;
        let mut phdr_vaddr = None;

        for index in 0..count {
            let offset = self
                .header
                .program_header_offset()
                .checked_add(u64::from(index) * u64::from(self.header.program_header_entry_size()))
                .ok_or_else(|| {
                    program_header_error(index, ProgramHeaderField::FileRange, 0)
                        .at_stage(LoadStage::Inspect)
                })?;
            self.reader
                .read_exact_at(offset, &mut raw[..entry_size])
                .map_err(|error| error.at_stage(LoadStage::Inspect))?;
            let program_header = ProgramHeaderInfo::decode(
                &raw[..entry_size],
                self.request.profile().class(),
                self.request.profile().endian(),
            )
            .map_err(|e| e.at_stage(LoadStage::Inspect))?;

            match program_header.r#type() {
                PT_LOAD => {
                    if program_header.file_size() > program_header.memory_size() {
                        return Err(program_header_error(
                            index,
                            ProgramHeaderField::FileRange,
                            program_header.file_size(),
                        )
                        .at_stage(LoadStage::Inspect));
                    }
                    let permissions = permissions_from_flags(program_header.flags());
                    if !self.policy.allows_segment_permissions(permissions) {
                        return Err(LoadError::new(
                            LoadErrorKind::UnsupportedByProfile,
                            ErrorContext::ProgramHeader {
                                index,
                                field: ProgramHeaderField::Permissions,
                                value: u64::from(permissions.bits()),
                            },
                        )
                        .at_stage(LoadStage::Inspect));
                    }
                    let file_range =
                        FileRange::new(program_header.file_offset(), program_header.file_size());
                    file_range
                        .validate(self.file_len)
                        .map_err(|e| e.at_stage(LoadStage::Inspect))?;
                    TargetRange::new(program_header.vaddr(), program_header.memory_size())
                        .end()
                        .map_err(|e| e.at_stage(LoadStage::Inspect))?;
                    load_segments.push(LoadSegmentInfo::new(
                        index,
                        file_range,
                        program_header.vaddr(),
                        program_header.memory_size(),
                        program_header.align(),
                        permissions,
                    ));
                }
                PT_DYNAMIC => {
                    if dynamic.is_some() {
                        return Err(program_header_error(
                            index,
                            ProgramHeaderField::DuplicateDynamic,
                            program_header.r#type().into(),
                        )
                        .at_stage(LoadStage::Inspect));
                    }
                    let file_range =
                        FileRange::new(program_header.file_offset(), program_header.file_size());
                    file_range
                        .validate(self.file_len)
                        .map_err(|e| e.at_stage(LoadStage::Inspect))?;
                    TargetRange::new(program_header.vaddr(), program_header.memory_size())
                        .end()
                        .map_err(|e| e.at_stage(LoadStage::Inspect))?;
                    dynamic = Some(DynamicSegmentInfo::new(
                        file_range,
                        program_header.vaddr(),
                        program_header.memory_size(),
                    ))
                }
                PT_GNU_RELRO => {
                    if relro.is_some() {
                        return Err(program_header_error(
                            index,
                            ProgramHeaderField::DuplicateRelro,
                            program_header.r#type().into(),
                        )
                        .at_stage(LoadStage::Inspect));
                    }
                    let target_range =
                        TargetRange::new(program_header.vaddr(), program_header.memory_size());
                    target_range
                        .end()
                        .map_err(|error| error.at_stage(LoadStage::Inspect))?;
                    relro = Some(target_range);
                }
                PT_GNU_STACK => {
                    if stack != StackKind::NotDeclared {
                        return Err(program_header_error(
                            index,
                            ProgramHeaderField::DuplicateStack,
                            program_header.r#type().into(),
                        )
                        .at_stage(LoadStage::Inspect));
                    }
                    if program_header.flags() & PF_X != 0 {
                        stack = StackKind::Executable;
                    } else {
                        stack = StackKind::NonExecutable
                    }
                }
                PT_INTERP => {
                    if interpreter.is_some() {
                        return Err(program_header_error(
                            index,
                            ProgramHeaderField::DuplicateInterpreter,
                            program_header.r#type().into(),
                        )
                        .at_stage(LoadStage::Inspect));
                    }
                    let file_range =
                        FileRange::new(program_header.file_offset(), program_header.file_size());
                    file_range
                        .validate(self.file_len)
                        .map_err(|e| e.at_stage(LoadStage::Inspect))?;
                    interpreter = Some(file_range);
                }
                PT_TLS => {
                    if tls.is_some() {
                        return Err(program_header_error(
                            index,
                            ProgramHeaderField::DuplicateTls,
                            program_header.r#type().into(),
                        )
                        .at_stage(LoadStage::Inspect));
                    }
                    if program_header.file_size() > program_header.memory_size() {
                        return Err(program_header_error(
                            index,
                            ProgramHeaderField::FileRange,
                            program_header.file_size(),
                        )
                        .at_stage(LoadStage::Inspect));
                    }
                    let file_range =
                        FileRange::new(program_header.file_offset(), program_header.file_size());
                    file_range
                        .validate(self.file_len)
                        .map_err(|e| e.at_stage(LoadStage::Inspect))?;
                    let target_range =
                        TargetRange::new(program_header.vaddr(), program_header.memory_size());
                    target_range
                        .end()
                        .map_err(|e| e.at_stage(LoadStage::Inspect))?;
                    tls = Some(target_range)
                }
                PT_PHDR => {
                    if phdr_vaddr.is_some() {
                        return Err(program_header_error(
                            index,
                            ProgramHeaderField::DuplicatePhdr,
                            program_header.r#type().into(),
                        )
                        .at_stage(LoadStage::Inspect));
                    }
                    phdr_vaddr = Some(program_header.vaddr());
                }
                PT_GNU_EH_FRAME => {}
                // Notes are structurally harmless metadata. The runtime loader
                // does not currently interpret their contents.
                PT_NOTE => {}
                PT_ARM_EXIDX if self.header.machine() == ElfMachine::Arm => {}
                PT_RISCV_ATTRIBUTES if self.header.machine() == ElfMachine::Riscv => {}
                t => {
                    if !self.policy.allows_unknown_program_headers() {
                        return Err(LoadError::new(
                            LoadErrorKind::UnsupportedByProfile,
                            ErrorContext::ProgramHeader {
                                index,
                                field: ProgramHeaderField::UnknownField,
                                value: t.into(),
                            },
                        )
                        .at_stage(LoadStage::Inspect));
                    }
                }
            }
        }
        if !self.policy.allows_executable_stack() && stack == StackKind::Executable {
            return Err(LoadError::new(
                LoadErrorKind::UnsupportedByProfile,
                ErrorContext::ProgramHeader {
                    index: 0,
                    field: ProgramHeaderField::ExecutableStack,
                    value: 0,
                },
            )
            .at_stage(LoadStage::Inspect));
        }
        if !self.policy.allows_interpreter() && interpreter.is_some() {
            return Err(LoadError::new(
                LoadErrorKind::UnsupportedByProfile,
                ErrorContext::ProgramHeader {
                    index: 0,
                    field: ProgramHeaderField::UnsupportedInterpreter,
                    value: 0,
                },
            )
            .at_stage(LoadStage::Inspect));
        }
        if !self.policy.allows_tls() && tls.is_some() {
            return Err(LoadError::new(
                LoadErrorKind::UnsupportedByProfile,
                ErrorContext::ProgramHeader {
                    index: 0,
                    field: ProgramHeaderField::UnsupportedTls,
                    value: 0,
                },
            )
            .at_stage(LoadStage::Inspect));
        }

        // The dynamic feature summary must be decided here, before
        // any allocation or write. A `PT_DYNAMIC` that requests an unsupported
        // feature is rejected while the write count is still zero.
        //
        // A dependency shared object must still carry a `PT_DYNAMIC` — its
        // symbols and relocations live there — but a missing table is a plain
        // malformed-ELF condition, not a SONAME one: the root and static
        // PIEs legitimately have none.
        let summary = match dynamic.as_ref() {
            Some(dynamic) => validate_dynamic_features(
                &self.reader,
                dynamic,
                self.policy,
                self.header.class(),
                self.header.endian(),
                self.request.limits(),
            )
            .map_err(|error| error.at_stage(LoadStage::Inspect))?,
            None if self.role == ArtifactRole::SharedObject => {
                return Err(missing_dynamic_error().at_stage(LoadStage::Inspect));
            }
            None => DynamicFeatureSummary::empty(),
        };

        let phdr_geometry = ProgramHeaderGeometry::new(
            self.header.program_header_entry_size(),
            self.header.program_header_count(),
            phdr_vaddr,
        );

        Ok(InspectedImage::new(
            self.reader,
            self.request,
            self.header,
            load_segments,
            dynamic,
            relro,
            stack,
            interpreter,
            tls,
            summary,
            phdr_geometry,
        )
        .with_policy(self.policy)
        .with_role(self.role))
    }
}

fn permissions_from_flags(flags: u32) -> MemoryPermissions {
    let mut permissions = MemoryPermissions::NONE;
    if flags & PF_R != 0 {
        permissions = permissions.bitor(MemoryPermissions::READ);
    }
    if flags & PF_W != 0 {
        permissions = permissions.bitor(MemoryPermissions::WRITE);
    }
    if flags & PF_X != 0 {
        permissions = permissions.bitor(MemoryPermissions::EXECUTE);
    }
    permissions
}

pub(crate) fn program_header_error(index: u16, field: ProgramHeaderField, value: u64) -> LoadError {
    LoadError::new(
        LoadErrorKind::BadElf,
        ErrorContext::ProgramHeader {
            index,
            field,
            value,
        },
    )
}
