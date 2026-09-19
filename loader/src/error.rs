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

use alloc::boxed::Box;
use core::fmt::Debug;

use crate::address::TargetAddress;

pub type LoadResult<T> = core::result::Result<T, LoadError>;

#[derive(Clone, Copy, Debug)]
pub enum LoadStage {
    Beginning,
    Admit,
    Inspect,
    Plan,
    Allocate,
    Map,
    Decode,
    Relocate,
    Cache,
    Seal,
    Publish,
    Discover,
    Scope,
    LinkRelocate,
    LinkSeal,
}

#[derive(Clone, Copy, Debug)]
pub enum LoadErrorKind {
    BadElf,
    UnsupportedByProfile,
    OutOfBounds,
    IntegerOverflow,
    ResourceLimit,
    OutOfMemory,
    InvalidAlignment,
    PermissionConflict,
    IdentityConflict,
    AmbiguousStrongDefinition,
    Backend,
    Io,
    IncorrectLayout,
    NotAllocated,
}

#[derive(Debug)]
pub enum HeaderField {
    Magic,
    Class,
    Endian,
    Version,
    OsAbi,
    Type,
    Machine,
    Flags,
    Entry,
    HeaderSize,
    ProgramHeaderSize,
    ProgramHeaderTable,
}

#[derive(Debug)]
pub enum LimitKind {
    FileLength,
    ProgramHeaderCount,
    LoadSegmentCount,
    ImageSpan,
    SegmentAlignment,
    LayoutBytes,
    DynamicEntryCount,
    RelocationCount,
    RuntimeMetadataBytes,
    RelocationOperationBytes,
    StringTableBytes,
    ProtectionRangeCount,
    ImageCount,
    DependencyEdgeCount,
    DependencyDepth,
    TotalImageBytes,
    TotalRuntimeMetadataBytes,
    TotalRelocations,
    SymbolLookups,
    SymbolNameLength,
    DependencyNameLength,
}

#[derive(Debug)]
pub enum ProgramHeaderField {
    Type,
    FileRange,
    VirtualRange,
    DuplicateDynamic,
    DuplicatePhdr,
    DuplicateRelro,
    DuplicateStack,
    DuplicateInterpreter,
    DuplicateTls,
    UnsupportedInterpreter,
    UnsupportedTls,
    ExecutableStack,
    Permissions,
    Align,
    UnknownField,
}

#[non_exhaustive]
#[derive(Debug)]
pub enum ErrorContext {
    None,
    FileRange {
        offset: u64,
        len: u64,
        file_len: u64,
    },
    HeaderField {
        field: HeaderField,
        value: u64,
    },
    TargetRange {
        start: TargetAddress,
        len: u64,
        align: u64,
    },
    ProgramHeader {
        index: u16,
        field: ProgramHeaderField,
        value: u64,
    },
    Allocation {
        base: TargetAddress,
        len: u64,
        align: u64,
    },
    MemoryAccess {
        allocation_base: TargetAddress,
        allocation_len: u64,
        allocation_align: u64,
        offset: u64,
        len: u64,
    },
    DynamicTag {
        tag: u64,
        value: u64,
    },
    Relocation {
        offset: TargetAddress,
        raw_type: u32,
        symbol_index: u32,
    },
    Dependency {
        requester: u32,
        needed: Box<[u8]>,
    },
    Symbol {
        image: u32,
        index: u32,
        name: Box<[u8]>,
    },
    Limit {
        resource: LimitKind,
        actual: u64,
        maximum: u64,
    },
}

pub struct LoadError {
    stage: Option<LoadStage>,
    kind: LoadErrorKind,
    context: ErrorContext,
}

impl LoadError {
    #[inline]
    pub const fn new(kind: LoadErrorKind, context: ErrorContext) -> Self {
        Self {
            stage: None,
            kind,
            context,
        }
    }

    #[inline]
    pub const fn at_stage(mut self, stage: LoadStage) -> Self {
        if self.stage.is_none() {
            self.stage = Some(stage)
        }
        self
    }

    /// Attach an error context, keeping any context the error already has.
    #[inline]
    pub fn with_context(mut self, context: ErrorContext) -> Self {
        if matches!(self.context, ErrorContext::None) {
            self.context = context;
        }
        self
    }

    #[inline]
    pub const fn stage(&self) -> Option<LoadStage> {
        self.stage
    }

    #[inline]
    pub const fn kind(&self) -> LoadErrorKind {
        self.kind
    }

    #[inline]
    pub const fn context(&self) -> &ErrorContext {
        &self.context
    }
}

impl Debug for LoadError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut debug = f.debug_struct("LoadError");

        match self.stage {
            Some(stage) => {
                debug.field("stage", &stage);
            }
            None => {
                debug.field("stage", &"<stage not attached>");
            }
        }

        debug
            .field("kind", &self.kind)
            .field("context", &self.context)
            .finish()
    }
}
