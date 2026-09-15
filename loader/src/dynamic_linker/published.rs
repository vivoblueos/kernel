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

//! The published/imported system image contract.
//!
//! A [`PublishedImageDescriptor`] is the immutable, loader-neutral snapshot of
//! a Ready system DSO that a registry keeps long-term. It carries exactly what
//! a later application needs to *import* that image — identity, SONAME,
//! load bias, published runtime regions, export surface and the
//! program-header summary — so a second link binds against the same
//! provider without re-opening, re-mapping, re-relocating or re-sealing it.
//!
//! The descriptor never holds an [`AllocationLease`](crate::memory::AllocationLease):
//! the unique lease stays in the publisher's receipt, and the registry's own
//! `SystemDsoLease` lives outside this crate.

use alloc::{sync::Arc, vec::Vec};

use crate::{
    address::{TargetAddress, TargetRange},
    dynamic_linker::{
        artifact::{ArtifactIdentity, DependencyName},
        graph::DependencyNode,
        symbol::SymbolTable,
        ProgramHeaderRuntimeInfo,
    },
    elf::LoadSegmentInfo,
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult},
    image::LoadedRegion,
    MemoryPermissions,
};

/// One published runtime region of a Ready image, sufficient for control-flow
/// and data target range checks during a later import.
#[derive(Clone, Copy, Debug)]
pub struct PublishedRegion {
    runtime_range: TargetRange,
    permissions: MemoryPermissions,
}

impl PublishedRegion {
    #[inline]
    pub(crate) const fn new(runtime_range: TargetRange, permissions: MemoryPermissions) -> Self {
        Self {
            runtime_range,
            permissions,
        }
    }

    #[inline]
    pub const fn runtime_range(&self) -> TargetRange {
        self.runtime_range
    }

    #[inline]
    pub const fn permissions(&self) -> MemoryPermissions {
        self.permissions
    }
}

/// The frozen export surface of a Ready image, retained so a later import can
/// resolve symbols against it without re-decoding the image.
///
/// The inner table is kept crate-private: only the loader performs lookups.
pub struct PublishedSymbolTable {
    table: SymbolTable,
}

impl PublishedSymbolTable {
    #[inline]
    pub(crate) const fn new(table: SymbolTable) -> Self {
        Self { table }
    }

    #[inline]
    pub(crate) const fn table(&self) -> &SymbolTable {
        &self.table
    }

    /// Owned metadata bytes retained by the export surface, charged against
    /// `SessionLimits::total_runtime_metadata_bytes` when imported.
    #[inline]
    pub fn metadata_bytes(&self) -> u64 {
        self.table.metadata_bytes()
    }
}

// The inner `SymbolTable` owns no debug representation; the table's entry
// count and owned metadata bytes are the useful audit facts.
impl core::fmt::Debug for PublishedSymbolTable {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PublishedSymbolTable")
            .field("entries", &self.table.symbol_count())
            .field("metadata_bytes", &self.table.metadata_bytes())
            .finish()
    }
}

/// The immutable, loader-neutral snapshot of a Ready system DSO.
#[derive(Debug)]
pub struct PublishedImageDescriptor {
    identity: ArtifactIdentity,
    soname: Option<DependencyName>,
    load_bias: TargetAddress,
    regions: Vec<PublishedRegion>,
    exports: PublishedSymbolTable,
    program_headers: ProgramHeaderRuntimeInfo,
}

impl PublishedImageDescriptor {
    /// Build the descriptor for one sealed session image.
    ///
    /// `node` supplies the graph facts (identity and SONAME).
    /// The remaining arguments are the decoded facts `into_publish_parts` split out
    /// of the `RuntimeImageState`: the mapped regions, the load segments (whose
    /// permissions pair with each region), the load bias, the program-header
    /// summary and the owned symbol table.
    #[inline]
    pub(crate) fn from_node_and_state(
        node: &DependencyNode,
        regions: Vec<LoadedRegion>,
        load_segments: Vec<LoadSegmentInfo>,
        load_bias: TargetAddress,
        program_headers: ProgramHeaderRuntimeInfo,
        symbols: SymbolTable,
    ) -> LoadResult<Self> {
        let published_regions = publish_regions(&load_segments, &regions)?;
        Ok(Self {
            identity: node.artifact().try_clone()?,
            soname: node.soname().map(DependencyName::try_clone).transpose()?,
            load_bias,
            regions: published_regions,
            exports: PublishedSymbolTable::new(symbols),
            program_headers,
        })
    }

    #[inline]
    pub const fn identity(&self) -> &ArtifactIdentity {
        &self.identity
    }

    #[inline]
    pub const fn soname(&self) -> Option<&DependencyName> {
        self.soname.as_ref()
    }

    #[inline]
    pub const fn load_bias(&self) -> TargetAddress {
        self.load_bias
    }

    #[inline]
    pub fn regions(&self) -> &[PublishedRegion] {
        &self.regions
    }

    #[inline]
    pub const fn program_headers(&self) -> &ProgramHeaderRuntimeInfo {
        &self.program_headers
    }

    #[inline]
    pub(crate) const fn exports(&self) -> &SymbolTable {
        self.exports.table()
    }
}

/// A Ready provider handed back by the resolver instead of a reader.
///
/// Importing an image joins it to the dependency graph and symbol scopes while
/// skipping allocation, relocation, seal and init planning. The descriptor is
/// shared through an `Arc`: repeated dependency edges and concurrent imports
/// reuse the immutable registry snapshot without cloning its symbol table.
pub struct ImportedImageDescriptor {
    descriptor: Arc<PublishedImageDescriptor>,
}

impl ImportedImageDescriptor {
    /// Wrap a published descriptor into an import provider handed back by a
    /// resolver.
    #[inline]
    pub fn new(descriptor: Arc<PublishedImageDescriptor>) -> Self {
        Self { descriptor }
    }

    #[inline]
    pub fn descriptor(&self) -> &PublishedImageDescriptor {
        self.descriptor.as_ref()
    }

    #[inline]
    pub(crate) fn into_descriptor(self) -> Arc<PublishedImageDescriptor> {
        self.descriptor
    }
}

/// Pair each load segment's permissions with the runtime range of the region
/// mapped from it, producing the `PublishedRegion` list a later import uses for
/// control-flow and data target range checks. Load segments and regions
/// are decoded in lockstep (one region per PT_LOAD), so a length mismatch fails
/// closed rather than silently truncating.
fn publish_regions(
    load_segments: &[LoadSegmentInfo],
    regions: &[LoadedRegion],
) -> LoadResult<Vec<PublishedRegion>> {
    if load_segments.len() != regions.len() {
        return Err(LoadError::new(LoadErrorKind::BadElf, ErrorContext::None));
    }
    let mut published = Vec::new();
    published
        .try_reserve_exact(regions.len())
        .map_err(|_| LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None))?;
    for (segment, region) in load_segments.iter().zip(regions.iter()) {
        published.push(PublishedRegion::new(
            region.runtime_range(),
            segment.permissions(),
        ));
    }
    Ok(published)
}
