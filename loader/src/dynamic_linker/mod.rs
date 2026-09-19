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

//! Multi-image dynamic linking for Thumbv7 applications.
//!
//! The module owns artifact resolution, dependency discovery, symbol scope,
//! relocation, lifecycle planning and publication.

mod artifact;
mod graph;
mod lifecycle;
mod metadata;
mod publish;
mod published;
mod relocate;
mod scope;
mod session;
mod symbol;

pub use artifact::{
    ArtifactIdentity, ArtifactResolver, ArtifactRole, DependencyName, DependencyRequest,
    DependencyRequester, DependencyResolution, FileIdentity, ImageId, ImageOwnership,
    ResolvedArtifact,
};

pub use published::{
    ImportedImageDescriptor, PublishedImageDescriptor, PublishedRegion, PublishedSymbolTable,
};

pub(crate) use lifecycle::LifecycleImage;
pub use lifecycle::{FiniPlan, ImageFiniPlan, InitPlan, LifecycleEntry, LifecyclePlans};
pub use metadata::ProgramHeaderRuntimeInfo;
pub(crate) use metadata::{
    ImageLifecycleMetadata, ProgramHeaderGeometry, RelocationTables, RuntimeImageMetadata,
    RuntimeImageState,
};
pub(crate) use publish::{build_manifest, LinkMapImage};
pub use publish::{
    CommittedImage, CommittingLinkProduct, LinkContext, LinkMapEntry, LinkProduct, LinkPublisher,
    PreparedLinkManifest,
};
pub use scope::RelocationBinding;
pub(crate) use scope::{ResolvedSymbol, ScopeSet, SymbolRegionKind, SymbolScope};
pub use session::{
    BuildingSession, DynamicLinker, LinkSession, RelocatedSession, ScopedSession, SealedSession,
};
pub(crate) use symbol::{
    symbol_count_from_hash, SymbolBinding, SymbolDefinition, SymbolEntry, SymbolTable, SymbolType,
    SymbolVisibility,
};
