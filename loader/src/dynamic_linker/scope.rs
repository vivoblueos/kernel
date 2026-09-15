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

//! Frozen symbol scopes.
//!
//! A [`ScopeSet`] is the immutable product of freezing a closed dependency
//! graph: two ordered lookups (the application scope and the system scope) plus
//! each image's ownership. Once frozen it never changes — no
//! image is added and no order is altered. The relocation engine
//! resolves references against it; the session owns the per-image
//! [`SymbolTable`]s the lookup reads from and charges each hash probe against
//! `max_symbol_lookups` — that counter is mutable session state, so it lives
//! outside this immutable value.

use alloc::vec::Vec;

use crate::{
    address::TargetAddress,
    dynamic_linker::{
        graph::DependencyGraph, session::SessionUsage, ImageId, ImageOwnership, SymbolBinding,
        SymbolDefinition, SymbolEntry, SymbolTable, SymbolType, SymbolVisibility,
    },
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult, LoadStage},
    identity::SessionLimits,
};

/// Region a resolved symbol's canonical target must live in, derived from its
/// ELF type: a function target is validated against an executable
/// region, an object/notype target against a readable region.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SymbolRegionKind {
    Executable,
    Readable,
}

impl SymbolRegionKind {
    #[inline]
    pub(crate) const fn for_type(symbol_type: SymbolType) -> Self {
        match symbol_type {
            SymbolType::Func => SymbolRegionKind::Executable,
            SymbolType::Object | SymbolType::NoType | SymbolType::Section => {
                SymbolRegionKind::Readable
            }
        }
    }
}

/// A symbol resolved against the frozen scopes.
///
/// `address` is the runtime address (the Thumb bit of a function is preserved);
/// `canonical` clears that bit so a control-flow target check can be performed
/// against an executable region. The owning [`ImageId`] is carried so a later
/// relocation policy can validate `S` against its provider allocation instead of
/// trusting a bare address.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ResolvedSymbol {
    owner: ImageId,
    address: TargetAddress,
    canonical: TargetAddress,
    size: u64,
    region: SymbolRegionKind,
    absolute: bool,
}

impl ResolvedSymbol {
    #[inline]
    pub(crate) fn from_entry(owner: ImageId, entry: &SymbolEntry) -> Self {
        let region = SymbolRegionKind::for_type(entry.symbol_type());
        let address = entry.value();
        let canonical = match entry.symbol_type() {
            SymbolType::Func => TargetAddress::new(address.get() & !1),
            _ => address,
        };
        Self {
            owner,
            address,
            canonical,
            size: entry.size(),
            region,
            absolute: entry.is_absolute(),
        }
    }

    #[inline]
    pub(crate) const fn owner(&self) -> ImageId {
        self.owner
    }

    #[inline]
    pub(crate) const fn address(&self) -> TargetAddress {
        self.address
    }

    #[inline]
    pub(crate) const fn canonical(&self) -> TargetAddress {
        self.canonical
    }

    #[inline]
    pub(crate) const fn size(&self) -> u64 {
        self.size
    }

    #[inline]
    pub(crate) const fn region(&self) -> SymbolRegionKind {
        self.region
    }

    #[inline]
    pub(crate) const fn is_absolute(&self) -> bool {
        self.absolute
    }
}

/// An ordered list of images searched left-to-right for a definition.
#[derive(Debug)]
pub(crate) struct SymbolScope {
    ordered_images: Vec<ImageId>,
}

impl SymbolScope {
    #[inline]
    pub(crate) fn ordered_images(&self) -> &[ImageId] {
        &self.ordered_images
    }
}

/// The frozen symbol scopes of a link session.
///
/// `application` is searched root → session-private → system-candidate, each
/// group in BFS discovery order; `system` holds only the system candidates, so a
/// system image's own relocation can never bind an application-private symbol.
/// `ownership` is indexed by [`ImageId`] and selects which of the two scopes
/// a requester may search.
#[derive(Debug)]
pub(crate) struct ScopeSet {
    application: SymbolScope,
    system: SymbolScope,
    ownership: Vec<ImageOwnership>,
}

impl ScopeSet {
    /// Freeze a closed dependency graph into immutable scopes.
    ///
    pub(crate) fn freeze(graph: &DependencyGraph) -> LoadResult<Self> {
        let nodes = graph.nodes();
        let mut session_private = Vec::new();
        let mut system_candidates = Vec::new();
        session_private
            .try_reserve_exact(nodes.len())
            .map_err(|_| scope_oom())?;
        system_candidates
            .try_reserve_exact(nodes.len())
            .map_err(|_| scope_oom())?;
        for node in nodes {
            match node.ownership() {
                ImageOwnership::SessionPrivate => session_private.push(node.id()),
                ImageOwnership::SystemCandidate | ImageOwnership::ExternalReady => {
                    system_candidates.push(node.id())
                }
            }
        }
        // BFS discovery order is the search order.
        session_private.sort_by_key(|id| nodes[id.get() as usize].discovery_index());
        system_candidates.sort_by_key(|id| nodes[id.get() as usize].discovery_index());

        let mut application_order = session_private;
        application_order
            .try_reserve(system_candidates.len())
            .map_err(|_| scope_oom())?;
        application_order.extend(system_candidates.iter().copied());

        let mut ownership = Vec::new();
        ownership
            .try_reserve_exact(nodes.len())
            .map_err(|_| scope_oom())?;
        for node in nodes {
            ownership.push(node.ownership());
        }

        Ok(Self {
            application: SymbolScope {
                ordered_images: application_order,
            },
            system: SymbolScope {
                ordered_images: system_candidates,
            },
            ownership,
        })
    }

    /// Resolve a global/weak reference by name for `requester`.
    ///
    /// The frozen scope is walked and the first strong definition wins,
    /// falling back to the first weak when no strong definition exists.
    /// Hidden, internal, and local definitions are not exported and are skipped.
    /// Owner-local protected references are resolved by exact index
    /// before this method is called. Returns `None` when no definition is found
    /// — the caller decides how to treat an undefined strong versus an
    /// undefined weak, since that depends on the reference's own
    /// binding in the requester's table.
    pub(crate) fn resolve_name(
        &self,
        symbols: &[&SymbolTable],
        requester: ImageId,
        name: &[u8],
        limits: &SessionLimits,
        usage: &mut SessionUsage,
    ) -> LoadResult<Option<ResolvedSymbol>> {
        let mut weak = None;
        for &image in self.scope_for(requester).ordered_images() {
            let Some(table) = symbols.get(image.get() as usize) else {
                continue;
            };
            usage.record_symbol_lookup(limits)?;
            let index = table.lookup(name);
            let Some(index) = index else {
                continue;
            };
            let Some(entry) = table.entry(index) else {
                continue;
            };
            if !is_exportable(entry) {
                continue;
            }
            match entry.binding() {
                SymbolBinding::Global => return Ok(Some(ResolvedSymbol::from_entry(image, entry))),
                SymbolBinding::Weak => {
                    weak.get_or_insert(ResolvedSymbol::from_entry(image, entry));
                }
                SymbolBinding::Local => {}
            }
        }
        Ok(weak)
    }

    /// Resolve a symbol by index within its owner, used for `STB_LOCAL`
    /// references that never enter the external scope.
    pub(crate) fn resolve_index(
        &self,
        symbols: &[&SymbolTable],
        owner: ImageId,
        index: u32,
    ) -> Option<ResolvedSymbol> {
        let entry = symbols.get(owner.get() as usize)?.entry(index)?;
        (entry.definition() == SymbolDefinition::Defined)
            .then(|| ResolvedSymbol::from_entry(owner, entry))
    }

    fn scope_for(&self, requester: ImageId) -> &SymbolScope {
        let is_system = self
            .ownership
            .get(requester.get() as usize)
            .is_some_and(|ownership| {
                matches!(
                    ownership,
                    ImageOwnership::SystemCandidate | ImageOwnership::ExternalReady
                )
            });
        if is_system {
            &self.system
        } else {
            &self.application
        }
    }
}

/// One recorded relocation binding: which image referenced which symbol and
/// which owner's definition won in the frozen scopes.
///
/// The frozen scope decision is captured per relocation, not re-derived after
/// publication: `provider` names the image whose definition the lookup
/// returned (`None` for a relative relocation or an undefined weak bound to
/// zero), `offset` is the relocation's image-relative target, and `name` is
/// the referenced symbol's byte name (empty when the relocation names no
/// symbol). Tests compare normalized image ids, symbol names and owners —
/// never raw addresses.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelocationBinding {
    requester: ImageId,
    name: Vec<u8>,
    provider: Option<ImageId>,
    kind: crate::relocation::RelocationKind,
    offset: TargetAddress,
}

impl RelocationBinding {
    #[inline]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        requester: ImageId,
        name: Vec<u8>,
        provider: Option<ImageId>,
        kind: crate::relocation::RelocationKind,
        offset: TargetAddress,
    ) -> Self {
        Self {
            requester,
            name,
            provider,
            kind,
            offset,
        }
    }

    /// The image whose relocation this binding records.
    #[inline]
    pub const fn requester(&self) -> ImageId {
        self.requester
    }

    /// The referenced symbol's byte name; empty for a symbol-less relocation
    /// (`R_ARM_RELATIVE`).
    #[inline]
    pub fn name(&self) -> &[u8] {
        &self.name
    }

    /// The provider image the frozen scopes resolved to, or `None` for a
    /// relative relocation or an undefined weak bound to zero.
    #[inline]
    pub const fn provider(&self) -> Option<ImageId> {
        self.provider
    }

    /// The relocation kind this binding was produced for.
    #[inline]
    pub const fn kind(&self) -> crate::relocation::RelocationKind {
        self.kind
    }

    /// The relocation's image-relative target offset.
    #[inline]
    pub const fn offset(&self) -> TargetAddress {
        self.offset
    }
}

#[inline]
fn is_exportable(entry: &SymbolEntry) -> bool {
    entry.definition() == SymbolDefinition::Defined
        && matches!(entry.binding(), SymbolBinding::Global | SymbolBinding::Weak)
        && matches!(
            entry.visibility(),
            SymbolVisibility::Default | SymbolVisibility::Protected
        )
}

fn scope_error(kind: LoadErrorKind, context: ErrorContext) -> LoadError {
    LoadError::new(kind, context).at_stage(LoadStage::Scope)
}

fn scope_oom() -> LoadError {
    scope_error(LoadErrorKind::OutOfMemory, ErrorContext::None)
}
