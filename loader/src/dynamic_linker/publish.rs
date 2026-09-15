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

//! Link map and prepared manifest for atomic publication.
//!
//! [`build_manifest`] derives the per-image [`LinkMapEntry`] list and the
//! root's runtime entry from the closed dependency graph and the relocated
//! images. The result is the [`PreparedLinkManifest`] the host
//! [`LinkPublisher`](crate::dynamic_linker::LinkPublisher) validates in 's
//! `prepare_batch` — a pure, allocation-only description that never turns a
//! target address into a host function pointer and never touches the committed
//! snapshot. The owned [`LinkContext`]/[`crate::dynamic_linker::CommittedImage`]
//! and the [`crate::dynamic_linker::LinkProduct`] land with , where the
//! session's graph/scopes/images move into the committed owner.

use alloc::{sync::Arc, vec::Vec};

use crate::{
    address::TargetAddress,
    dynamic_linker::{
        graph::{DependencyEdge, DependencyGraph},
        scope::RelocationBinding,
        DependencyName, ImageId, ImageOwnership, LifecyclePlans, PublishedImageDescriptor,
    },
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult, LoadStage},
    memory::AllocationLease,
};

/// One entry of the published link map, in stable image-id order.
///
/// The entry retains only the facts consumed by the publisher and diagnostics;
/// allocation ownership remains in the publisher receipt.
#[derive(Clone, Debug)]
pub struct LinkMapEntry {
    owner: ImageId,
    soname: Option<DependencyName>,
    ownership: ImageOwnership,
    load_bias: TargetAddress,
}

impl LinkMapEntry {
    #[inline]
    #[inline]
    pub const fn owner(&self) -> ImageId {
        self.owner
    }

    #[inline]
    pub const fn soname(&self) -> Option<&DependencyName> {
        self.soname.as_ref()
    }

    /// How this image participates in the link: a session-private
    /// artifact, a system candidate, or an externally imported Ready DSO. The
    /// publisher uses it — never the image id or SONAME — to decide which lease
    /// owner receives the image's allocation.
    #[inline]
    pub const fn ownership(&self) -> ImageOwnership {
        self.ownership
    }

    #[inline]
    pub const fn load_bias(&self) -> TargetAddress {
        self.load_bias
    }
}

/// The pre-commit publication description a [`LinkPublisher`](crate::dynamic_linker::LinkPublisher)
/// validates. It owns only the allocatable facts the publisher must
/// check (entry, link-map slots); it holds no lease and mutates no snapshot.
#[derive(Clone, Debug)]
pub struct PreparedLinkManifest {
    entry: TargetAddress,
    link_map: Vec<LinkMapEntry>,
}

impl PreparedLinkManifest {
    /// The root's mapped runtime entry, Thumb bit preserved.
    #[inline]
    pub const fn entry(&self) -> TargetAddress {
        self.entry
    }

    #[inline]
    pub fn link_map(&self) -> &[LinkMapEntry] {
        &self.link_map
    }

    #[inline]
    pub(crate) fn into_parts(self) -> (TargetAddress, Vec<LinkMapEntry>) {
        (self.entry, self.link_map)
    }
}

/// Per-image inputs to manifest construction, borrowed from the session's
/// relocated and imported images.
///
/// A loaded root carries its runtime entry; an imported provider contributes
/// the same owner/load-bias facts without a second allocation.
pub(crate) enum LinkMapImage {
    Loaded {
        image_id: ImageId,
        load_bias: TargetAddress,
        runtime_entry: TargetAddress,
    },
    Imported {
        image_id: ImageId,
        load_bias: TargetAddress,
    },
}

impl LinkMapImage {
    #[inline]
    pub(crate) const fn loaded(
        image_id: ImageId,
        load_bias: TargetAddress,
        runtime_entry: TargetAddress,
    ) -> Self {
        Self::Loaded {
            image_id,
            load_bias,
            runtime_entry,
        }
    }

    #[inline]
    pub(crate) const fn imported(image_id: ImageId, load_bias: TargetAddress) -> Self {
        Self::Imported {
            image_id,
            load_bias,
        }
    }

    #[inline]
    pub(crate) const fn image_id(&self) -> ImageId {
        match self {
            Self::Loaded { image_id, .. } | Self::Imported { image_id, .. } => *image_id,
        }
    }
}

/// Build the prepared manifest from the closed graph and every admitted image.
///
/// The link map is emitted in image-id order (root first, then discovery
/// order). Only the root contributes a runtime entry; every entry keeps
/// its owner and identity so a publisher can validate capacity, identity and
/// generation without dereferencing a bare address. Imported Ready images are
/// joined at their graph-assigned ids.
pub(crate) fn build_manifest(
    graph: &DependencyGraph,
    images: &[LinkMapImage],
) -> LoadResult<PreparedLinkManifest> {
    let mut entries = Vec::new();
    entries
        .try_reserve_exact(images.len())
        .map_err(|_| publish_oom())?;

    let mut root_entry = None;
    for image in images {
        let image_id = image.image_id();
        let node = graph
            .node(image_id)
            .ok_or_else(|| publish_error(LoadErrorKind::BadElf, ErrorContext::None))?;

        let load_bias = match image {
            LinkMapImage::Loaded {
                runtime_entry,
                load_bias,
                ..
            } => {
                if image_id.get() == 0 {
                    let runtime = *runtime_entry;
                    root_entry = Some(runtime);
                }
                *load_bias
            }
            LinkMapImage::Imported { load_bias, .. } => *load_bias,
        };

        entries.push(LinkMapEntry {
            owner: image_id,
            soname: node.soname().map(DependencyName::try_clone).transpose()?,
            ownership: node.ownership(),
            load_bias,
        });
    }

    let entry =
        root_entry.ok_or_else(|| publish_error(LoadErrorKind::BadElf, ErrorContext::None))?;
    Ok(PreparedLinkManifest {
        entry,
        link_map: entries,
    })
}

fn publish_error(kind: LoadErrorKind, context: ErrorContext) -> LoadError {
    LoadError::new(kind, context).at_stage(LoadStage::LinkSeal)
}

fn publish_oom() -> LoadError {
    publish_error(LoadErrorKind::OutOfMemory, ErrorContext::None)
}

/// One image in a published link context.
///
/// Unlike [`LinkMapEntry`], this value pairs the link-map facts with the
/// full [`PublishedImageDescriptor`]: the immutable export surface, published
/// regions and program-header summary a
/// later link imports instead of re-loading. It holds no lease: the
/// unique allocation lease is transferred into the publisher's `Receipt` at
/// commit, making the publisher receipt the long-term allocation owner.
#[derive(Debug)]
pub struct CommittedImage {
    owner: ImageId,
    ownership: ImageOwnership,
    descriptor: Arc<PublishedImageDescriptor>,
}

impl CommittedImage {
    #[inline]
    pub(crate) fn new(
        owner: ImageId,
        ownership: ImageOwnership,
        descriptor: Arc<PublishedImageDescriptor>,
    ) -> Self {
        Self {
            owner,
            ownership,
            descriptor,
        }
    }

    #[inline]
    pub const fn owner(&self) -> ImageId {
        self.owner
    }

    #[inline]
    pub const fn ownership(&self) -> ImageOwnership {
        self.ownership
    }

    /// The immutable descriptor the registry retains for cross-application
    /// import.
    #[inline]
    pub fn descriptor(&self) -> &PublishedImageDescriptor {
        self.descriptor.as_ref()
    }

    /// Clone the shared descriptor handle for a long-lived registry entry.
    #[inline]
    pub fn descriptor_handle(&self) -> Arc<PublishedImageDescriptor> {
        Arc::clone(&self.descriptor)
    }
}

/// The owned, immutable context a [`LinkProduct`] exposes: the closed
/// dependency graph and one committed image per id.
pub struct LinkContext {
    edges: Vec<DependencyEdge>,
    images: Vec<CommittedImage>,
}

impl LinkContext {
    #[inline]
    pub(crate) fn new(graph: DependencyGraph, images: Vec<CommittedImage>) -> Self {
        Self {
            edges: graph.into_edges(),
            images,
        }
    }

    /// The recorded dependency edges (requester → provider), for the
    /// lifecycle diagnostic to assert the closure shape.
    #[inline]
    pub fn graph_edges(&self) -> &[crate::dynamic_linker::graph::DependencyEdge] {
        &self.edges
    }

    #[inline]
    pub fn images(&self) -> &[CommittedImage] {
        &self.images
    }
}

/// The lease payload handed to [`LinkPublisher::commit_batch`](LinkPublisher::commit_batch).
///
/// Every fallible check (capacity, identity, generation, entry, link-map slot)
/// already happened in `prepare_batch`; the publisher's prepared state encodes
/// the entry and link-map slots. The only thing the infallible commit step
/// must move is the set of unique allocation leases, so this value is exactly
/// that set, in image-id order.
pub struct CommittingLinkProduct {
    leases: Vec<AllocationLease>,
}

impl CommittingLinkProduct {
    #[inline]
    pub(crate) fn new(leases: Vec<AllocationLease>) -> Self {
        Self { leases }
    }

    #[inline]
    pub fn into_leases(self) -> Vec<AllocationLease> {
        self.leases
    }
}

/// The atomic publication boundary between the loader and the external system
///
/// `prepare_batch` performs every fallible check without mutating the visible
/// snapshot; `commit_batch` only moves the prepared state and the leases, and
/// must not allocate, validate, panic, or otherwise fail. The returned
/// `Receipt` is the publisher's long-term owner of the committed images.
pub trait LinkPublisher {
    type PreparedBatch;
    type Receipt;

    fn prepare_batch(&mut self, manifest: &PreparedLinkManifest)
        -> LoadResult<Self::PreparedBatch>;

    /// # Safety
    ///
    /// `prepared` and `product` must come from the same active link session on
    /// this publisher. Implementations must move the leases into the committed
    /// owner and must not allocate, validate, panic, or otherwise fail.
    unsafe fn commit_batch(
        &mut self,
        prepared: Self::PreparedBatch,
        product: CommittingLinkProduct,
    ) -> Self::Receipt;
}

/// The published result of a link session.
///
/// This is the immutable snapshot a reader observes after commit: the owned
/// context, the root entry, the constructor/destructor plans, the flat link
/// map, and the publisher's receipt (the long-term owner
/// of every committed allocation lease).
pub struct LinkProduct<Receipt> {
    context: LinkContext,
    entry: TargetAddress,
    /// The ownership-partitioned lifecycle.
    plans: LifecyclePlans,
    link_map: Vec<LinkMapEntry>,
    /// Recorded scope decision for each relocation.
    bindings: Vec<crate::dynamic_linker::scope::RelocationBinding>,
    publication: Receipt,
}

impl<Receipt> LinkProduct<Receipt> {
    #[inline]
    pub(crate) fn new(
        context: LinkContext,
        entry: TargetAddress,
        plans: LifecyclePlans,
        link_map: Vec<LinkMapEntry>,
        bindings: Vec<crate::dynamic_linker::scope::RelocationBinding>,
        publication: Receipt,
    ) -> Self {
        Self {
            context,
            entry,
            plans,
            link_map,
            bindings,
            publication,
        }
    }

    #[inline]
    pub const fn context(&self) -> &LinkContext {
        &self.context
    }

    /// The root's runtime entry (Thumb bit preserved on ARM).
    #[inline]
    pub const fn entry(&self) -> TargetAddress {
        self.entry
    }

    /// The ownership-partitioned lifecycle plans.
    #[inline]
    pub const fn lifecycle_plans(&self) -> &LifecyclePlans {
        &self.plans
    }

    #[inline]
    pub fn link_map(&self) -> &[LinkMapEntry] {
        &self.link_map
    }

    /// Mutable access to the publisher receipt, for the host to move parts
    /// out before installation. System backings move into the registry at
    /// batch publication.
    #[inline]
    pub fn publication_mut(&mut self) -> &mut Receipt {
        &mut self.publication
    }

    #[inline]
    /// The relocation-binding diagnostic: the recorded scope
    /// decision per relocation — requester, symbol name and winning provider.
    #[inline]
    pub fn relocation_bindings(&self) -> &[RelocationBinding] {
        &self.bindings
    }

    /// Consume the product and hand back the publisher's receipt, the long-term
    /// owner of every committed allocation lease.
    ///
    /// Dropping the rest of the product — the context, plans,
    /// link map — releases only metadata: no allocation lease or
    /// counted DSO lease authority lives outside the receipt, so the reaper can
    /// destructure the receipt after this call and release the backing exactly
    /// once.
    #[inline]
    pub fn into_publication(self) -> Receipt {
        self.publication
    }
}
