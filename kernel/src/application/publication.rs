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

//! Kernel-side link publication.
//!
//! [`KernelLinkPublisher`] is the [`LinkPublisher`] the `ApplicationLoader`
//! drives the staged `DynamicLinker::publish` with. Its receipt —
//! [`KernelLinkReceipt`] — receives every raw
//! [`AllocationLease`](blueos_loader::AllocationLease) produced by the link
//! session and partitions them by residency:
//!
//! * `private_allocations` hold the executable root (and any session-private
//!   image); they are released by the group reaper when the application
//!   terminates.
//! * `system_allocations` temporarily hold first-loading system DSO candidates.
//!   Before the group starts, the loader moves them into the system registry.
//!   If initialization later fails, the registry returns those allocations to
//!   the receipt so they remain mapped until the failed group is quiescent.
//!
//! `prepare_batch` performs the only fallible work: it proves the target group
//! has no linked resources yet, derives the private/system residency of each
//! rollback-log lease from the manifest's explicit `ImageOwnership`, and
//! pre-reserves the commit sinks. The leases arrive in `commit_batch` in
//! creation order (the same order the manifest's non-imported entries list), so
//! `commit_batch` only partitions — it never allocates, validates or fails.

use alloc::vec::Vec;

use blueos_loader::{
    AllocationLease, CommittingLinkProduct, ErrorContext, ImageOwnership, LinkPublisher, LoadError,
    LoadErrorKind, LoadResult, PreparedLinkManifest,
};

use crate::application::{
    group::{GroupState, ThreadGroup},
    registry::SystemDsoLease,
};

/// The long-term owner of a committed link's raw allocation leases.
///
/// Besides the raw [`AllocationLease`]s (split by residency), the receipt holds
/// the counted [`SystemDsoLease`] set the resolver minted for every Ready DSO
/// this link *imported*. Those references keep the root and every provider
/// valid across `main` and fini. Their `Drop` delivers the registry's
/// quiescence event after the last application releases them.
pub struct KernelLinkReceipt {
    private_allocations: Vec<AllocationLease>,
    system_allocations: Vec<AllocationLease>,
    system_leases: Vec<SystemDsoLease>,
}

impl KernelLinkReceipt {
    /// Take the first-loading system candidates' unique allocation leases.
    ///
    /// The loader moves system allocations into the registry at batch
    /// publication, so the receipt only retains private allocations and
    /// imported leases from then on.
    pub fn take_system_allocations(&mut self) -> Vec<AllocationLease> {
        core::mem::take(&mut self.system_allocations)
    }

    /// Retain system candidate allocations whose constructors did not finish.
    ///
    /// The registry has already hidden their descriptors and reopened their
    /// slots. Keeping the allocations in the group receipt delays the physical
    /// release until every thread that could still execute in them has left.
    pub fn retain_failed_system_allocations(&mut self, allocations: Vec<AllocationLease>) {
        debug_assert!(self.system_allocations.is_empty());
        self.system_allocations = allocations;
    }

    /// Attach the first group's system leases, minted when the initialization
    /// batch completes: the first-loading group holds ordinary
    /// counted leases like any importer, released at group exit.
    pub fn attach_system_leases(&mut self, leases: Vec<SystemDsoLease>) {
        self.system_leases.extend(leases);
    }

    /// Destructure the receipt so the reaper can release each owned resource
    /// exactly once.
    pub fn into_parts(
        self,
    ) -> (
        Vec<AllocationLease>,
        Vec<AllocationLease>,
        Vec<SystemDsoLease>,
    ) {
        (
            self.private_allocations,
            self.system_allocations,
            self.system_leases,
        )
    }
}

/// Fallible state produced by [`KernelLinkPublisher::prepare_batch`].
///
/// `owners` records the residency of each rollback-log lease in creation order;
/// `private`/`system` are the pre-reserved commit sinks so `commit_batch` can
/// partition the leases without allocating.
pub struct KernelLinkPreparedBatch {
    owners: Vec<ImageOwnership>,
    private: Vec<AllocationLease>,
    system: Vec<AllocationLease>,
}

/// The kernel publication boundary.
///
/// `prepare_batch` re-verifies the target group is still unlinked, checks the
/// imported Ready leases against the manifest's imported nodes, and precomputes
/// the private/system split from the manifest; `commit_batch` then only moves
/// the raw leases and the imported leases into the receipt.
pub struct KernelLinkPublisher {
    group: ThreadGroup,
    /// The counted references to every Ready DSO this link imported, minted by
    /// the resolver and moved in by [`KernelLinkPublisher::import_leases`]
    /// before `publish` is driven. `commit_batch` moves them into the receipt.
    system_leases: Vec<SystemDsoLease>,
}

impl KernelLinkPublisher {
    /// Build a publisher that will publish into `group`.
    pub fn new(group: ThreadGroup) -> Self {
        Self {
            group,
            system_leases: Vec::new(),
        }
    }

    /// Hand over the imported Ready DSO leases the resolver accumulated, for the
    /// receipt to own across the application lifetime. Must be called
    /// after dependency resolution and before `publish`; `prepare_batch` verifies
    /// they correspond one-to-one with the manifest's imported nodes.
    pub fn import_leases(&mut self, leases: Vec<SystemDsoLease>) {
        self.system_leases = leases;
    }
}

impl LinkPublisher for KernelLinkPublisher {
    type PreparedBatch = KernelLinkPreparedBatch;
    type Receipt = KernelLinkReceipt;

    fn prepare_batch(
        &mut self,
        manifest: &PreparedLinkManifest,
    ) -> LoadResult<Self::PreparedBatch> {
        // The group must not already carry linked resources: a second install
        // would expose a half-written link map to a reader.
        if self.group.state() != GroupState::New {
            return Err(publish_error());
        }

        // The rollback log drains in creation order, which is exactly the order
        // the manifest lists loaded images (the root id 0 first, then each
        // discovered dependency in id order); imported Ready images carry no raw
        // lease and are skipped here. Record the residency of each raw
        // lease so `commit_batch` can partition without re-deriving it, and
        // reserve the commit sinks up front. Every imported node must have a
        // matching counted lease minted by the resolver — a mismatch means the
        // resolver hand-off was skipped and the link must not publish.
        let mut imported_nodes = 0usize;
        let mut owners = Vec::new();
        let mut private_cap = 0usize;
        let mut system_cap = 0usize;
        for entry in manifest.link_map() {
            let ownership = entry.ownership();
            if ownership == ImageOwnership::ExternalReady {
                imported_nodes += 1;
                continue;
            }
            owners.try_reserve(1).map_err(|_| publish_oom())?;
            owners.push(ownership);
            if ownership == ImageOwnership::SessionPrivate {
                private_cap += 1;
            } else {
                system_cap += 1;
            }
        }
        if imported_nodes != self.system_leases.len() {
            return Err(publish_error());
        }

        let mut private = Vec::new();
        private
            .try_reserve_exact(private_cap)
            .map_err(|_| publish_oom())?;
        let mut system = Vec::new();
        system
            .try_reserve_exact(system_cap)
            .map_err(|_| publish_oom())?;

        Ok(KernelLinkPreparedBatch {
            owners,
            private,
            system,
        })
    }

    /// # Safety
    ///
    /// `prepared` and `product` come from the same live link session on this
    /// publisher; the `prepare_batch` check already proved the group is unlinked.
    unsafe fn commit_batch(
        &mut self,
        prepared: Self::PreparedBatch,
        product: CommittingLinkProduct,
    ) -> Self::Receipt {
        let KernelLinkPreparedBatch {
            owners,
            mut private,
            mut system,
        } = prepared;
        let leases = product.into_leases();
        debug_assert_eq!(leases.len(), owners.len());
        for (lease, ownership) in leases.into_iter().zip(owners) {
            match ownership {
                ImageOwnership::SessionPrivate => private.push(lease),
                ImageOwnership::SystemCandidate => system.push(lease),
                // `prepare_batch` skipped imported Ready images; a lease should
                // never carry that residency here.
                ImageOwnership::ExternalReady => {
                    unreachable!("imported images carry no lease")
                }
            }
        }
        KernelLinkReceipt {
            private_allocations: private,
            system_allocations: system,
            system_leases: core::mem::take(&mut self.system_leases),
        }
    }
}

fn publish_error() -> LoadError {
    LoadError::new(LoadErrorKind::Backend, ErrorContext::None)
}

fn publish_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
}
