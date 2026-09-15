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

//! Bounded dependency graph: stable BFS closure, identity/SONAME
//! de-duplication, and a dependency-first SCC condensation.
//!
//! The graph records *structure* only: which artifact depends on which. It
//! never resolves names, reads ELF bytes, or owns an allocation. The discovery
//! driver (the session in ) feeds it resolved `ArtifactIdentity`/`SONAME`
//! facts; this module enforces identity de-duplication and the quotas
//! of , and derives the dependency-first order required by lifecycle
//! planning.

use alloc::vec::Vec;

use crate::{
    dynamic_linker::{ArtifactIdentity, DependencyName, ImageId, ImageOwnership},
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult},
    identity::SessionLimits,
};

/// One artifact admitted into the link session.
pub(crate) struct DependencyNode {
    id: ImageId,
    artifact: ArtifactIdentity,
    soname: Option<DependencyName>,
    ownership: ImageOwnership,
    discovery_index: u32,
    depth: u16,
}

impl DependencyNode {
    #[inline]
    pub(crate) const fn id(&self) -> ImageId {
        self.id
    }

    #[inline]
    pub(crate) const fn artifact(&self) -> &ArtifactIdentity {
        &self.artifact
    }

    #[inline]
    pub(crate) const fn soname(&self) -> Option<&DependencyName> {
        self.soname.as_ref()
    }

    #[inline]
    pub(crate) const fn ownership(&self) -> ImageOwnership {
        self.ownership
    }

    #[inline]
    pub(crate) const fn discovery_index(&self) -> u32 {
        self.discovery_index
    }

    #[inline]
    pub(crate) const fn depth(&self) -> u16 {
        self.depth
    }
}

/// A directed dependency edge: `requester` needs the `needed_index`-th
/// `DT_NEEDED` of its dynamic table, satisfied by `provider`.
pub struct DependencyEdge {
    requester: ImageId,
    provider: ImageId,
    needed_index: u16,
}

impl DependencyEdge {
    #[inline]
    pub const fn requester(&self) -> ImageId {
        self.requester
    }

    #[inline]
    pub const fn provider(&self) -> ImageId {
        self.provider
    }

    #[inline]
    pub const fn needed_index(&self) -> u16 {
        self.needed_index
    }
}

/// The set of artifacts and the de-duplicated dependency edges between them.
///
/// Identity and SONAME lookup is a bounded linear scan over `max_images`; this
/// avoids hidden, infallible tree-node allocations while preserving stable BFS
/// order. Every growth is charged against the session budget before it is
/// reserved, so a link can never exceed `max_images`/`max_dependency_edges`/
/// `max_dependency_depth` regardless of the resolver's catalog order.
pub(crate) struct DependencyGraph {
    nodes: Vec<DependencyNode>,
    edges: Vec<DependencyEdge>,
    limits: SessionLimits,
}

impl DependencyGraph {
    pub(crate) const fn new(limits: SessionLimits) -> Self {
        Self {
            nodes: Vec::new(),
            edges: Vec::new(),
            limits,
        }
    }

    #[inline]
    pub(crate) fn nodes(&self) -> &[DependencyNode] {
        &self.nodes
    }

    #[inline]
    pub(crate) fn edges(&self) -> &[DependencyEdge] {
        &self.edges
    }

    #[inline]
    pub(crate) fn into_edges(self) -> Vec<DependencyEdge> {
        self.edges
    }

    #[inline]
    pub(crate) fn node(&self, id: ImageId) -> Option<&DependencyNode> {
        self.nodes.get(id.get() as usize)
    }

    /// Look up an already-admitted image by its full identity, so the
    /// discovery driver can de-duplicate before allocating.
    #[inline]
    pub(crate) fn find_identity(&self, identity: &ArtifactIdentity) -> Option<ImageId> {
        self.nodes
            .iter()
            .find(|node| node.artifact() == identity)
            .map(DependencyNode::id)
    }

    /// Record an edge from `requester` to an already-admitted `provider`.
    ///
    /// This is the de-duplication fast path: the discovery driver
    /// resolved an identity already present in the graph, so no new image is
    /// loaded, but the dependency edge must still be recorded.
    #[inline]
    pub(crate) fn link_existing(
        &mut self,
        requester: ImageId,
        provider: ImageId,
        needed_index: u16,
    ) -> LoadResult<()> {
        self.record_edge(requester, provider, needed_index)
    }

    /// Admit the link root. The root is always `ImageId(0)` at depth 0. Role
    /// validation (an `ExecutableRoot` root, a `SharedObject` dependency) is
    /// the discovery driver's responsibility and happens before this call.
    pub(crate) fn insert_root(
        &mut self,
        artifact: ArtifactIdentity,
        soname: Option<DependencyName>,
        ownership: ImageOwnership,
    ) -> LoadResult<ImageId> {
        if !self.nodes.is_empty() {
            return Err(graph_error(LoadErrorKind::BadElf, ErrorContext::None));
        }
        self.limits.check_image_count(1)?;
        self.check_soname_len(soname.as_ref())?;
        let id = ImageId::new(0);
        self.record_node(id, artifact, soname, ownership, 0)?;
        Ok(id)
    }

    /// Record a resolved dependency and return its provider image id.
    ///
    /// De-duplication runs before any new node is admitted. The same
    /// `ArtifactIdentity` reuses the existing id. A repeated SONAME with a
    /// different identity produces `IdentityConflict`; the same identity with
    /// a different non-empty SONAME produces `BadElf`.
    ///
    /// An edge is always recorded, even when the provider is the root or an
    /// already-loaded dependency, so a diamond keeps both edges while loading
    /// the shared provider once.
    pub(crate) fn insert_dependency(
        &mut self,
        requester: ImageId,
        needed: &DependencyName,
        needed_index: u16,
        artifact: ArtifactIdentity,
        soname: Option<DependencyName>,
        ownership: ImageOwnership,
    ) -> LoadResult<ImageId> {
        let requester_depth = self
            .node(requester)
            .map(|node| node.depth())
            .ok_or_else(|| graph_error(LoadErrorKind::BadElf, ErrorContext::None))?;
        self.limits
            .check_dependency_name_len(needed.as_bytes().len() as u32)?;
        self.check_soname_len(soname.as_ref())?;

        let provider = if let Some(existing) = self.find_identity(&artifact) {
            // Same snapshot: reuse, but a re-declared, conflicting SONAME is
            // still malformed rather than silently ignored.
            if let (Some(declared), Some(new_soname)) = (
                self.node(existing).and_then(|node| node.soname()),
                soname.as_ref(),
            ) && declared != new_soname
            {
                return Err(dependency_error(LoadErrorKind::BadElf, requester, needed));
            }
            existing
        } else if let Some(new_soname) = soname.as_ref()
            && let Some(existing) = self.find_soname(new_soname)
        {
            // A SONAME already claimed by a different identity is a conflict.
            return Err(dependency_error(
                LoadErrorKind::IdentityConflict,
                requester,
                needed,
            ));
        } else {
            let id = ImageId::new(self.nodes.len() as u32);
            self.limits.check_image_count(self.nodes.len() as u32 + 1)?;
            let depth = requester_depth
                .checked_add(1)
                .ok_or_else(|| graph_error(LoadErrorKind::IntegerOverflow, ErrorContext::None))?;
            self.limits.check_dependency_depth(depth)?;
            self.record_node(id, artifact, soname, ownership, depth)?;
            id
        };

        self.record_edge(requester, provider, needed_index)?;
        Ok(provider)
    }

    fn record_node(
        &mut self,
        id: ImageId,
        artifact: ArtifactIdentity,
        soname: Option<DependencyName>,
        ownership: ImageOwnership,
        depth: u16,
    ) -> LoadResult<()> {
        self.nodes
            .try_reserve(1)
            .map_err(|_| graph_error(LoadErrorKind::OutOfMemory, ErrorContext::None))?;
        self.nodes.push(DependencyNode {
            id,
            artifact,
            soname,
            ownership,
            discovery_index: id.get(),
            depth,
        });
        Ok(())
    }

    fn find_soname(&self, soname: &DependencyName) -> Option<ImageId> {
        self.nodes
            .iter()
            .find(|node| node.soname() == Some(soname))
            .map(DependencyNode::id)
    }

    fn record_edge(
        &mut self,
        requester: ImageId,
        provider: ImageId,
        needed_index: u16,
    ) -> LoadResult<()> {
        self.limits
            .check_dependency_edge_count(self.edges.len() as u32 + 1)?;
        self.edges
            .try_reserve(1)
            .map_err(|_| graph_error(LoadErrorKind::OutOfMemory, ErrorContext::None))?;
        self.edges.push(DependencyEdge {
            requester,
            provider,
            needed_index,
        });
        Ok(())
    }

    fn check_soname_len(&self, soname: Option<&DependencyName>) -> LoadResult<()> {
        if let Some(soname) = soname {
            self.limits
                .check_dependency_name_len(soname.as_bytes().len() as u32)?;
        }
        Ok(())
    }

    /// Derive the dependency-first order: providers before requesters.
    ///
    /// Strongly-connected components (dependency cycles) are contracted; the
    /// condensation is walked from the root in DFS post-order so a provider SCC
    /// always precedes the SCC that needs it. Within an SCC, members are sorted
    /// by BFS discovery index. The result is stable and independent of the
    /// resolver's map/container iteration order.
    pub(crate) fn dependency_order(&self) -> LoadResult<Vec<Vec<ImageId>>> {
        let n = self.nodes.len();
        if n == 0 {
            return Ok(Vec::new());
        }

        let mut out_degrees = zero_counts(n)?;
        let mut in_degrees = zero_counts(n)?;
        for edge in &self.edges {
            increment_count(&mut out_degrees[edge.requester.get() as usize])?;
            increment_count(&mut in_degrees[edge.provider.get() as usize])?;
        }
        let mut adj = adjacency_with_capacities(&out_degrees)?;
        let mut adj_t = adjacency_with_capacities(&in_degrees)?;
        for edge in &self.edges {
            adj[edge.requester.get() as usize].push(edge.provider.get());
            adj_t[edge.provider.get() as usize].push(edge.requester.get());
        }
        for neighbors in adj.iter_mut() {
            neighbors.sort_unstable();
        }
        for neighbors in adj_t.iter_mut() {
            neighbors.sort_unstable();
        }

        let (scc_count, scc_of) = compute_sccs(&adj, &adj_t)?;

        let mut cond_degrees = zero_counts(scc_count)?;
        for edge in &self.edges {
            let u = scc_of[edge.requester.get() as usize];
            let v = scc_of[edge.provider.get() as usize];
            if u != v {
                increment_count(&mut cond_degrees[u as usize])?;
            }
        }
        let mut cond = adjacency_with_capacities(&cond_degrees)?;
        for edge in &self.edges {
            let u = scc_of[edge.requester.get() as usize];
            let v = scc_of[edge.provider.get() as usize];
            if u != v {
                cond[u as usize].push(v);
            }
        }
        for neighbors in cond.iter_mut() {
            neighbors.sort_unstable();
            neighbors.dedup();
        }

        let finish = dfs_post_order(&cond, scc_of[0])?;

        let mut member_counts = zero_counts(scc_count)?;
        for &scc in &scc_of {
            increment_count(&mut member_counts[scc as usize])?;
        }
        let mut members = image_groups_with_capacities(&member_counts)?;
        for (node, &scc) in self.nodes.iter().zip(scc_of.iter()) {
            members[scc as usize].push(node.id);
        }
        for member in members.iter_mut() {
            member.sort_unstable();
        }

        let mut groups = Vec::new();
        groups
            .try_reserve_exact(scc_count)
            .map_err(|_| graph_oom())?;
        for scc in finish {
            groups.push(core::mem::take(&mut members[scc as usize]));
        }
        Ok(groups)
    }
}

fn zero_counts(len: usize) -> LoadResult<Vec<usize>> {
    let mut counts = Vec::new();
    counts.try_reserve_exact(len).map_err(|_| graph_oom())?;
    counts.resize(len, 0);
    Ok(counts)
}

fn increment_count(count: &mut usize) -> LoadResult<()> {
    *count = count.checked_add(1).ok_or_else(graph_oom)?;
    Ok(())
}

fn adjacency_with_capacities(counts: &[usize]) -> LoadResult<Vec<Vec<u32>>> {
    let mut adjacency = Vec::new();
    adjacency
        .try_reserve_exact(counts.len())
        .map_err(|_| graph_oom())?;
    for &count in counts {
        let mut neighbors = Vec::new();
        neighbors
            .try_reserve_exact(count)
            .map_err(|_| graph_oom())?;
        adjacency.push(neighbors);
    }
    Ok(adjacency)
}

fn image_groups_with_capacities(counts: &[usize]) -> LoadResult<Vec<Vec<ImageId>>> {
    let mut groups = Vec::new();
    groups
        .try_reserve_exact(counts.len())
        .map_err(|_| graph_oom())?;
    for &count in counts {
        let mut members = Vec::new();
        members.try_reserve_exact(count).map_err(|_| graph_oom())?;
        groups.push(members);
    }
    Ok(groups)
}

/// FIFO of pending dependency resolutions, bounded by the session edge budget.
///
/// The discovery driver pushes one item per `DT_NEEDED` in encounter order and
/// pops in the same order, giving the stable BFS of .
pub(crate) struct DiscoveryQueue {
    pending: alloc::collections::VecDeque<DiscoveryItem>,
    limits: SessionLimits,
}

pub(crate) struct DiscoveryItem {
    requester: ImageId,
    needed_index: u16,
}

impl DiscoveryItem {
    pub(crate) const fn new(requester: ImageId, needed_index: u16) -> Self {
        Self {
            requester,
            needed_index,
        }
    }

    pub const fn requester(&self) -> ImageId {
        self.requester
    }

    pub const fn needed_index(&self) -> u16 {
        self.needed_index
    }
}

impl DiscoveryQueue {
    pub(crate) const fn new(limits: SessionLimits) -> Self {
        Self {
            pending: alloc::collections::VecDeque::new(),
            limits,
        }
    }

    pub(crate) fn push(&mut self, item: DiscoveryItem) -> LoadResult<()> {
        self.limits
            .check_dependency_edge_count(self.pending.len() as u32 + 1)?;
        self.pending
            .try_reserve(1)
            .map_err(|_| graph_error(LoadErrorKind::OutOfMemory, ErrorContext::None))?;
        self.pending.push_back(item);
        Ok(())
    }

    pub(crate) fn pop(&mut self) -> Option<DiscoveryItem> {
        self.pending.pop_front()
    }
}

/// Tarjan-free Kosaraju SCC over an out-adjacency, returning the component
/// count and a per-node component id. The explicit stacks keep depth bounded
/// independently of the graph, and the input adjacency is already sorted for
/// determinism.
fn compute_sccs(adj: &[Vec<u32>], adj_t: &[Vec<u32>]) -> LoadResult<(usize, Vec<u32>)> {
    let n = adj.len();

    let mut visited: Vec<bool> = Vec::new();
    visited.try_reserve_exact(n).map_err(|_| graph_oom())?;
    visited.resize(n, false);

    let mut finish: Vec<u32> = Vec::new();
    finish.try_reserve_exact(n).map_err(|_| graph_oom())?;

    let mut stack: Vec<(u32, usize)> = Vec::new();
    stack.try_reserve_exact(n).map_err(|_| graph_oom())?;

    for start in 0..n {
        if visited[start] {
            continue;
        }
        stack.clear();
        stack.push((start as u32, 0));
        visited[start] = true;
        while let Some((node, next)) = stack.last_mut() {
            if *next < adj[*node as usize].len() {
                let child = adj[*node as usize][*next];
                *next += 1;
                if !visited[child as usize] {
                    visited[child as usize] = true;
                    stack.push((child, 0));
                }
            } else {
                finish.push(*node);
                stack.pop();
            }
        }
    }

    let mut comp: Vec<u32> = Vec::new();
    comp.try_reserve_exact(n).map_err(|_| graph_oom())?;
    comp.resize(n, u32::MAX);

    let mut count = 0usize;
    let mut stack: Vec<u32> = Vec::new();
    stack.try_reserve_exact(n).map_err(|_| graph_oom())?;

    for &node in finish.iter().rev() {
        if comp[node as usize] != u32::MAX {
            continue;
        }
        stack.clear();
        stack.push(node);
        comp[node as usize] = count as u32;
        while let Some(u) = stack.pop() {
            for &v in &adj_t[u as usize] {
                if comp[v as usize] == u32::MAX {
                    comp[v as usize] = count as u32;
                    stack.push(v);
                }
            }
        }
        count += 1;
    }

    Ok((count, comp))
}

/// Iterative DFS post-order over a condensation graph. The root component is
/// walked first; any unreachable component (which a valid BFS closure cannot
/// produce) is appended in ascending id order so the output stays total and
/// deterministic. Post-order places providers before their requesters.
fn dfs_post_order(adj: &[Vec<u32>], root: u32) -> LoadResult<Vec<u32>> {
    let n = adj.len();

    let mut visited: Vec<bool> = Vec::new();
    visited.try_reserve_exact(n).map_err(|_| graph_oom())?;
    visited.resize(n, false);

    let mut finish: Vec<u32> = Vec::new();
    finish.try_reserve_exact(n).map_err(|_| graph_oom())?;

    let mut stack: Vec<(u32, usize)> = Vec::new();
    stack.try_reserve_exact(n).map_err(|_| graph_oom())?;

    // Deterministic start sequence: root first, then any stragglers.
    let mut starts: Vec<u32> = Vec::new();
    starts.try_reserve_exact(n).map_err(|_| graph_oom())?;
    starts.push(root);
    for id in 0..n as u32 {
        if id != root {
            starts.push(id);
        }
    }

    for start in starts {
        if visited[start as usize] {
            continue;
        }
        stack.clear();
        stack.push((start, 0));
        visited[start as usize] = true;
        while let Some((node, next)) = stack.last_mut() {
            if *next < adj[*node as usize].len() {
                let child = adj[*node as usize][*next];
                *next += 1;
                if !visited[child as usize] {
                    visited[child as usize] = true;
                    stack.push((child, 0));
                }
            } else {
                finish.push(*node);
                stack.pop();
            }
        }
    }

    Ok(finish)
}

fn graph_error(kind: LoadErrorKind, context: ErrorContext) -> LoadError {
    LoadError::new(kind, context)
}

fn dependency_error(kind: LoadErrorKind, requester: ImageId, needed: &DependencyName) -> LoadError {
    LoadError::new(
        kind,
        ErrorContext::Dependency {
            requester: requester.get(),
            needed: needed.as_bytes().into(),
        },
    )
}

fn graph_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
}
