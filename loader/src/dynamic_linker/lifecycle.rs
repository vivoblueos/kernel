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

//! Lifecycle plan generation after relocation.
//!
//! After relocation, the init/fini array words are fixed into their final
//! function addresses. This module reads them back through the session memory
//! backend, validates each non-sentinel canonical address against its owner's
//! executable region (and the Thumb bit on ARM), and produces the dependency-
//! first [`InitPlan`] plus its exact reverse [`FiniPlan`]. This module only
//! *generates* the plan; nothing here turns a target address into a host
//! function pointer or calls a constructor.

use alloc::vec::Vec;

use crate::{
    address::{TargetAddress, TargetRange},
    dynamic_linker::{
        graph::DependencyGraph, relocate::locate_region_offset, ImageId, ImageLifecycleMetadata,
    },
    elf::LoadSegmentInfo,
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult, LoadStage},
    identity::LoadProfile,
    image::LoadedRegion,
    memory::{ImageMemory, SessionAllocation},
    relocation::{TargetWord, WordWidth},
    MemoryPermissions,
};

/// One validated constructor/destructor target: the owning image plus its
/// runtime function address. The owner (not a bare pointer) is what ties the
/// entry back to the image allocation that must outlive it.
#[derive(Clone, Copy, Debug)]
pub struct LifecycleEntry {
    owner: ImageId,
    function: TargetAddress,
}

impl LifecycleEntry {
    #[inline]
    pub(crate) const fn new(owner: ImageId, function: TargetAddress) -> Self {
        Self { owner, function }
    }

    #[inline]
    pub const fn owner(&self) -> ImageId {
        self.owner
    }

    #[inline]
    pub const fn function(&self) -> TargetAddress {
        self.function
    }
}

/// The dependency-first constructor order, ready to be executed by the
/// runtime in.
#[derive(Clone, Debug)]
pub struct InitPlan(Vec<LifecycleEntry>);

impl InitPlan {
    #[inline]
    pub fn iter(&self) -> core::slice::Iter<'_, LifecycleEntry> {
        self.0.iter()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// The destructor order — the exact reverse of the init plan.
#[derive(Clone, Debug, Default)]
pub struct FiniPlan(Vec<LifecycleEntry>);

impl FiniPlan {
    #[inline]
    pub fn iter(&self) -> core::slice::Iter<'_, LifecycleEntry> {
        self.0.iter()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The sub-plan for one owning image, preserving the original relative
    /// order of that image's entries.
    ///
    /// The registry retains a per-SONAME `FiniPlan` at `mark_ready`, but a
    /// `LinkProduct` only exposes the combined plan. The publisher filters the
    /// combined plan here — the relative order of a single image's
    /// `DT_FINI_ARRAY` (reverse) then `DT_FINI` is unchanged by dropping the
    /// other images' entries — so the reaper runs exactly one image's
    /// destructors. An image with no destructors yields an empty plan.
    pub fn for_image(&self, owner: ImageId) -> LoadResult<FiniPlan> {
        let mut entries = Vec::new();
        // The plan is bounded by the session's total lifecycle entries; the
        // filtered view can only shrink, so reserving the full count is a
        // safe upper bound and never exceeds the already-charged metadata.
        entries
            .try_reserve(self.0.len())
            .map_err(|_| lifecycle_oom())?;
        for entry in &self.0 {
            if entry.owner() == owner {
                entries.push(*entry);
            }
        }
        Ok(FiniPlan(entries))
    }
}

/// One image's destructor plan: the registry retains one per
/// new system candidate, so a system image's fini runs only when the
/// registry reaps the instance — never at an application exit.
#[derive(Clone, Debug)]
pub struct ImageFiniPlan {
    owner: ImageId,
    plan: FiniPlan,
}

impl ImageFiniPlan {
    #[inline]
    pub(crate) fn new(owner: ImageId, plan: FiniPlan) -> Self {
        Self { owner, plan }
    }

    #[inline]
    pub const fn owner(&self) -> ImageId {
        self.owner
    }

    #[inline]
    pub fn plan(&self) -> &FiniPlan {
        &self.plan
    }
}

/// The session's lifecycle, partitioned by ownership.
///
/// `startup` contains every constructor this session runs: the root's
/// `DT_PREINIT_ARRAY`, then each loaded private or new system image in
/// dependency-first SCC order. Imported ready images never appear because
/// their generation has already been initialized.
///
/// `group_fini` contains only root and private destructors in the exact reverse
/// of the startup order. A system DSO's fini is never executed at application
/// exit. `system_fini` contains one plan per new system candidate for the
/// registry to retain until the instance quiesces. `sccs` is the frozen SCC
/// snapshot in dependency-first order and stable discovery order.
#[derive(Clone, Debug)]
pub struct LifecyclePlans {
    startup: InitPlan,
    group_fini: FiniPlan,
    system_fini: Vec<ImageFiniPlan>,
    sccs: Vec<Vec<ImageId>>,
}

impl LifecyclePlans {
    #[inline]
    pub fn startup(&self) -> &InitPlan {
        &self.startup
    }

    #[inline]
    pub fn group_fini(&self) -> &FiniPlan {
        &self.group_fini
    }

    #[inline]
    pub fn system_fini(&self) -> &[ImageFiniPlan] {
        &self.system_fini
    }

    /// The frozen SCC snapshot: groups in dependency-first order,
    /// each in stable discovery order.
    #[inline]
    pub fn sccs(&self) -> &[Vec<ImageId>] {
        &self.sccs
    }
}

/// Per-image inputs to plan generation, borrowed from the session's relocated
/// images.
pub(crate) struct LifecycleImage<'a> {
    image_id: ImageId,
    allocation: SessionAllocation,
    regions: &'a [LoadedRegion],
    load_segments: &'a [LoadSegmentInfo],
    lifecycle: &'a ImageLifecycleMetadata,
    load_bias: TargetAddress,
}

impl<'a> LifecycleImage<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        image_id: ImageId,
        allocation: SessionAllocation,
        regions: &'a [LoadedRegion],
        load_segments: &'a [LoadSegmentInfo],
        lifecycle: &'a ImageLifecycleMetadata,
        load_bias: TargetAddress,
    ) -> Self {
        Self {
            image_id,
            allocation,
            regions,
            load_segments,
            lifecycle,
            load_bias,
        }
    }

    #[inline]
    pub(crate) const fn image_id(&self) -> ImageId {
        self.image_id
    }
}

/// Immutable decode geometry carried through every per-entry step.
struct Decode {
    target_word: TargetWord,
    thumb: bool,
    min_instruction: u64,
}

/// Build the init and fini plans from a closed dependency graph and the
/// relocated images.
///
/// Init order: root `DT_PREINIT_ARRAY` (the only image that may carry one),
/// then every image in SCC dependency-first order, each emitting `DT_INIT`
/// before its `DT_INIT_ARRAY` in forward order. Fini is the exact reverse
/// image order with, per image, `DT_FINI_ARRAY` in reverse then `DT_FINI`.
pub(crate) fn build<M: ImageMemory + ?Sized>(
    graph: &DependencyGraph,
    images: &[LifecycleImage<'_>],
    profile: &LoadProfile,
    memory: &M,
) -> LoadResult<LifecyclePlans> {
    let width = WordWidth::for_elf_class(profile.class());
    let decode = Decode {
        target_word: TargetWord::new(width, profile.endian()),
        thumb: profile.entry_mode().is_thumb(),
        min_instruction: u64::from(profile.entry_mode().minimum_instruction_size()),
    };
    let ordered = ordered_images(graph)?;

    let mut init = Vec::new();

    // The root's preinit array precedes all DSO init; a DSO carrying a preinit
    // array is unsupported in this profile.
    for image in images {
        if image.image_id.get() == 0 {
            read_array(
                image,
                image.lifecycle.preinit_array(),
                &decode,
                memory,
                false,
                &mut init,
            )?;
        } else if image.lifecycle.preinit_array().is_some() {
            return Err(lifecycle_error(LoadErrorKind::UnsupportedByProfile));
        }
    }

    for &image_id in &ordered {
        // An imported Ready image contributes no constructor (it was already
        // initialized by the link that first published it), so its
        // image id has no lifecycle entry here and is skipped.
        let Some(image) = image_for(images, image_id) else {
            continue;
        };
        emit_direct(image, image.lifecycle.init(), &decode, &mut init)?;
        read_array(
            image,
            image.lifecycle.init_array(),
            &decode,
            memory,
            false,
            &mut init,
        )?;
    }

    let mut fini = Vec::new();
    for &image_id in ordered.iter().rev() {
        let Some(image) = image_for(images, image_id) else {
            continue;
        };
        read_array(
            image,
            image.lifecycle.fini_array(),
            &decode,
            memory,
            true,
            &mut fini,
        )?;
        emit_direct(image, image.lifecycle.fini(), &decode, &mut fini)?;
    }

    // partition: split the combined fini by ownership so an
    // application exit runs only root/private destructors and the registry
    // retains one plan per new system candidate. Partitioning preserves the
    // relative order of each image's own entries.
    let mut group_fini = Vec::new();
    let mut system_fini = Vec::new();
    group_fini
        .try_reserve_exact(fini.len())
        .map_err(|_| lifecycle_oom())?;
    system_fini
        .try_reserve_exact(fini.len())
        .map_err(|_| lifecycle_oom())?;
    for entry in &fini {
        let ownership = graph
            .node(entry.owner())
            .ok_or_else(|| lifecycle_error(LoadErrorKind::BadElf))?
            .ownership();
        match ownership {
            crate::dynamic_linker::ImageOwnership::SessionPrivate => {
                group_fini.push(*entry);
            }
            crate::dynamic_linker::ImageOwnership::SystemCandidate => {
                match system_fini
                    .iter_mut()
                    .find(|plan: &&mut (ImageId, Vec<LifecycleEntry>)| plan.0 == entry.owner())
                {
                    Some((_, entries)) => entries.push(*entry),
                    None => system_fini.push((entry.owner(), alloc::vec![*entry])),
                }
            }
            crate::dynamic_linker::ImageOwnership::ExternalReady => {
                // Imported images carry no fini entries by construction.
            }
        }
    }
    let mut system_fini = system_fini
        .into_iter()
        .map(|(owner, entries)| ImageFiniPlan::new(owner, FiniPlan(entries)))
        .collect::<Vec<_>>();

    // The frozen SCC snapshot: the exact groups and in-group order the
    // plans above were generated from.
    let sccs = graph.dependency_order()?;

    Ok(LifecyclePlans {
        startup: InitPlan(init),
        group_fini: FiniPlan(group_fini),
        system_fini,
        sccs,
    })
}

/// Flatten the SCC groups into one dependency-first image order.
fn ordered_images(graph: &DependencyGraph) -> LoadResult<Vec<ImageId>> {
    let groups = graph.dependency_order()?;
    let total = groups.iter().map(|group| group.len()).sum();
    let mut ordered = Vec::new();
    ordered
        .try_reserve_exact(total)
        .map_err(|_| lifecycle_oom())?;
    for group in groups.iter() {
        ordered.extend_from_slice(group);
    }
    Ok(ordered)
}

/// Emit a direct `DT_INIT`/`DT_FINI` target. The stored value is a link-time
/// vaddr, so the load bias is applied to form the runtime address.
fn emit_direct(
    image: &LifecycleImage<'_>,
    direct: Option<TargetAddress>,
    decode: &Decode,
    plan: &mut Vec<LifecycleEntry>,
) -> LoadResult<()> {
    let Some(vaddr) = direct else {
        return Ok(());
    };
    let runtime = image
        .load_bias
        .checked_add(vaddr.get())
        .map_err(|_| lifecycle_error(LoadErrorKind::IntegerOverflow))?;
    validate_function(decode, image, runtime)?;
    push_entry(plan, image.image_id, runtime)
}

/// Read an init/fini array's post-relocation words, skipping the null
/// sentinel, and validate each remaining canonical address.
#[allow(clippy::too_many_arguments)]
fn read_array<M: ImageMemory + ?Sized>(
    image: &LifecycleImage<'_>,
    range: Option<TargetRange>,
    decode: &Decode,
    memory: &M,
    reverse: bool,
    plan: &mut Vec<LifecycleEntry>,
) -> LoadResult<()> {
    let Some(range) = range else {
        return Ok(());
    };
    let allocation = image.allocation.allocation();
    let width = decode.target_word.width();
    let count = range.len() / width.bytes();
    for slot in 0..count {
        let index = if reverse { count - 1 - slot } else { slot };
        let delta = index
            .checked_mul(width.bytes())
            .ok_or_else(|| lifecycle_error(LoadErrorKind::IntegerOverflow))?;
        let vaddr = range
            .start()
            .checked_add(delta)
            .map_err(|_| lifecycle_error(LoadErrorKind::IntegerOverflow))?;
        let offset = locate_region_offset(image.regions, vaddr, width.bytes())
            .map_err(|error| error.at_stage(LoadStage::LinkSeal))?;
        let value = decode
            .target_word
            .read(memory, &allocation, offset)
            .map_err(|error| error.at_stage(LoadStage::LinkSeal))?;
        if value == 0 || value == width.maximum() {
            continue;
        }
        let function = TargetAddress::new(value);
        validate_function(decode, image, function)?;
        push_entry(plan, image.image_id, function)?;
    }
    Ok(())
}

/// A function target must have its Thumb bit set (ARM) and its canonical
/// address must span at least one whole instruction inside an executable
/// segment owned by the image.
fn validate_function(
    decode: &Decode,
    image: &LifecycleImage<'_>,
    function: TargetAddress,
) -> LoadResult<()> {
    let canonical = if decode.thumb {
        TargetAddress::new(function.get() & !1)
    } else {
        function
    };
    if decode.thumb && function.get() & 1 == 0 {
        return Err(function_error(function));
    }
    if image.load_segments.len() != image.regions.len() {
        return Err(lifecycle_error(LoadErrorKind::BadElf));
    }
    let ok = image
        .load_segments
        .iter()
        .zip(image.regions.iter())
        .any(|(segment, region)| {
            segment.permissions().contains(MemoryPermissions::EXECUTE)
                && region
                    .runtime_range()
                    .contains_span(canonical, decode.min_instruction)
        });
    if ok {
        Ok(())
    } else {
        Err(function_error(function))
    }
}

fn push_entry(
    plan: &mut Vec<LifecycleEntry>,
    owner: ImageId,
    function: TargetAddress,
) -> LoadResult<()> {
    plan.try_reserve(1).map_err(|_| lifecycle_oom())?;
    plan.push(LifecycleEntry::new(owner, function));
    Ok(())
}

fn image_for<'a, 'b>(
    images: &'a [LifecycleImage<'b>],
    id: ImageId,
) -> Option<&'a LifecycleImage<'b>> {
    images.iter().find(|image| image.image_id() == id)
}

fn function_error(function: TargetAddress) -> LoadError {
    LoadError::new(
        LoadErrorKind::BadElf,
        ErrorContext::TargetRange {
            start: function,
            len: 0,
            align: 0,
        },
    )
    .at_stage(LoadStage::LinkSeal)
}

fn lifecycle_error(kind: LoadErrorKind) -> LoadError {
    LoadError::new(kind, ErrorContext::None).at_stage(LoadStage::LinkSeal)
}

fn lifecycle_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None).at_stage(LoadStage::LinkSeal)
}
