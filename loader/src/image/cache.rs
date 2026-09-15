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
    address::{TargetAddress, TargetRange},
    cache::CacheSyncOutcome,
    dynamic_linker::RuntimeImageMetadata,
    elf::LoadSegmentInfo,
    error::{LoadResult, LoadStage},
    identity::LoadRequest,
    image::{
        inspect::StackKind,
        map::LoadedRegion,
        seal::{
            AppliedProtectionSet, PreparedProtectionPlan, ProtectionBatch, SealPlan, SealedImage,
        },
    },
    memory::{ImageLoadTransaction, ImageMemory, ImageProtectionMemory},
};

#[must_use = "dropping a cache-synchronized image aborts its allocation"]
pub(crate) struct CachedImage<M: ImageMemory> {
    transaction: ImageLoadTransaction<M>,
    load_bias: TargetAddress,
    request: LoadRequest,
    entry_vaddr: TargetAddress,
    canonical_entry_vaddr: TargetAddress,
    load_segments: Vec<LoadSegmentInfo>,
    regions: Vec<LoadedRegion>,
    metadata: RuntimeImageMetadata,
    relro: Option<TargetRange>,
    stack: StackKind,
    cache_sync: CacheSyncOutcome,
}

impl<M: ImageMemory> CachedImage<M> {
    #[inline]
    pub fn new(
        transaction: ImageLoadTransaction<M>,
        load_bias: TargetAddress,
        request: LoadRequest,
        entry_vaddr: TargetAddress,
        canonical_entry_vaddr: TargetAddress,
        load_segments: Vec<LoadSegmentInfo>,
        regions: Vec<LoadedRegion>,
        metadata: RuntimeImageMetadata,
        relro: Option<TargetRange>,
        stack: StackKind,
        cache_sync: CacheSyncOutcome,
    ) -> Self {
        Self {
            transaction,
            load_bias,
            request,
            entry_vaddr,
            canonical_entry_vaddr,
            load_segments,
            regions,
            metadata,
            relro,
            stack,
            cache_sync,
        }
    }

    pub fn seal(mut self) -> LoadResult<SealedImage<M>>
    where
        M: ImageProtectionMemory,
    {
        let allocation = *self.transaction.allocation();
        let seal_plan = SealPlan::build(
            &allocation,
            self.load_bias,
            self.request.profile().class(),
            &self.load_segments,
            &self.regions,
            self.relro,
            &self.stack,
            self.metadata.relocations().records(),
        )
        .map_err(|error| error.at_stage(LoadStage::Seal))?;
        let prepared = PreparedProtectionPlan::prepare(&self.transaction, &seal_plan)
            .map_err(|error| error.at_stage(LoadStage::Seal))?;
        let mut protection_records = prepared.into_ranges();
        self.transaction
            .apply_protection(ProtectionBatch::new(&mut protection_records))
            .map_err(|error| error.at_stage(LoadStage::Seal))?;
        let protections = AppliedProtectionSet::new(protection_records);

        let sealed = crate::image::SealedState::new(
            self.load_bias,
            self.entry_vaddr,
            self.canonical_entry_vaddr,
            self.cache_sync,
            seal_plan,
            protections,
        );
        Ok(SealedImage::new(self.transaction, sealed))
    }
}
