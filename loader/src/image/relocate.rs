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
    cache::CodeCache,
    dynamic_linker::RuntimeImageMetadata,
    elf::LoadSegmentInfo,
    error::{ErrorContext, LoadError, LoadErrorKind, LoadResult, LoadStage},
    identity::LoadRequest,
    image::{cache::CachedImage, inspect::StackKind, map::LoadedRegion},
    memory::{ImageLoadTransaction, ImageMemory},
};

#[must_use = "dropping a relocated image aborts its allocation"]
pub(crate) struct RelocatedImage<M: ImageMemory> {
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
}

impl<M: ImageMemory> RelocatedImage<M> {
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
        }
    }

    pub fn cache<C: CodeCache>(self, mut cache: C) -> LoadResult<CachedImage<M>> {
        let mut executable_ranges = Vec::new();
        let executable_count = self
            .load_segments
            .iter()
            .filter(|segment| {
                segment
                    .permissions()
                    .contains(crate::MemoryPermissions::EXECUTE)
                    && segment.memory_size() != 0
            })
            .count();
        executable_ranges
            .try_reserve_exact(executable_count)
            .map_err(|_| cache_oom().at_stage(LoadStage::Cache))?;

        if self.load_segments.len() != self.regions.len() {
            return Err(cache_backend_error(None).at_stage(LoadStage::Cache));
        }
        for (segment, region) in self.load_segments.iter().zip(self.regions.iter()) {
            let expected_vaddr = TargetRange::new(segment.vaddr(), segment.memory_size());
            let expected_runtime = TargetRange::new(
                self.load_bias
                    .checked_add(segment.vaddr().get())
                    .map_err(|error| error.at_stage(LoadStage::Cache))?,
                segment.memory_size(),
            );
            if region.vaddr_range() != expected_vaddr || region.runtime_range() != expected_runtime
            {
                return Err(
                    cache_backend_error(Some(region.runtime_range())).at_stage(LoadStage::Cache)
                );
            }
            if segment
                .permissions()
                .contains(crate::MemoryPermissions::EXECUTE)
                && !region.runtime_range().is_empty()
            {
                region
                    .runtime_range()
                    .end()
                    .map_err(|error| error.at_stage(LoadStage::Cache))?;
                executable_ranges.push(region.runtime_range());
            }
        }

        let requirements = cache.requirements();
        let prepared = cache
            .prepare(&executable_ranges)
            .map_err(|error| error.at_stage(LoadStage::Cache))?;
        requirements
            .validate_prepared(&executable_ranges, &prepared)
            .map_err(|error| error.at_stage(LoadStage::Cache))?;
        let prepared_scope = prepared.scope();
        let prepared_maintenance = prepared.maintenance();
        let cache_sync = cache
            .synchronize(prepared)
            .map_err(|error| error.at_stage(LoadStage::Cache))?;
        cache_sync
            .validate_completion(&executable_ranges, prepared_scope, prepared_maintenance)
            .map_err(|error| error.at_stage(LoadStage::Cache))?;

        Ok(CachedImage::new(
            self.transaction,
            self.load_bias,
            self.request,
            self.entry_vaddr,
            self.canonical_entry_vaddr,
            self.load_segments,
            self.regions,
            self.metadata,
            self.relro,
            self.stack,
            cache_sync,
        ))
    }
}

fn cache_oom() -> LoadError {
    LoadError::new(LoadErrorKind::OutOfMemory, ErrorContext::None)
}

fn cache_backend_error(range: Option<TargetRange>) -> LoadError {
    let context = match range {
        Some(range) => ErrorContext::TargetRange {
            start: range.start(),
            len: range.len(),
            align: 0,
        },
        None => ErrorContext::None,
    };
    LoadError::new(LoadErrorKind::Backend, context)
}
