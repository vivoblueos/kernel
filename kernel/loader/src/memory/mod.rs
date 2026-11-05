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

//! Image memory preparation and owning mappings.
//!
//! Submit one complete `ImageLayout` to `ImageMemory::prepare_image`. The
//! returned `ImageMapping` owns its backing or the exclusive use of borrowed
//! storage. Moving it retains that storage; dropping it releases the resources.

pub(crate) mod address;
mod flat_memory_mapper;
mod layout;

use crate::LoadResult;

pub use address::{TargetAddress, TargetRange};
pub use flat_memory_mapper::{FlatImageAllocation, MemoryMapper, MemoryRegion};
pub use layout::{AllocationOffset, ImageLayout, MemoryPermissions, Placement, SegmentLayout};

/// Prepares image storage and transfers its lifetime to the returned mapping.
///
/// The allocation type is backend-specific: it may own heap storage, page
/// mappings, or an exclusive claim on a fixed region. It must retain everything
/// needed for access and cleanup independently of this factory's lifetime.
pub trait ImageMemory {
    type Allocation: ImageMapping;

    /// Prepare the complete logical reservation and every listed segment.
    ///
    /// All offsets share one target execution base. Physical backing may be
    /// scattered and gaps need not be backed. Each listed segment must support
    /// loader reads and writes until final protection is applied later.
    /// Successful reads must never expose uninitialized bytes.
    ///
    /// Borrowed storage must be exclusively available for this mapping. Its
    /// previous contents need not be preserved, even when preparation fails.
    /// Prepare it for a fresh load before returning success; a caller must not
    /// overwrite a live image or rely on bytes left by a previous attempt.
    ///
    /// On error, release any resources acquired by this call. On success, the
    /// returned allocation is solely responsible for cleanup through `Drop`.
    fn prepare_image(&mut self, layout: &ImageLayout) -> LoadResult<Self::Allocation>;
}

/// An owning image allocation with backend-mediated byte access.
///
/// The base is a target execution VA, not necessarily a host pointer. Every
/// access must check overflow, allocation bounds and the backing required for
/// that access. An empty access at the end is permitted; an offset beyond the
/// end is not. Failed writes or zeroing may have partially changed contents.
///
/// Implementations must retain all backing and exclusive-use claims while
/// alive. `Drop` releases owned resources or ends the borrow, without allocating,
/// failing or panicking. It does not restore previous contents or distinguish
/// loading failure from normal unload. The image owner must ensure execution
/// and other users have ended before dropping a published mapping.
///
/// Resource-owning implementations should carry type-level `#[must_use]`.
pub trait ImageMapping {
    fn base(&self) -> TargetAddress;
    fn len(&self) -> u64;
    fn align(&self) -> u64;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn read(&self, offset: AllocationOffset, dst: &mut [u8]) -> LoadResult<()>;
    fn write(&mut self, offset: AllocationOffset, data: &[u8]) -> LoadResult<()>;
    fn zero(&mut self, offset: AllocationOffset, len: u64) -> LoadResult<()>;
}

impl<M: ImageMemory + ?Sized> ImageMemory for &mut M {
    type Allocation = M::Allocation;

    fn prepare_image(&mut self, layout: &ImageLayout) -> LoadResult<Self::Allocation> {
        (**self).prepare_image(layout)
    }
}
