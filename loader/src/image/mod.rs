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

mod admit;
mod allocate;
mod cache;
mod decode;
mod features;
mod image_loader;
mod inspect;
mod map;
mod plan;
mod relocate;
pub mod scan;
mod seal;

pub(crate) use decode::{
    absorb_into_session, RelocationAddend, RelocationRecord, RelocationTableKind,
};
pub(crate) use features::DynamicFeatureSummary;
pub(crate) use image_loader::{read_u16, read_u32, read_u64, ImageLoader};
pub(crate) use inspect::StackKind;
pub(crate) use map::LoadedRegion;
pub use scan::{scan_artifact, ScannedArtifact};
pub use seal::{
    AppliedProtectionSet, PreparedProtectionPlan, ProtectionBatch, ProtectionCapabilities,
    ProtectionLevel, ProtectionRecord, SealPlan, SealRange, SealedState,
};
