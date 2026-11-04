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

//! Read-only stages of single-image ELF loading.
//! Follow `ImageLoader::admit`, `AdmittedImage::inspect`, then
//! `InspectedImage::plan`. These stages never allocate or write image backing.

mod admit;
mod image_loader;
mod inspect;
mod plan;

pub(crate) use image_loader::ImageLoader;
pub(crate) use plan::PlannedImage;
