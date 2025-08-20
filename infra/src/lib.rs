// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

#![cfg_attr(not(test), no_std)]
#![cfg_attr(test, feature(test))]
#![allow(internal_features)]
#![feature(box_as_ptr)]
#![feature(box_into_inner)]
#![feature(box_vec_non_null)]
#![feature(c_size_t)]
#![feature(const_trait_impl)]
#![feature(core_intrinsics)]
#![feature(linkage)]
#![feature(negative_impls)]
#![feature(non_null_from_ref)]
#![feature(pointer_is_aligned_to)]
#![feature(ptr_as_uninit)]
#![feature(slice_as_chunks)]
#![feature(slice_ptr_get)]
#![feature(strict_provenance_atomic_ptr)]

pub mod intrusive;
pub mod list;
pub mod ringbuffer;
pub mod spinarc;
pub mod string;
pub mod tinyarc;
pub mod tinyrwlock;
