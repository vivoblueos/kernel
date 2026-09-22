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
#![allow(clippy::drop_non_drop)]
#![feature(box_as_ptr)]
#![feature(box_into_inner)]
#![feature(box_vec_non_null)]
#![feature(c_size_t)]
#![feature(const_trait_impl)]
#![feature(core_intrinsics)]
#![feature(linkage)]
#![feature(negative_impls)]
#![feature(pointer_is_aligned_to)]
#![feature(ptr_as_uninit)]
#![feature(slice_ptr_get)]
// Features below are stable in modern toolchains (version noted); only
// declare them on old toolchains via `compatible_old_toolchain` so the
// stable_features lint (deny via -D warnings) doesn't fire on new ones.
#![cfg_attr(compatible_old_toolchain, feature(let_chains))] // 1.88
#![cfg_attr(compatible_old_toolchain, feature(non_null_from_ref))] // 1.89
#![cfg_attr(compatible_old_toolchain, feature(slice_as_chunks))] // 1.88
#![cfg_attr(compatible_old_toolchain, feature(strict_provenance_atomic_ptr))] // 1.91

pub mod intrusive;
pub mod lifetime;
pub mod list;
pub mod rbtree;
pub mod ringbuffer;
pub mod spinarc;
pub mod storage;
pub mod string;
pub mod tinyarc;
pub use tinyarc::sorted_list;
pub mod iheap;
pub mod nolock;
pub mod tinyrwlock;
