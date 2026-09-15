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

//! Dynamic application loading: platform adapters that bind the loader's
//! neutral contracts (`ElfReader`, `ArtifactResolver`, `ImageMemory`, …) to
//! the kernel's VFS, memory and cache services.
//!
//! A launch freezes an [`namespace::ApplicationNamespace`], then
//! [`planner::NamespaceLoadPlanner`] scans the actual VFS ELF closure and
//! resolves each dependency to a concrete path. The resolver atomically
//! acquires that plan's system-library keys before the linker maps anything;
//! private images stay group-owned while system images are published through
//! [`registry::SystemDsoRegistry`]. Manager/group/start-storage/reaper modules
//! own the remaining execution and lifecycle state.

/// The board policy's dynamic-application profile: the single place
/// where the board ABI decides which loader profile an application links with.
#[cfg(target_board = "qemu_mps2_an385")]
pub fn board_dynamic_profile() -> blueos_loader::LoadProfile {
    blueos_loader::LoadProfile::arm_thumb_soft_float(blueos_loader::ElfType::Dyn)
}

pub mod adapters;
pub mod group;
pub mod loader;
pub mod manager;
pub mod namespace;
pub mod planner;
pub mod publication;
pub mod reaper;
pub mod registry;
pub mod runtime;
/// Boot-time installation of the system image into the root tmpfs. Present
/// only when the board asks for it; the loader backend below is independent
/// of it, so a board whose images arrive by another route keeps `runtime`
/// without `seed`.
#[cfg(boot_dynamic_seed)]
pub mod seed;
pub mod service;
pub mod start_storage;
