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

pub(crate) mod connection;
pub(crate) mod connection_err;
pub(crate) mod error;
pub(crate) mod iface;
pub(crate) mod link;
pub(crate) mod net_manager;
pub(crate) mod packet;
pub(crate) mod port_generator;
pub(crate) mod protocol;
pub(crate) mod smoltcp;
pub(crate) mod socket;
pub mod syscalls;
pub(crate) mod types;

// Re-export core types for backward compatibility.
pub use error::NetError;
pub use types::*;

/// Initialize the new layered network architecture components.
///
/// This must be called during kernel initialization to register protocols
/// and populate the link registry. In Phase 0 the existing smoltcp-based
/// `net_manager::init()` remains the primary entry point; this function
/// seeds the registries used by the new code paths.
pub(crate) fn init() {
    protocol::init();
    link::init();
}
