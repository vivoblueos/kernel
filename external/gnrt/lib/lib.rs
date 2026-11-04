// Copyright 2022 The Chromium Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#![forbid(unsafe_op_in_unsafe_fn)]
#![forbid(unsafe_code)]

pub mod collect;
pub mod condition;
pub mod config;
pub mod crates;
pub mod deps;
pub mod generate;
pub mod gn;
/// Represents conditions rendered through project GN templates.
pub mod gn_condition;
pub mod group;
pub mod inherit;
pub mod manifest;
pub mod package;
pub mod paths;
pub mod readme;
pub mod resolve;
pub mod selector;
pub mod sync_context;
/// Fingerprints sync inputs and publishes recoverable updates.
pub mod sync_state;
pub mod target_triple {
    include!(concat!(env!("OUT_DIR"), "/target_triple.rs"));
}
pub mod toml_edit_utils;
pub mod unsafe_code_detector;
pub mod util;
