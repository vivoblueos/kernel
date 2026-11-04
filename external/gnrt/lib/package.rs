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

//! Resolved third-party package model.
//!
//! Dependency edges keep their raw Cargo target selectors: resolve records what
//! Cargo declared, it does not decide which edges are active for a target. The
//! generate stage maps the selectors onto GN conditions.

use crate::collect::ConfigurableValue;
use crate::deps::{BinTarget, LibTarget};
use crate::group::Group;
use semver::Version;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// A resolved package recipe within a declaration feature closure.
#[derive(Clone, Debug, Serialize)]
pub struct Package {
    /// The package name as used by cargo.
    pub package_name: String,
    /// The package version as used by cargo.
    pub version: Version,
    /// The `cargo_spec` declaration labels that declare this package.
    ///
    /// A package can be declared from several GN modules.
    pub declared_by: Vec<String>,
    /// Package description from Cargo metadata.
    pub description: Option<String>,
    /// Native library identifier from the manifest's `links` field.
    pub links: Option<String>,
    /// Authors listed in Cargo metadata.
    pub authors: Vec<String>,
    /// Rust edition declared by the package.
    pub edition: String,
    /// Additional rustc arguments from this package's declaration.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub rustflags: Vec<ConfigurableValue>,
    /// Repository URL from Cargo metadata, when present.
    pub repository: Option<String>,
    /// Homepage URL from Cargo metadata, when present.
    pub homepage: Option<String>,
    /// License expression from Cargo metadata, when present.
    pub license: Option<String>,
    /// The `license-file` path as written in the manifest, relative to the
    /// package root.
    pub license_file: Option<String>,
    /// The `rust-version` field, normalized to a full semver version.
    pub rust_version: Option<String>,
    /// The `readme` path as written in the manifest, relative to the package
    /// root.
    pub readme: Option<String>,
    /// This package's normal dependencies.
    pub dependencies: Vec<Dependency>,
    /// This package's build-script dependencies.
    pub build_dependencies: Vec<Dependency>,
    /// The features enabled when the package is built for the target.
    pub target_features: Vec<FeatureGroup>,
    /// The features enabled when the package is built for the host.
    pub host_features: Vec<FeatureGroup>,
    /// Features gated on a GN condition from `cargo_spec` `features`,
    /// on top of the resolved feature set. Rendered as
    /// `if (<condition>) { features += [...] }` in the generated BUILD.gn.
    pub declared_conditions: Vec<FeatureGroup>,
    /// The package's lib target, or `None` if it doesn't have one.
    pub lib_target: Option<LibTarget>,
    /// List of binaries provided by the package.
    pub bin_targets: Vec<BinTarget>,
    /// The build script's absolute path, or `None` if the package does not use
    /// one.
    pub build_script: Option<PathBuf>,
    /// What privilege group the crate is a part of.
    pub group: Group,
    /// Whether the source is a local path.
    pub is_local: bool,
    /// Whether this package is depended on directly by the workspace.
    pub is_toplevel_dep: bool,
}

/// One dependency edge of a [`Package`].
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Dependency {
    /// Full declaration label owning this dependency closure.
    pub instance: String,
    /// Symbolic activation when the parent is compiled for the target.
    pub target_condition: SymbolicCondition,
    /// Symbolic activation when the parent is compiled for the host.
    pub host_condition: SymbolicCondition,
    /// The dependency's package name as used by cargo.
    pub package_name: String,
    /// The name of the lib crate as `use`d by the dependent.
    pub use_name: String,
    /// The resolved version of this dependency.
    pub version: Version,
    /// Raw Cargo target selectors declared for this edge; the edge applies when
    /// any of them matches. `None` means the edge is unconditional.
    pub condition: Option<Vec<String>>,
    /// The build side this edge is resolved for.
    pub context: ResolutionContext,
    /// Set when a conditional-removal rule in the build config targets this
    /// edge.
    pub removal: Option<Removal>,
}

/// Features enabled under one symbolic GN/Cargo condition.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct FeatureGroup {
    /// An OR of AND terms retaining each selector's origin and build context.
    pub condition: SymbolicCondition,
    /// The named features enabled while `condition` holds.
    pub features: Vec<String>,
}

/// The host or target context used to resolve dependency edges and features.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum ResolutionContext {
    /// Compiled for the target.
    Target,
    /// Compiled for the host: build scripts and proc-macros.
    Host,
}

/// A conditional-removal rule that was recorded for an edge.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Removal {
    /// The config rule that recorded the removal.
    pub reason: String,
    /// Raw Cargo target selectors under which the edge is removed.
    pub when: Vec<String>,
}

/// A symbolic condition retains its GN or Cargo origin and platform context.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum ConditionAtom {
    /// A declaration expression evaluated by GN.
    Gn {
        /// The GN boolean expression.
        expression: String,
    },
    /// A Cargo platform selector evaluated in the originating build context.
    Cargo {
        /// The raw Cargo target selector.
        selector: String,
        /// The host or target context where the selector is evaluated.
        context: ResolutionContext,
    },
}

/// An OR of AND terms; `None` means unconditional, an empty OR means false.
pub type SymbolicCondition = Option<Vec<Vec<ConditionAtom>>>;
