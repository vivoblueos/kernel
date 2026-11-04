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

//! Shared domain data produced by one `gnrt sync` run.

use crate::{
    collect::{DeclarationGroups, ResolutionScope},
    package::Package,
};
use serde::Serialize;
use std::collections::BTreeMap;

/// Data shared between the collect, resolve, and generate stages.
///
/// Command inputs, paths, and temporary Cargo graph values stay in the modules
/// that use them. Resolved crates use the [`Package`] model, which keeps the
/// raw Cargo target selectors for the generate stage to translate.
#[derive(Debug)]
pub struct SyncContext {
    /// The complete declaration catalog collected from registered files.
    pub catalog: DeclarationGroups,
    /// The GN files and build inputs that affected collection.
    pub collect_inputs: Vec<std::path::PathBuf>,
    /// Concrete GN scopes, including independently configured nested builds.
    pub scopes: Vec<ResolutionScope>,
    /// The declarations selected for this sync request.
    pub declarations: DeclarationGroups,
    /// Resolved recipes keyed by declaration label and exact Cargo package ID.
    pub crates: BTreeMap<String, CrateInfo>,
}

/// A third-party crate and the generation data resolved for this sync run.
#[derive(Debug, Clone, Serialize)]
pub struct CrateInfo {
    /// The feature scope and resolution context for this compilation instance.
    pub instance: String,
    /// The Cargo Host/Target context for this recipe.
    pub context: crate::package::ResolutionContext,
    /// The GN directory where this crate's rules are generated.
    pub rule_dir: String,
    /// The Cargo source identifier, or `None` for a local package.
    pub source: Option<String>,
    /// The crate source directory as a project-root-relative GN path.
    pub path: String,
    /// The resolved Cargo package data, flattened in serialized output.
    #[serde(flatten)]
    pub package: Package,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        group::Group,
        package::{FeatureGroup, Package},
    };
    use semver::Version;

    #[test]
    fn crate_info_serializes_generation_fields_flattened() {
        let info = CrateInfo {
            instance: "//test:bitflags".to_owned(),
            context: crate::package::ResolutionContext::Target,
            rule_dir: "//external/vendor/bitflags-2.10.0".to_owned(),
            source: Some("registry+https://github.com/rust-lang/crates.io-index".to_owned()),
            path: "//external/vendor/bitflags-2.10.0".to_owned(),
            package: Package {
                package_name: "bitflags".to_owned(),
                version: Version::new(2, 10, 0),
                declared_by: Vec::new(),
                description: None,
                links: None,
                authors: Vec::new(),
                edition: "2021".to_owned(),
                rustflags: Vec::new(),
                repository: None,
                homepage: None,
                license: None,
                license_file: None,
                rust_version: None,
                readme: None,
                dependencies: Vec::new(),
                build_dependencies: Vec::new(),
                target_features: vec![FeatureGroup {
                    condition: None,
                    features: vec!["std".to_owned()],
                }],
                host_features: Vec::new(),
                declared_conditions: Vec::new(),
                lib_target: None,
                bin_targets: Vec::new(),
                build_script: None,
                group: Group::Safe,
                is_local: false,
                is_toplevel_dep: true,
            },
        };

        let value = serde_json::to_value(info).unwrap();
        assert_eq!(value["package_name"], "bitflags");
        assert_eq!(value["version"], "2.10.0");
        assert_eq!(value["path"], "//external/vendor/bitflags-2.10.0");
        assert_eq!(
            value["target_features"][0]["features"],
            serde_json::json!(["std"])
        );
        assert!(value.get("package").is_none());
        assert!(value["lib_target"].is_null());
    }
}
