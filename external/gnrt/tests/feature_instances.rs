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

use guppy::graph::cargo::{CargoOptions, CargoResolverVersion, CargoSet};
use guppy::graph::feature::{FeatureSet, StandardFeatures};
use guppy::graph::PackageGraph;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

/// Creates a minimal library package under `root/name` for Cargo metadata tests.
///
/// `manifest` adds dependency, feature, or library settings after the package
/// header; `source` supplies the contents of `src/lib.rs`.
fn write_package(root: &Path, name: &str, manifest: &str, source: &str) {
    let dir = root.join(name);
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::write(
        dir.join("Cargo.toml"),
        format!("[package]\nname = {name:?}\nversion = \"1.0.0\"\nedition = \"2021\"\n{manifest}"),
    )
    .unwrap();
    fs::write(dir.join("src/lib.rs"), source).unwrap();
}

/// Resolves the named root packages with Cargo Resolver V2.
///
/// Each call starts from the selected roots' default features and computes
/// separate host and target feature sets within the shared package graph.
fn resolve_roots<'g>(graph: &'g PackageGraph, roots: &[&str]) -> CargoSet<'g> {
    let ids: Vec<_> = graph
        .packages()
        .filter(|package| roots.contains(&package.name()))
        .map(|package| package.id())
        .collect();
    assert_eq!(ids.len(), roots.len());
    let initial = graph
        .resolve_ids(ids)
        .unwrap()
        .to_feature_set(StandardFeatures::Default);
    let mut options = CargoOptions::new();
    options.set_resolver(CargoResolverVersion::V2);
    initial.into_cargo_set(&options).unwrap()
}

/// Returns a package's enabled named features in deterministic order.
///
/// Returns an empty set if `set` does not include the package.
fn features(set: &FeatureSet<'_>, package: &str) -> BTreeSet<String> {
    let id = set
        .graph()
        .package_graph()
        .packages()
        .find(|metadata| metadata.name() == package)
        .unwrap()
        .id();
    set.features_for(id)
        .unwrap()
        .map(|list| list.named_features().map(str::to_owned).collect())
        .unwrap_or_default()
}

#[test]
fn shared_package_graph_preserves_independent_feature_instances() {
    let fixture = tempfile::tempdir().unwrap();
    let root = fixture.path();
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nresolver = \"2\"\nmembers = [\"root-a\", \"root-b\"]\n\
         exclude = [\"library\", \"shared\", \"chip-a\", \"chip-b\", \"helper\"]\n",
    )
    .unwrap();
    for feature in ["a", "b"] {
        write_package(
            root,
            &format!("root-{feature}"),
            &format!(
                "[dependencies]\nlibrary = {{ path = \"../library\", \
                 default-features = false, features = [{feature:?}] }}\n"
            ),
            "",
        );
        write_package(root, &format!("chip-{feature}"), "", "");
    }
    write_package(
        root,
        "shared",
        "[features]\na = []\nb = []\nbuild = []\n",
        "",
    );
    write_package(
        root,
        "helper",
        "[lib]\nproc-macro = true\n[features]\na = []\nb = []\n",
        "",
    );
    write_package(
        root,
        "library",
        r#"
[dependencies]
chip-a = { path = "../chip-a", optional = true }
chip-b = { path = "../chip-b", optional = true }
shared = { path = "../shared", default-features = false }
helper = { path = "../helper", default-features = false }
[build-dependencies]
shared = { path = "../shared", default-features = false, features = ["build"] }
[features]
a = ["dep:chip-a", "shared/a", "helper/a"]
b = ["dep:chip-b", "shared/b", "helper/b"]
"#,
        "#[cfg(all(feature = \"a\", feature = \"b\"))]\ncompile_error!(\"exclusive features\");\n",
    );
    fs::write(root.join("library/build.rs"), "fn main() {}\n").unwrap();
    let mut metadata = guppy::MetadataCommand::new();
    metadata.cargo_path(env!("CARGO"));
    metadata.current_dir(root);
    metadata.other_options(vec!["--offline".to_owned()]);
    let graph = metadata.exec().unwrap().build_graph().unwrap();

    let combined = resolve_roots(&graph, &["root-a", "root-b"]);
    assert_eq!(
        features(combined.target_features(), "library"),
        BTreeSet::from(["a".to_owned(), "b".to_owned()])
    );
    for selected in ["a", "b"] {
        let instance = resolve_roots(&graph, &[&format!("root-{selected}")]);
        for package in ["library", "shared"] {
            assert_eq!(
                features(instance.target_features(), package),
                BTreeSet::from([selected.to_owned()])
            );
        }
        assert_eq!(
            features(instance.host_features(), "helper"),
            BTreeSet::from([selected.to_owned()])
        );
        assert_eq!(
            features(instance.host_features(), "shared"),
            BTreeSet::from(["build".to_owned(), selected.to_owned()])
        );
        let packages: BTreeSet<_> = instance
            .target_features()
            .to_package_set()
            .packages(guppy::graph::DependencyDirection::Forward)
            .map(|package| package.name().to_owned())
            .collect();
        assert!(packages.contains(&format!("chip-{selected}")));
        let other = if selected == "a" { "b" } else { "a" };
        assert!(!packages.contains(&format!("chip-{other}")));
    }
}
