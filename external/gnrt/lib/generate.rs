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

//! Generates crate `BUILD.gn` files and the declaration-to-target index.
//!
//! Converts resolved host and target recipes into template data, preserving
//! feature, dependency, alias, and rustflag conditions as structured expressions.
//! Recipes sharing a vendored directory produce one file with distinct target
//! names. The configured project template controls the GN target definitions.

use crate::collect::{ConfigurableValue, Declaration, DeclarationGroups};
use crate::config::BuildConfig;
use crate::crates::{Epoch, NormalizedName};
use crate::gn_condition::{self, ConditionExpr};
use crate::package::{Dependency, FeatureGroup, Package, ResolutionContext};
use crate::paths::GnrtPaths;
use crate::selector;
use crate::sync_context::{CrateInfo, SyncContext};
use crate::util::{
    create_dirs_if_needed, format_gn_file, gn_path_label_to_path,
    init_handlebars_with_template_paths, render_handlebars,
};
use anyhow::{bail, ensure, Context, Result};
use semver::Version;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::Path;

/// The Handlebars render context for one crate's `BUILD.gn`.
///
/// Built from the resolved `package::Package` and `selector`.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CrateBuildFile {
    /// One entry per lib target and per bin target of the crate.
    pub targets: Vec<Target>,
}

/// A single GN target generated for a crate.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Target {
    /// The GN target name, including its compilation instance identity.
    pub name: String,
    /// The Rust crate name without the compilation instance suffix.
    pub crate_name: String,
    /// `rlib`, `proc-macro`, or `bin`.
    pub crate_type: String,
    /// Cargo Host/Target resolution context for this crate.
    pub context: String,
    /// The crate root source file as a project-root-relative GN path.
    ///
    /// Emitted as the single `sources` entry so GN infers `crate_root`; the
    /// other Rust sources are tracked by rustc dep-info.
    pub crate_root: String,
    /// Rust edition.
    pub edition: String,
    /// Package version.
    pub version: String,
    /// Semver compatibility epoch of `version`.
    pub epoch: String,
    /// `CARGO_PKG_*` and `CARGO_MANIFEST_DIR` values.
    pub rustenv: Vec<String>,
    /// Ordered rustc argument groups with optional GN conditions.
    pub rustflags: Vec<CondGroup<String>>,
    /// Shared vendored manifest directory as a GN source path.
    pub manifest_dir: String,
    /// Stable compilation identity including its declaration domain.
    pub rustc_metadata: String,
    /// Resolved features for this crate's Cargo resolution context.
    pub features: Vec<CondGroup<String>>,
    /// Normal dependencies in the target context.
    pub deps: Vec<CondGroup<String>>,
    /// Build dependencies.
    pub build_deps: Vec<CondGroup<String>>,
    /// Renamed dependencies.
    pub aliased_deps: Vec<CondGroup<Alias>>,
    /// Renamed dependencies of this recipe's host-compiled build script.
    pub build_aliased_deps: Vec<CondGroup<Alias>>,
    /// GN path of the build script, or `None` when the package has no build
    /// script or config removed it.
    pub build_root: Option<String>,
    /// Sources of the build-script target (the build script itself).
    pub build_sources: Vec<String>,
    /// Extra inputs of the build-script action.
    pub build_script_inputs: Vec<String>,
    /// Declared outputs of the build-script action. Currently a single marker
    /// file the runner rewrites on every run, so a build-script re-run always
    /// rebuilds the main crate.
    pub build_script_outputs: Vec<String>,
    /// `CARGO_FEATURE_*=1` entries for the build script, as condition groups
    /// so the generated BUILD.gn can gate them per board.
    pub build_script_env: Vec<CondGroup<String>>,
}

/// The build-script output marker file name.
fn build_script_stamp(crate_name: &str, version: &Version) -> String {
    format!("{crate_name}-{version}.build_script_outputs.stamp")
}

/// Renders a feature name the way Cargo exports it to build scripts.
fn cargo_feature_env(name: &str) -> String {
    format!("CARGO_FEATURE_{}=1", name.to_uppercase().replace('-', "_"))
}

/// Maps feature-name condition groups to `CARGO_FEATURE_*=1` entries.
fn feature_env_groups(groups: &[CondGroup<String>]) -> Vec<CondGroup<String>> {
    groups
        .iter()
        .map(|group| CondGroup {
            cond: group.cond.clone(),
            items: group
                .items
                .iter()
                .map(|name| cargo_feature_env(name))
                .collect(),
        })
        .collect()
}

/// The Rust edition used to compile `package`: the per-crate config override
/// when set, otherwise the manifest edition.
fn edition(package: &Package, config: &BuildConfig) -> String {
    config
        .get_crate_config(&package.package_name, &package.version)
        .and_then(|crate_config| crate_config.edition.clone())
        .unwrap_or_else(|| package.edition.clone())
}

/// Build-script fields shared by a package's targets.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct BuildScript {
    root: Option<String>,
    sources: Vec<String>,
    inputs: Vec<String>,
    outputs: Vec<String>,
}

/// Collects the build-script fields for a package.
///
/// Returns an empty value when the package has no build script or the build
/// config removes it.
fn build_script(
    package: &Package,
    config: &BuildConfig,
    paths: &dyn GnrtPaths,
) -> Result<BuildScript> {
    let crate_config = config.get_crate_config(&package.package_name, &package.version);
    if crate_config.is_some_and(|c| c.remove_build_rs) {
        return Ok(BuildScript::default());
    }
    let Some(build_script) = &package.build_script else {
        return Ok(BuildScript::default());
    };
    let root = gn_path(paths, build_script)?;
    let crate_name = NormalizedName::from_crate_name(&package.package_name).to_string();
    Ok(BuildScript {
        root: Some(root.clone()),
        sources: vec![root],
        inputs: Vec::new(),
        outputs: vec![build_script_stamp(&crate_name, &package.version)],
    })
}

/// Entries enabled under one GN condition.
///
/// Shared by dependencies and features. `cond` is `None` for unconditional
/// entries; otherwise it retains the condition's Cargo or GN meaning.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct CondGroup<T> {
    /// Condition enabling these items, or `None` when unconditional.
    pub cond: Option<ConditionExpr>,
    /// Values enabled by `cond`.
    pub items: Vec<T>,
}

/// A renamed dependency edge (`package = "..."`).
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Alias {
    /// The name the crate uses for the dependency.
    pub use_name: String,
    /// The real dependency label.
    pub label: String,
}

/// Generated GN labels keyed by feature instance, package name, and version.
type LabelMap = BTreeMap<(String, String, Version), String>;

/// The host toolchain label that qualifies host-context dependency edges.
///
/// Prefers a declared host toolchain; otherwise uses the `gn.host_toolchain`
/// value from the config. Collection rejects conflicting host labels, so any
/// declared host label serves every generated `BUILD.gn`.
fn host_toolchain_label(declarations: &DeclarationGroups, fallback: &str) -> String {
    declarations
        .gn
        .iter()
        .find_map(|item| match item {
            Declaration::Toolchain(toolchain) if toolchain.role == "host" => {
                Some(toolchain.label.clone())
            }
            _ => None,
        })
        .unwrap_or_else(|| fallback.to_owned())
}

/// The proxy index written to `gnrt_crate_index.json`.
#[derive(Debug, Serialize)]
struct CrateIndex {
    version: u32,
    crates: Vec<CrateIndexEntry>,
}

/// A `cargo_spec` declaration label and the crate label it maps to.
#[derive(Debug, Serialize)]
struct CrateIndexEntry {
    /// The declaration label business BUILD.gn references.
    proxy: String,
    /// The generated crate target label.
    #[serde(skip_serializing_if = "Option::is_none")]
    target_label: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    host_label: Option<String>,
    crate_type: String,
}

/// Generates a `BUILD.gn` for every resolved crate and the proxy index that
/// maps declaration labels to the generated crate labels.
///
/// # Errors
///
/// Returns an error if a crate's vendored source directory is missing, a
/// dependency has no generated label, the configured template cannot be loaded,
/// or a rule or index file cannot be written.
pub fn generate(context: &SyncContext, paths: &dyn GnrtPaths) -> Result<()> {
    let stage = tempfile::tempdir().context("creating generation staging directory")?;
    let files = generate_to(context, paths, stage.path())?;
    for relative in files {
        let destination = paths.root().join(&relative);
        create_dirs_if_needed(destination.parent().unwrap_or(paths.root()))?;
        std::fs::copy(stage.path().join(&relative), &destination)
            .with_context(|| format!("publishing {}", destination.display()))?;
    }
    Ok(())
}

/// Renders generated rules and the proxy index beneath a staging directory.
///
/// # Errors
///
/// Returns an error if sources, templates, dependency labels or output files
/// cannot be read, resolved or written.
pub fn generate_to(
    context: &SyncContext,
    paths: &dyn GnrtPaths,
    stage_dir: &Path,
) -> Result<Vec<std::path::PathBuf>> {
    let config = BuildConfig::from_path(paths.third_party_config_file())?;
    let template_path = paths
        .third_party_config_file()
        .parent()
        .context("gnrt config file has no parent directory")?
        .join(&config.gn_config.build_file_template);
    let handlebars = init_handlebars_with_template_paths(&[&template_path])?;

    let labels = crate_label_map(context);
    let host_toolchain =
        host_toolchain_label(&context.declarations, &config.gn_config.host_toolchain);
    let mut build_files: BTreeMap<std::path::PathBuf, CrateBuildFile> = BTreeMap::new();
    for crate_info in context.crates.values() {
        let dir = gn_path_label_to_path(paths.root(), &crate_info.path)?;
        ensure!(
            dir.is_dir(),
            "vendored source dir {} is missing; resolve did not materialize {} {}",
            dir.display(),
            crate_info.package.package_name,
            crate_info.package.version
        );
        let build_file =
            build_crate_build_file(crate_info, &config, &labels, &host_toolchain, paths)?;
        let relative_dir = std::path::PathBuf::from(crate_info.rule_dir.trim_start_matches("//"));
        build_files
            .entry(relative_dir)
            .or_insert_with(|| CrateBuildFile {
                targets: Vec::new(),
            })
            .targets
            .extend(build_file.targets);
    }

    let mut files = Vec::with_capacity(build_files.len().saturating_add(1));
    for (relative_dir, mut build_file) in build_files {
        build_file.targets.sort_by(|a, b| a.name.cmp(&b.name));
        ensure!(
            build_file
                .targets
                .windows(2)
                .all(|pair| pair[0].name != pair[1].name),
            "duplicate GN target in {}",
            relative_dir.display()
        );
        let rule_dir = stage_dir.join(&relative_dir);
        create_dirs_if_needed(&rule_dir)?;
        let build_file_path = rule_dir.join("BUILD.gn");
        render_handlebars(&handlebars, &template_path, &build_file, &build_file_path)
            .with_context(|| format!("rendering BUILD.gn for {}", relative_dir.display()))?;
        format_gn_file(&build_file_path)
            .with_context(|| format!("formatting {}", build_file_path.display()))?;
        files.push(relative_dir.join("BUILD.gn"));
    }

    let index = crate_index(&context.declarations, &context.crates)?;
    let index_relative = paths.third_party().join("gnrt_crate_index.json");
    let index_path = stage_dir.join(&index_relative);
    write_crate_index_file(&index_path, &index)?;

    log::debug!(
        "generate: {} crates rendered, {} declarations indexed at {}",
        context.crates.len(),
        index.crates.len(),
        index_path.display()
    );
    files.push(index_relative);
    Ok(files)
}

/// Builds the proxy index from the `cargo_spec` declarations.
///
/// `declared_by` already records, for every resolved crate, the declaration
/// labels that pulled it in, so the index is its inverse. Iterating the
/// declarations still catches a declared crate that resolve dropped.
fn crate_index(
    declarations: &DeclarationGroups,
    resolved: &BTreeMap<String, CrateInfo>,
) -> Result<CrateIndex> {
    let mut labels_by_proxy: BTreeMap<&str, CrateIndexEntry> = BTreeMap::new();
    for crate_info in resolved.values() {
        for proxy in &crate_info.package.declared_by {
            let entry = labels_by_proxy
                .entry(proxy)
                .or_insert_with(|| CrateIndexEntry {
                    proxy: proxy.clone(),
                    target_label: None,
                    host_label: None,
                    crate_type: crate_info
                        .package
                        .lib_target
                        .as_ref()
                        .map(|target| target.lib_type.to_string())
                        .unwrap_or_else(|| "bin".to_owned()),
                });
            let slot = match crate_info.context {
                ResolutionContext::Target => &mut entry.target_label,
                ResolutionContext::Host => &mut entry.host_label,
            };
            let label = crate_label(crate_info);
            ensure!(
                slot.as_ref().map_or(true, |previous| previous == &label),
                "declaration {proxy} has conflicting {:?} bindings",
                crate_info.context
            );
            *slot = Some(label);
        }
    }
    let mut crates = Vec::new();
    for declaration in &declarations.cargo {
        let Declaration::Crate(declaration) = declaration else {
            continue;
        };
        let entry = labels_by_proxy
            .remove(declaration.label.as_str())
            .with_context(|| {
                format!(
                    "declaration {} ({}) has no resolved crate",
                    declaration.label, declaration.package
                )
            })?;
        crates.push(entry);
    }
    crates.sort_by(|lhs, rhs| lhs.proxy.cmp(&rhs.proxy));
    Ok(CrateIndex { version: 1, crates })
}

/// Serializes the proxy index to `path`.
fn write_crate_index_file(path: &Path, index: &CrateIndex) -> Result<()> {
    let json = serde_json::to_string_pretty(index).context("serializing gnrt_crate_index.json")?;
    create_dirs_if_needed(path.parent().unwrap_or(Path::new(".")))?;
    std::fs::write(path, json).with_context(|| format!("writing {}", path.display()))
}

/// Builds the render model for one crate.
fn build_crate_build_file(
    crate_info: &CrateInfo,
    config: &BuildConfig,
    labels: &LabelMap,
    host_toolchain: &str,
    paths: &dyn GnrtPaths,
) -> Result<CrateBuildFile> {
    let package = &crate_info.package;
    let mut targets = Vec::with_capacity(package.bin_targets.len().saturating_add(1));

    // A package has a single build script. Attach it to the lib target only:
    // `cargo_crate` creates one build-script action per target, so attaching it
    // to several targets would have them collide on the same action outputs.
    let build = build_script(package, config, paths)?;
    let context = crate_info.context;
    let context_name = match context {
        ResolutionContext::Target => "target",
        ResolutionContext::Host => "host",
    };
    let mut features = match context {
        ResolutionContext::Target => feature_groups(&package.target_features, context)?,
        ResolutionContext::Host => feature_groups(&package.host_features, context)?,
    };
    if context == ResolutionContext::Target {
        features.extend(declared_groups(&package.declared_conditions)?);
    }

    if let Some(lib_target) = &package.lib_target {
        let crate_name = NormalizedName::from_crate_name(&package.package_name).to_string();
        let name = instance_target_name(crate_info, &crate_name);
        targets.push(Target {
            rustc_metadata: format!("{}:{name}", crate_info.rule_dir),
            name,
            crate_name,
            crate_type: lib_target.lib_type.to_string(),
            context: context_name.to_owned(),
            crate_root: gn_path(paths, &lib_target.root)?,
            edition: edition(package, config),
            version: package.version.to_string(),
            epoch: Epoch::from_version(&package.version).to_version_string(),
            rustenv: rustenv(package)?,
            rustflags: rustflag_groups(&package.rustflags),
            manifest_dir: crate_info.path.clone(),
            features: features.clone(),
            deps: dependency_groups(package.dependencies.iter(), labels, host_toolchain, context)?,
            build_deps: dependency_groups(
                package.build_dependencies.iter(),
                labels,
                host_toolchain,
                context,
            )?,
            aliased_deps: alias_groups(
                package.dependencies.iter(),
                labels,
                host_toolchain,
                context,
            )?,
            build_aliased_deps: alias_groups(
                package.build_dependencies.iter(),
                labels,
                host_toolchain,
                context,
            )?,
            build_root: build.root.clone(),
            build_sources: build.sources.clone(),
            build_script_inputs: build.inputs.clone(),
            build_script_outputs: build.outputs.clone(),
            build_script_env: feature_env_groups(&features),
        });
    }

    for bin in &package.bin_targets {
        let crate_name = NormalizedName::from_crate_name(&bin.name).to_string();
        let name = instance_target_name(crate_info, &format!("{crate_name}__bin"));
        targets.push(Target {
            rustc_metadata: format!("{}:{name}", crate_info.rule_dir),
            name,
            crate_name,
            crate_type: "bin".to_owned(),
            context: context_name.to_owned(),
            crate_root: gn_path(paths, &bin.root)?,
            edition: edition(package, config),
            version: package.version.to_string(),
            epoch: Epoch::from_version(&package.version).to_version_string(),
            rustenv: rustenv(package)?,
            rustflags: rustflag_groups(&package.rustflags),
            manifest_dir: crate_info.path.clone(),
            features: features.clone(),
            deps: dependency_groups(package.dependencies.iter(), labels, host_toolchain, context)?,
            build_deps: dependency_groups(
                package.build_dependencies.iter(),
                labels,
                host_toolchain,
                context,
            )?,
            aliased_deps: Vec::new(),
            build_aliased_deps: Vec::new(),
            build_root: None,
            build_sources: Vec::new(),
            build_script_inputs: Vec::new(),
            build_script_outputs: Vec::new(),
            build_script_env: Vec::new(),
        });
    }

    if targets.is_empty() {
        bail!("package {} has no lib or bin target", package.package_name);
    }
    Ok(CrateBuildFile { targets })
}

/// Maps every resolved crate to its generated GN label.
fn crate_label_map(context: &SyncContext) -> LabelMap {
    context
        .crates
        .values()
        .map(|crate_info| {
            let package = &crate_info.package;
            let key = (
                crate_info.instance.clone(),
                package.package_name.clone(),
                package.version.clone(),
            );
            (key, crate_label(crate_info))
        })
        .collect()
}

/// The generated GN label of a resolved crate.
fn crate_label(crate_info: &CrateInfo) -> String {
    let crate_name = NormalizedName::from_crate_name(&crate_info.package.package_name).to_string();
    let target = instance_target_name(crate_info, &crate_name);
    format!("{}:{target}", crate_info.rule_dir)
}

/// Returns a GN target name unique to a compilation instance.
fn instance_target_name(crate_info: &CrateInfo, name: &str) -> String {
    let (context, shared_instance) = match crate_info.context {
        ResolutionContext::Target => ("target", "shared"),
        ResolutionContext::Host => ("host", "shared#host"),
    };
    let target = format!("{name}_variant_{context}");
    if crate_info.instance == shared_instance {
        target
    } else {
        let hash = format!("{:x}", Sha256::digest(crate_info.instance.as_bytes()));
        format!("{target}_{}", &hash[..12])
    }
}

/// Groups dependency edges by their GN condition, keeping a stable order.
fn dependency_groups<'a>(
    edges: impl Iterator<Item = &'a Dependency>,
    labels: &LabelMap,
    host_toolchain: &str,
    context: ResolutionContext,
) -> Result<Vec<CondGroup<String>>> {
    let mut grouped: BTreeMap<Option<ConditionExpr>, Vec<String>> = BTreeMap::new();
    for edge in edges {
        let cond = edge_condition_for(edge, context)?;
        grouped
            .entry(cond)
            .or_default()
            .push(dependency_label(edge, labels, host_toolchain)?);
    }
    Ok(grouped
        .into_iter()
        .map(|(cond, mut items)| {
            items.sort();
            CondGroup { cond, items }
        })
        .collect())
}

/// Groups renamed dependency edges by their GN condition.
fn alias_groups<'a>(
    edges: impl Iterator<Item = &'a Dependency>,
    labels: &LabelMap,
    host_toolchain: &str,
    context: ResolutionContext,
) -> Result<Vec<CondGroup<Alias>>> {
    let mut grouped: BTreeMap<Option<ConditionExpr>, Vec<Alias>> = BTreeMap::new();
    for edge in edges {
        let normalized = NormalizedName::from_crate_name(&edge.package_name).to_string();
        if edge.use_name == normalized {
            continue;
        }
        grouped
            .entry(edge_condition_for(edge, context)?)
            .or_default()
            .push(Alias {
                use_name: edge.use_name.clone(),
                label: dependency_label(edge, labels, host_toolchain)?,
            });
    }
    Ok(grouped
        .into_iter()
        .map(|(cond, mut items)| {
            items.sort_by(|lhs, rhs| lhs.use_name.cmp(&rhs.use_name));
            CondGroup { cond, items }
        })
        .collect())
}

/// The GN condition under which an edge applies, including conditional removal.
#[cfg(test)]
fn edge_condition(edge: &Dependency) -> Result<Option<ConditionExpr>> {
    edge_condition_for(edge, ResolutionContext::Target)
}

fn edge_condition_for(
    edge: &Dependency,
    context: ResolutionContext,
) -> Result<Option<ConditionExpr>> {
    let platform = selector::edge_condition(&edge.condition, edge.context)?;
    let condition = match context {
        ResolutionContext::Target => &edge.target_condition,
        ResolutionContext::Host => &edge.host_condition,
    };
    let activation = selector::condition_expr(condition, context)?;
    let mut conditions = Vec::new();
    conditions.extend(platform);
    conditions.extend(activation);
    let removal = edge
        .removal
        .as_ref()
        .map(|removal| selector::removal_condition(&removal.when, edge.context))
        .transpose()?;
    conditions.extend(removal);
    let condition = gn_condition::all(conditions);
    Ok((condition != ConditionExpr::True).then_some(condition))
}

/// The generated GN label of a dependency.
fn dependency_label(edge: &Dependency, labels: &LabelMap, host_toolchain: &str) -> Result<String> {
    let label = labels
        .get(&(
            edge.instance.clone(),
            edge.package_name.clone(),
            edge.version.clone(),
        ))
        .cloned()
        .with_context(|| {
            format!(
                "no generated label for dependency {} {}",
                edge.package_name, edge.version
            )
        })?;
    // rust.gni expands proc-macro proxy labels to the host toolchain; the
    // alias value must use the same resolved form for GN's aliased_deps
    // lookup to match the dep actually listed in `deps`.
    Ok(match edge.context {
        ResolutionContext::Host => format!("{label}({host_toolchain})"),
        ResolutionContext::Target => label,
    })
}

/// Translates each conditional feature group into a GN condition group.
fn feature_groups(
    groups: &[FeatureGroup],
    context: ResolutionContext,
) -> Result<Vec<CondGroup<String>>> {
    groups
        .iter()
        .map(|group| {
            Ok(CondGroup {
                cond: selector::condition_expr(&group.condition, context)?,
                items: group.features.clone(),
            })
        })
        .collect()
}

/// Preserves argument order because later rustc flags can override earlier ones.
fn rustflag_groups(values: &[ConfigurableValue]) -> Vec<CondGroup<String>> {
    values
        .iter()
        .map(|value| CondGroup {
            cond: value.condition().map(|expression| ConditionExpr::Gn {
                expression: expression.to_owned(),
            }),
            items: value.values().to_vec(),
        })
        .collect()
}

/// Translates conditional `cargo_spec` features into GN condition groups.
///
/// Unlike resolved feature groups, a declared condition is a GN boolean
/// expression verbatim; it is never a Cargo target selector.
fn declared_groups(groups: &[FeatureGroup]) -> Result<Vec<CondGroup<String>>> {
    feature_groups(groups, ResolutionContext::Target)
}

/// The `CARGO_PKG_*` and `CARGO_MANIFEST_DIR` values for a package.
fn rustenv(package: &Package) -> Result<Vec<String>> {
    let version = &package.version;
    let mut env = vec![
        format!("CARGO_PKG_NAME={}", package.package_name),
        format!("CARGO_PKG_VERSION={version}"),
        format!("CARGO_PKG_VERSION_MAJOR={}", version.major),
        format!("CARGO_PKG_VERSION_MINOR={}", version.minor),
        format!("CARGO_PKG_VERSION_PATCH={}", version.patch),
        format!("CARGO_PKG_VERSION_PRE={}", version.pre),
    ];
    push_env(&mut env, "CARGO_MANIFEST_LINKS", package.links.as_deref());
    if !package.authors.is_empty() {
        env.push(format!(
            "CARGO_PKG_AUTHORS={}",
            shell_safe(&package.authors.join(":"))
        ));
    }
    if let Some(description) = &package.description {
        env.push(format!("CARGO_PKG_DESCRIPTION={}", shell_safe(description)));
    }
    push_env(
        &mut env,
        "CARGO_PKG_REPOSITORY",
        package.repository.as_deref(),
    );
    push_env(&mut env, "CARGO_PKG_HOMEPAGE", package.homepage.as_deref());
    push_env(&mut env, "CARGO_PKG_LICENSE", package.license.as_deref());
    push_env(
        &mut env,
        "CARGO_PKG_LICENSE_FILE",
        package.license_file.as_deref(),
    );
    push_env(
        &mut env,
        "CARGO_PKG_RUST_VERSION",
        package.rust_version.as_deref(),
    );
    push_env(&mut env, "CARGO_PKG_README", package.readme.as_deref());
    Ok(env)
}

/// Pushes `key=value` onto `env` when `value` is set.
fn push_env(env: &mut Vec<String>, key: &str, value: Option<&str>) {
    if let Some(value) = value {
        env.push(format!("{key}={value}"));
    }
}

/// Replaces single quotes, which would terminate the single-quoted clippy
/// command line the Rust toolchain writes. Other shell metacharacters are
/// escaped by GN.
fn shell_safe(value: &str) -> String {
    value.replace('\'', "\u{2019}")
}

/// Converts an absolute path into a project-root-relative GN path.
fn gn_path(paths: &dyn GnrtPaths, path: &Path) -> Result<String> {
    let relative = paths.to_gn_abs_path(path).with_context(|| {
        format!(
            "crate path {} is outside project root {}",
            path.display(),
            paths.root().display()
        )
    })?;
    Ok(format!("//{relative}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::package::Removal;

    #[test]
    fn cargo_feature_env_matches_cargo_naming() {
        assert_eq!(cargo_feature_env("alloc"), "CARGO_FEATURE_ALLOC=1");
        assert_eq!(
            cargo_feature_env("log-level-debug"),
            "CARGO_FEATURE_LOG_LEVEL_DEBUG=1"
        );
    }

    /// Creates an unconditional normal dependency for generation fixtures.
    fn dependency(package: &str, use_name: &str) -> Dependency {
        Dependency {
            instance: String::new(),
            target_condition: None,
            host_condition: None,
            package_name: package.to_owned(),
            use_name: use_name.to_owned(),
            version: Version::new(1, 0, 0),
            condition: None,
            context: ResolutionContext::Target,
            removal: None,
        }
    }

    /// Returns generated labels for the dependency fixtures.
    fn labels() -> LabelMap {
        BTreeMap::from([(
            (String::new(), "libc".to_owned(), Version::new(1, 0, 0)),
            "//third_party/libc-1.0.0:libc".to_owned(),
        )])
    }

    /// Renders a condition with the project bindings used by the template fixture.
    fn render_condition(condition: &Option<ConditionExpr>) -> Option<String> {
        condition.as_ref().map(|condition| {
            gn_condition::render(
                condition,
                gn_condition::GnConditionBindings {
                    target_triple: "build_ctx.toolchain_target_triple",
                    target_cfgs: "build_ctx.toolchain_cfgs",
                    host_triple: "host_build_ctx.toolchain_target_triple",
                    host_cfgs: "host_build_ctx.toolchain_cfgs",
                },
            )
        })
    }

    #[test]
    fn edge_condition_combines_condition_and_removal() {
        let mut edge = dependency("libc", "libc");
        edge.condition = Some(vec!["cfg(unix)".to_owned()]);
        let cond = edge_condition(&edge).unwrap().unwrap();
        let rendered = render_condition(&Some(cond)).unwrap();
        assert!(rendered.contains("unix"), "got: {rendered}");

        edge.removal = Some(Removal {
            reason: "test".to_owned(),
            when: vec!["cfg(windows)".to_owned()],
        });
        let cond = edge_condition(&edge).unwrap().unwrap();
        let rendered = render_condition(&Some(cond)).unwrap();
        assert!(
            rendered.contains("unix") && rendered.contains("windows"),
            "got: {rendered}"
        );

        let mut unconditional_edge = dependency("libc", "libc");
        unconditional_edge.condition = None;
        assert_eq!(edge_condition(&unconditional_edge).unwrap(), None);
    }

    #[test]
    fn dependency_groups_sort_labels_and_split_by_condition() {
        let mut typed = dependency("libc", "libc");
        typed.condition = Some(vec!["cfg(unix)".to_owned()]);
        let plain = dependency("libc", "libc");
        let groups = dependency_groups(
            [&typed, &plain].into_iter(),
            &labels(),
            "//build/toolchain:host",
            ResolutionContext::Target,
        )
        .unwrap();
        assert_eq!(groups.len(), 2);
        let unconditional = groups.iter().find(|g| g.cond.is_none()).unwrap();
        assert_eq!(unconditional.items, vec!["//third_party/libc-1.0.0:libc"]);
    }

    #[test]
    fn alias_groups_only_include_renamed_edges() {
        let renamed = dependency("libc", "libc_alias");
        let plain = dependency("libc", "libc");
        let groups = alias_groups(
            [&renamed, &plain].into_iter(),
            &labels(),
            "//build/toolchain:host",
            ResolutionContext::Target,
        )
        .unwrap();
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].items[0].use_name, "libc_alias");
        assert_eq!(groups[0].items[0].label, "//third_party/libc-1.0.0:libc");
    }

    #[test]
    fn render_model_serializes_to_the_template_context() {
        let value = serde_json::to_value(CrateBuildFile {
            targets: vec![Target {
                name: "cfg_if".to_owned(),
                crate_name: "cfg_if".to_owned(),
                crate_type: "rlib".to_owned(),
                context: "target".to_owned(),
                crate_root: "//third_party/cfg-if-1.0.4/src/lib.rs".to_owned(),
                edition: "2018".to_owned(),
                version: "1.0.4".to_owned(),
                epoch: "1".to_owned(),
                rustenv: vec!["CARGO_PKG_NAME=cfg-if".to_owned()],
                rustflags: rustflag_groups(&[
                    ConfigurableValue::Value("--cfg=custom=\"value with spaces\"".to_owned()),
                    ConfigurableValue::Conditional {
                        condition: "board == \"test\"".to_owned(),
                        values: vec!["--cfg=conditional".to_owned()],
                    },
                    ConfigurableValue::Value("-Copt-level=2".to_owned()),
                    ConfigurableValue::Value("-Copt-level=2".to_owned()),
                ]),
                manifest_dir: "//third_party/cfg-if-1.0.4".to_owned(),
                rustc_metadata: "fixture_cfg_if".to_owned(),
                features: vec![CondGroup {
                    cond: None,
                    items: vec!["std".to_owned()],
                }],
                deps: vec![CondGroup {
                    cond: Some(ConditionExpr::CargoCfg {
                        context: ResolutionContext::Target,
                        expression: crate::gn_condition::CfgCondition::Name {
                            name: "unix".to_owned(),
                        },
                    }),
                    items: vec!["//third_party/libc-0.2.189:libc".to_owned()],
                }],
                build_deps: Vec::new(),
                aliased_deps: vec![CondGroup {
                    cond: None,
                    items: vec![Alias {
                        use_name: "lock_api_crate".to_owned(),
                        label: "//third_party/lock_api-0.4.14:lock_api".to_owned(),
                    }],
                }],
                build_aliased_deps: Vec::new(),
                build_root: None,
                build_sources: Vec::new(),
                build_script_inputs: Vec::new(),
                build_script_outputs: Vec::new(),
                build_script_env: Vec::new(),
            }],
        })
        .unwrap();
        let target = &value["targets"][0];
        assert_eq!(target["name"], "cfg_if");
        assert_eq!(target["crate_name"], "cfg_if");
        assert_eq!(target["crate_type"], "rlib");
        assert_eq!(target["version"], "1.0.4");
        assert_eq!(
            target["rustflags"][0]["items"],
            serde_json::json!(["--cfg=custom=\"value with spaces\""])
        );
        assert_eq!(target["rustflags"][1]["cond"]["kind"], "gn");
        assert_eq!(
            target["rustflags"][1]["cond"]["expression"],
            "board == \"test\""
        );
        assert_eq!(target["rustflags"][2], target["rustflags"][3]);
        assert_eq!(target["features"][0]["items"], serde_json::json!(["std"]));
        assert_eq!(target["deps"][0]["cond"]["kind"], "cargo_cfg");
        assert_eq!(
            target["deps"][0]["items"][0],
            "//third_party/libc-0.2.189:libc"
        );
        assert_eq!(
            target["aliased_deps"][0]["items"][0]["use_name"],
            "lock_api_crate"
        );
        let template =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/CARGO_BUILD.gn.hbs");
        let handlebars = init_handlebars_with_template_paths(&[&template]).unwrap();
        let output = tempfile::tempdir().unwrap();
        let path = output.path().join("BUILD.gn");
        render_handlebars(&handlebars, &template, &value, &path).unwrap();
        let generated = std::fs::read_to_string(path).unwrap();
        assert!(generated
            .contains("\"CARGO_MANIFEST_DIR=\" + rebase_path(\"//third_party/cfg-if-1.0.4\")"));
        assert!(!generated.contains(env!("CARGO_MANIFEST_DIR")));
        assert!(generated.contains("context = \"target\""));
        assert!(generated.contains("crate_name = \"cfg_if\""));
        assert!(generated.contains("rustc_metadata = \"fixture_cfg_if\""));
        assert!(generated.contains("\"--cfg=custom=\\\"value with spaces\\\"\""));
        assert!(generated.contains("if (board == \"test\") {\n    rustflags += ["));
        assert!(generated.contains("\"--cfg=conditional\""));
        assert!(
            generated.find("--cfg=custom").unwrap() < generated.find("--cfg=conditional").unwrap()
        );
        assert!(
            generated.find("--cfg=conditional").unwrap() < generated.find("-Copt-level=2").unwrap()
        );
        assert_eq!(generated.matches("-Copt-level=2").count(), 2);
    }

    #[test]
    fn dependency_instances_never_alias_another_declaration() {
        let mut a = dependency("libc", "libc");
        a.instance = "//external/rust:library_a".to_owned();
        let mut b = a.clone();
        b.instance = "//external/rust:library_b".to_owned();
        let labels = BTreeMap::from([
            (
                (
                    a.instance.clone(),
                    a.package_name.clone(),
                    a.version.clone(),
                ),
                "//third_party/libc-1.0.0:libc__a".to_owned(),
            ),
            (
                (
                    b.instance.clone(),
                    b.package_name.clone(),
                    b.version.clone(),
                ),
                "//third_party/libc-1.0.0:libc__b".to_owned(),
            ),
        ]);
        assert_ne!(
            dependency_label(&a, &labels, "//build/toolchain:host").unwrap(),
            dependency_label(&b, &labels, "//build/toolchain:host").unwrap()
        );
    }

    #[test]
    fn host_label_prefers_declaration_over_config_fallback() {
        let host = |label: &str| {
            Declaration::Toolchain(crate::collect::ToolchainDeclaration {
                origin: "//build/toolchain".to_owned(),
                label: label.to_owned(),
                role: "host".to_owned(),
                cc: "clang".to_owned(),
                cxx: "clang++".to_owned(),
                ar: "llvm-ar".to_owned(),
                rustc: "rustc".to_owned(),
                llvm_target: "x86_64".to_owned(),
                target_triple: "x86_64-unknown-none".to_owned(),
            })
        };
        let mut declarations = DeclarationGroups::default();
        declarations.gn = vec![host("//build/rust:host_x64")];
        assert_eq!(
            host_toolchain_label(&declarations, "//build/toolchain:host"),
            "//build/rust:host_x64"
        );
        assert_eq!(
            host_toolchain_label(&DeclarationGroups::default(), "//build/custom:host"),
            "//build/custom:host"
        );
    }

    #[test]
    fn host_edges_use_the_declared_host_toolchain_label() {
        let mut edge = dependency("libc", "libc");
        edge.context = ResolutionContext::Host;
        let labels = labels();
        assert_eq!(
            dependency_label(&edge, &labels, "//build/rust:host_x64").unwrap(),
            "//third_party/libc-1.0.0:libc(//build/rust:host_x64)"
        );
        assert_eq!(
            dependency_label(&edge, &labels, "//build/toolchain:host").unwrap(),
            "//third_party/libc-1.0.0:libc(//build/toolchain:host)"
        );
        edge.context = ResolutionContext::Target;
        assert_eq!(
            dependency_label(&edge, &labels, "//build/rust:host_x64").unwrap(),
            "//third_party/libc-1.0.0:libc"
        );
    }

    #[test]
    fn dependency_activation_preserves_gn_and_host_conditions() {
        use crate::package::ConditionAtom;
        let mut edge = dependency("libc", "libc");
        edge.target_condition = Some(vec![vec![ConditionAtom::Gn {
            expression: "product == \"a\"".to_owned(),
        }]]);
        edge.host_condition = Some(vec![vec![ConditionAtom::Gn {
            expression: "product == \"b\"".to_owned(),
        }]]);
        assert_eq!(
            edge_condition_for(&edge, ResolutionContext::Target).unwrap(),
            Some(ConditionExpr::Gn {
                expression: "product == \"a\"".to_owned(),
            })
        );
        assert_eq!(
            edge_condition_for(&edge, ResolutionContext::Host).unwrap(),
            Some(ConditionExpr::Gn {
                expression: "product == \"b\"".to_owned(),
            })
        );
    }

    #[test]
    fn crate_metadata_maps_labels_and_exports_manifest_links() {
        use crate::collect::CrateDeclaration;
        use crate::group::Group;

        let declarations = DeclarationGroups {
            cargo: vec![Declaration::Crate(CrateDeclaration {
                origin: "cargo".to_owned(),
                isolation: Default::default(),
                label: "//kernel/driver:libc".to_owned(),
                package: "libc".to_owned(),
                version: "1.0.0".to_owned(),
                features: Vec::new(),
                rustflags: Vec::new(),
                default_features: true,
                git: String::new(),
                rev: String::new(),
                branch: String::new(),
                tag: String::new(),
                patches: Vec::new(),
            })],
            gn: Vec::new(),
        };
        let resolved = BTreeMap::from([(
            "libc 1.0.0".to_owned(),
            CrateInfo {
                source: None,
                context: ResolutionContext::Target,
                instance: "//kernel/driver:libc".to_owned(),
                rule_dir: "//third_party/libc-1.0.0".to_owned(),
                path: "//third_party/libc-1.0.0".to_owned(),
                package: Package {
                    package_name: "libc".to_owned(),
                    version: Version::new(1, 0, 0),
                    declared_by: vec!["//kernel/driver:libc".to_owned()],
                    description: None,
                    links: Some("native_ffi".to_owned()),
                    authors: Vec::new(),
                    edition: "2018".to_owned(),
                    rustflags: Vec::new(),
                    repository: None,
                    homepage: None,
                    license: None,
                    license_file: None,
                    rust_version: None,
                    readme: None,
                    dependencies: Vec::new(),
                    build_dependencies: Vec::new(),
                    target_features: Vec::new(),
                    host_features: Vec::new(),
                    declared_conditions: Vec::new(),
                    lib_target: None,
                    bin_targets: Vec::new(),
                    build_script: None,
                    group: Group::Safe,
                    is_local: false,
                    is_toplevel_dep: true,
                },
            },
        )]);

        let index = crate_index(&declarations, &resolved).unwrap();
        let target_label = crate_label(&resolved["libc 1.0.0"]);
        let mut shared = resolved["libc 1.0.0"].clone();
        shared.instance = "shared".to_owned();
        assert_eq!(
            crate_label(&shared),
            "//third_party/libc-1.0.0:libc_variant_target"
        );
        shared.context = ResolutionContext::Host;
        shared.instance = "shared#host".to_owned();
        assert_eq!(
            crate_label(&shared),
            "//third_party/libc-1.0.0:libc_variant_host"
        );
        assert_eq!(index.version, 1);
        assert_eq!(index.crates.len(), 1);
        assert_eq!(index.crates[0].proxy, "//kernel/driver:libc");
        assert_eq!(
            index.crates[0].target_label.as_deref(),
            Some(target_label.as_str())
        );
        assert!(index.crates[0].host_label.is_none());
        let serialized = serde_json::to_value(&index).unwrap();
        assert!(serialized["crates"][0].get("host_label").is_none());
        let mut host_recipe = resolved["libc 1.0.0"].clone();
        host_recipe.context = ResolutionContext::Host;
        host_recipe.instance = "host".to_owned();
        let host_label = crate_label(&host_recipe);
        assert_ne!(target_label, host_label);
        assert_eq!(host_recipe.rule_dir, resolved["libc 1.0.0"].rule_dir);
        let mut both_domains = resolved.clone();
        both_domains.insert("host libc 1.0.0".to_owned(), host_recipe.clone());
        let index = crate_index(&declarations, &both_domains).unwrap();
        assert_eq!(
            index.crates[0].target_label.as_deref(),
            Some(target_label.as_str())
        );
        assert_eq!(
            index.crates[0].host_label.as_deref(),
            Some(host_label.as_str())
        );
        host_recipe.context = ResolutionContext::Target;
        both_domains.insert("conflicting libc 1.0.0".to_owned(), host_recipe);
        assert!(crate_index(&declarations, &both_domains).is_err());

        let mut package = resolved["libc 1.0.0"].package.clone();
        assert!(rustenv(&package)
            .unwrap()
            .contains(&"CARGO_MANIFEST_LINKS=native_ffi".to_owned()));
        package.links = None;
        assert!(!rustenv(&package)
            .unwrap()
            .iter()
            .any(|value| value.starts_with("CARGO_MANIFEST_LINKS=")));

        assert!(
            crate_index(&declarations, &BTreeMap::new()).is_err(),
            "a declaration with no resolved crate must be reported"
        );
    }
}
