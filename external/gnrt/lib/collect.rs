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

//! Collects `gnrt_declarations` metadata from the GN build graph.
//!
//! The collection runs in two steps, both driven by the `gn` executable:
//! 1. `gn gen <out>` evaluates the graph with the supplied build arguments.
//! 2. `gn meta <out> <entry> --data=gnrt_declarations --walk=""` extracts the
//!    declarations reachable from the entry target.
//!
//! `gn meta` prints one GN-scope block per declaration, which is parsed into
//! `Declaration` values. The result is grouped by `origin` and written as
//! `declarations.json`.

use crate::config::BuildConfig;
use crate::sync_context::SyncContext;
use anyhow::{bail, ensure, Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// One collected declaration, keyed by its `type` field.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum Declaration {
    /// A Cargo crate declaration collected from GN metadata.
    Crate(CrateDeclaration),
    /// A host or target toolchain declaration collected from GN metadata.
    Toolchain(ToolchainDeclaration),
}

/// The boundary for feature unification around a declaration.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Isolation {
    /// Share the root and its transitive dependencies.
    #[default]
    None,
    /// Keep the root separate while sharing its transitive dependencies.
    Root,
    /// Keep the entire dependency closure separate.
    Closure,
}

/// A Cargo crate declaration exported by a GN target.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CrateDeclaration {
    /// The declaration kind recorded by the GN target.
    pub origin: String,

    /// The GN label of the target declaring the crate.
    pub label: String,

    /// The Cargo package name.
    pub package: String,

    /// The requested package version or version requirement.
    pub version: String,

    /// Whether Cargo default features are enabled.
    pub default_features: bool,
    /// The features enabled by this declaration.
    pub features: Vec<ConfigurableValue>,

    /// Additional rustc arguments for the declared crate.
    #[serde(default)]
    pub rustflags: Vec<ConfigurableValue>,

    /// Whether the root or its complete dependency closure is isolated.
    #[serde(default)]
    pub isolation: Isolation,

    /// Git source URL. Empty means crates.io.
    pub git: String,
    /// Commit hash pinning the git source. Empty if unused.
    pub rev: String,
    /// Branch pinning the git source. Empty if unused.
    pub branch: String,
    /// Tag pinning the git source. Empty if unused.
    pub tag: String,

    /// Patch files applied to the vendored package.
    pub patches: Vec<String>,
}

/// An unconditional value or a list enabled by a symbolic GN condition.
#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum ConfigurableValue {
    /// A value enabled for every build configuration.
    Value(String),
    /// Values enabled when GN evaluates the condition to true.
    Conditional {
        /// A GN boolean expression, preserved until build generation.
        condition: String,
        /// Values appended when the condition holds.
        values: Vec<String>,
    },
}

impl ConfigurableValue {
    /// Returns the values needed to prepare every configuration.
    pub fn values(&self) -> &[String] {
        match self {
            Self::Value(value) => std::slice::from_ref(value),
            Self::Conditional { values, .. } => values,
        }
    }

    /// Returns the symbolic condition, or `None` for an unconditional value.
    pub fn condition(&self) -> Option<&str> {
        match self {
            Self::Value(_) => None,
            Self::Conditional { condition, .. } => Some(condition),
        }
    }
}

/// A toolchain declaration exported by a GN target.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct ToolchainDeclaration {
    /// The declaration kind recorded by the GN target.
    pub origin: String,

    /// The GN label of the declaring toolchain target.
    pub label: String,

    /// Whether the toolchain builds product code or host tools.
    pub role: String,

    /// The C compiler executable.
    pub cc: String,

    /// The C++ compiler executable.
    pub cxx: String,

    /// The archiver executable.
    pub ar: String,

    /// The Rust compiler command, including toolchain arguments.
    pub rustc: String,

    /// The LLVM target name passed to the compiler.
    pub llvm_target: String,

    /// The target triple associated with the toolchain.
    pub target_triple: String,
}

/// Declarations grouped into Cargo and GN inputs.
#[derive(Clone, Debug, Default, PartialEq, Deserialize, Serialize)]
pub struct DeclarationGroups {
    /// Cargo crate and toolchain declarations.
    pub cargo: Vec<Declaration>,

    /// Additional GN declarations.
    pub gn: Vec<Declaration>,
}

/// Declaration requests and effective arguments from one concrete GN graph.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct ResolutionScope {
    /// The entry traversed in this graph.
    pub entry: String,
    /// Effective GN arguments, excluding the collection mode switch.
    pub args: BTreeMap<String, String>,
    /// Cargo declarations reached in this graph, excluding nested graphs.
    pub declarations: DeclarationGroups,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct NestedBuild {
    entry: String,
    args: Vec<String>,
    inputs: Vec<PathBuf>,
}

#[derive(Deserialize)]
struct GraphTarget {
    toolchain: String,
    #[serde(default)]
    deps: Vec<String>,
    #[serde(default)]
    public_deps: Vec<String>,
    #[serde(default)]
    data_deps: Vec<String>,
    #[serde(default)]
    metadata: BTreeMap<String, serde_json::Value>,
}

enum ScopeVisit {
    Active,
    Complete,
}

/// Collects the complete catalog and the roots selected by the request.
///
/// # Errors
/// Returns an error for invalid registrations, GN failures, or declarations
/// reachable from a product but absent from the registered catalog.
pub fn collect(
    out_dir: &Path,
    gnrt_out_dir: &Path,
    entry: Option<&str>,
    args: &[String],
    config: &BuildConfig,
) -> Result<SyncContext> {
    if config.collect.declaration_files.is_empty() {
        bail!("collect.declaration_files must register at least one BUILD.gn");
    }
    let mut catalog = DeclarationGroups::default();
    let mut collect_inputs = Vec::new();
    // Load metadata from every registered declaration file into the full catalog.
    for (index, file) in config.collect.declaration_files.iter().enumerate() {
        // GN root labels refer to the directory containing the registered BUILD.gn.
        let root = declaration_root(file)?;
        if !file.is_file() {
            bail!(
                "registered declaration file does not exist: {}",
                file.display()
            );
        }
        let catalog_out = out_dir.join(format!("catalog-{index}"));
        crate::util::create_dirs_if_needed(&catalog_out)?;
        generate_build_dir(&catalog_out, args, Some(&root))?;
        let declarations = extract_catalog(&catalog_out, &root)?;
        catalog.cargo.extend(declarations.cargo);
        collect_inputs.extend(gn_inputs(&catalog_out)?);
    }

    if !config.resolve.toolchain_file.as_os_str().is_empty() {
        let file = &config.resolve.toolchain_file;
        let root = declaration_root(file)?;
        ensure!(
            file.is_file(),
            "toolchain metadata file does not exist: {}",
            file.display()
        );
        let toolchain_out = out_dir.join("toolchains");
        crate::util::create_dirs_if_needed(&toolchain_out)?;
        generate_build_dir(&toolchain_out, args, Some(&root))?;
        let declarations = extract_catalog_kind(&toolchain_out, &root, true)?;
        ensure!(
            !declarations.gn.is_empty(),
            "no toolchain metadata found in {}",
            file.display()
        );
        catalog.gn = declarations.gn;
        collect_inputs.extend(gn_inputs(&toolchain_out)?);
    }

    // Normalize and validate the complete catalog before selecting roots.
    catalog.cargo = dedupe_cargo(catalog.cargo);
    catalog
        .cargo
        .sort_by(|a, b| declaration_label(a).cmp(declaration_label(b)));
    validate(&catalog)?;
    let mut scopes = Vec::new();
    let mut visits = BTreeMap::new();
    // The CLI disables --target, so entry is None for sync and sync --all.
    let declarations = if let Some(entry) = entry {
        // Collect declarations reachable from the requested product entry.
        let selected_out = out_dir.join("target");
        crate::util::create_dirs_if_needed(&selected_out)?;
        // FIXME: Nested product collection calls generate_artifacts.py with
        // --collect-inputs, but the script lacks the JSON config/inputs interface.
        // Full-catalog sync does not traverse this path.
        collect_scope_tree(
            &selected_out,
            entry,
            args,
            &mut scopes,
            &mut collect_inputs,
            &mut visits,
        )?;
        let mut selected = DeclarationGroups::default();
        for scope in &scopes {
            selected.cargo.extend(scope.declarations.cargo.clone());
        }
        selected.cargo = dedupe_cargo(selected.cargo);
        selected.gn = catalog.gn.clone();
        selected
    } else {
        // Full sync prepares every catalog declaration, including unused roots.
        catalog.clone()
    };
    // Require every reachable declaration to exist unchanged in the catalog.
    for scope in &scopes {
        for declaration in &scope.declarations.cargo {
            let label = declaration_label(declaration);
            let registered = catalog
                .cargo
                .iter()
                .find(|d| declaration_label(d) == label)
                .with_context(|| {
                    format!("cargo_spec {label} is outside collect.declaration_files")
                })?;
            if registered != declaration {
                bail!("cargo_spec {label} changes with product configuration; use symbolic conditions");
            }
        }
    }

    // Save the declarations and GN inputs needed by later sync stages.
    collect_inputs.sort();
    collect_inputs.dedup();
    write_declarations(gnrt_out_dir, &declarations, &scopes)?;
    Ok(SyncContext {
        declarations,
        catalog,
        collect_inputs,
        scopes,
        crates: Default::default(),
    })
}

fn collect_scope_tree(
    out_dir: &Path,
    entry: &str,
    args: &[String],
    scopes: &mut Vec<ResolutionScope>,
    inputs: &mut Vec<PathBuf>,
    visits: &mut BTreeMap<(String, String), ScopeVisit>,
) -> Result<()> {
    let key = (entry.to_owned(), crate::util::normalize_gn_args(args)?);
    match visits.get(&key) {
        Some(ScopeVisit::Active) => bail!("nested GN collection cycle at {entry}"),
        Some(ScopeVisit::Complete) => return Ok(()),
        None => {}
    }
    visits.insert(key.clone(), ScopeVisit::Active);
    // A cycle that changes arguments may never repeat the same request key.
    ensure!(
        visits
            .values()
            .filter(|visit| matches!(visit, ScopeVisit::Active))
            .count()
            <= 64,
        "nested GN collection exceeds 64 levels at {entry}"
    );
    generate_build_dir(out_dir, args, Some(entry))?;
    let out = path_str(out_dir);
    let root_target = format!("--root-target={entry}");
    let root_pattern_arg = root_pattern(entry);
    let mut arguments: Vec<&str> = vec!["desc", &out, "*", "--format=json", &root_target];
    if let Some(pattern) = &root_pattern_arg {
        arguments.push(pattern);
    }
    let output = run_gn_with_output(&arguments)?;
    let nested = parse_scope_graph(&output.stdout, entry)?;
    let declarations = extract_declarations(out_dir, entry)?;
    inputs.extend(gn_inputs(out_dir)?);
    scopes.push(ResolutionScope {
        entry: entry.to_owned(),
        args: effective_args(out_dir, Some(entry))?,
        declarations,
    });
    for (index, build) in nested.into_iter().enumerate() {
        for input in &build.inputs {
            ensure!(
                input.is_absolute() && input.is_file(),
                "invalid nested GN input {}",
                input.display()
            );
        }
        inputs.extend(build.inputs);
        collect_scope_tree(
            &out_dir.join(format!("nested-{index}")),
            &build.entry,
            &build.args,
            scopes,
            inputs,
            visits,
        )?;
    }
    visits.insert(key, ScopeVisit::Complete);
    Ok(())
}

fn parse_scope_graph(bytes: &[u8], entry: &str) -> Result<Vec<NestedBuild>> {
    let targets: BTreeMap<String, GraphTarget> =
        serde_json::from_slice(bytes).context("gn desc produced invalid graph JSON")?;
    let mut aliases = BTreeMap::new();
    let mut graph = BTreeMap::new();
    for (label, target) in targets {
        let qualified = if label.ends_with(')') {
            label.clone()
        } else {
            format!("{label}({})", target.toolchain)
        };
        aliases.insert(label, qualified.clone());
        graph.insert(qualified, target);
    }
    let (entry_label, suffix) = entry.split_once('(').unwrap_or((entry, ""));
    let entry_label = if entry_label.contains(':') {
        entry_label.to_owned()
    } else {
        format!(
            "{entry_label}:{}",
            entry_label.rsplit('/').next().unwrap_or_default()
        )
    };
    let entry = if suffix.is_empty() {
        entry_label
    } else {
        format!("{entry_label}({suffix}")
    };
    let mut pending = vec![entry];
    let mut visited = BTreeSet::new();
    let mut nested = Vec::new();
    while let Some(label) = pending.pop() {
        let qualified = aliases.get(&label).unwrap_or(&label);
        if !visited.insert(qualified.clone()) {
            continue;
        }
        let target = graph
            .get(qualified)
            .with_context(|| format!("GN target {label} is missing from collection graph"))?;
        if let Some(values) = target.metadata.get("gnrt_nested_builds") {
            let values: Vec<NestedBuild> = serde_json::from_value(values.clone())
                .with_context(|| format!("invalid nested build metadata on {label}"))?;
            nested.extend(values);
        }
        pending.extend(
            target
                .deps
                .iter()
                .chain(&target.public_deps)
                .chain(&target.data_deps)
                .cloned(),
        );
    }
    Ok(nested)
}

/// Returns effective GN argument values without sync-only arguments.
///
/// # Errors
/// Returns an error if GN fails or its argument report is invalid.
pub fn effective_args(
    out_dir: &Path,
    root_target: Option<&str>,
) -> Result<BTreeMap<String, String>> {
    let out_arg = path_str(out_dir);
    let mut arguments = vec!["args", &out_arg, "--list", "--json"];
    let root_arg;
    let root_pattern_arg;
    if let Some(root) = root_target {
        root_arg = format!("--root-target={root}");
        arguments.push(&root_arg);
        root_pattern_arg = root_pattern(root);
        if let Some(pattern) = &root_pattern_arg {
            arguments.push(pattern);
        }
    }
    let output = run_gn_with_output(&arguments)?;
    parse_effective_args(&output.stdout)
}

fn parse_effective_args(bytes: &[u8]) -> Result<BTreeMap<String, String>> {
    let entries: Vec<serde_json::Value> =
        serde_json::from_slice(bytes).context("gn args produced invalid JSON")?;
    let mut values = BTreeMap::new();
    for entry in entries {
        let name = entry
            .get("name")
            .and_then(serde_json::Value::as_str)
            .context("GN argument is missing its name")?;
        if name == "gnrt_mode" {
            continue;
        }
        let value = entry
            .get("current")
            .or_else(|| entry.get("default"))
            .and_then(|value| value.get("value"))
            .and_then(serde_json::Value::as_str)
            .with_context(|| format!("GN argument {name} is missing its value"))?;
        values.insert(name.to_owned(), value.to_owned());
    }
    Ok(values)
}

fn declaration_label(declaration: &Declaration) -> &str {
    match declaration {
        Declaration::Crate(d) => &d.label,
        Declaration::Toolchain(d) => &d.label,
    }
}

fn declaration_root(file: &Path) -> Result<String> {
    if file.is_absolute()
        || file
            .components()
            .any(|part| !matches!(part, std::path::Component::Normal(_)))
        || file.file_name() != Some(std::ffi::OsStr::new("BUILD.gn"))
    {
        bail!(
            "declaration file must be a project-relative BUILD.gn: {}",
            file.display()
        );
    }
    let directory = file.parent().context("declaration file has no directory")?;
    Ok(format!(
        "//{}",
        directory.to_string_lossy().replace('\\', "/")
    ))
}

fn extract_catalog(out_dir: &Path, root: &str) -> Result<DeclarationGroups> {
    extract_catalog_kind(out_dir, root, false)
}

fn extract_catalog_kind(out_dir: &Path, root: &str, toolchains: bool) -> Result<DeclarationGroups> {
    let root_arg = format!("--root-target={root}");
    let output = run_gn_with_output(&[
        "desc",
        &path_str(out_dir),
        "*",
        "metadata",
        "--format=json",
        // Wildcards otherwise include declaration copies from other toolchains.
        "--default-toolchain",
        &root_arg,
    ])?;
    let mut declarations = parse_catalog_kind(&output.stdout, root, toolchains)?;
    declarations.cargo = dedupe_cargo(declarations.cargo);
    validate(&declarations)?;
    Ok(declarations)
}

#[cfg(test)]
fn parse_catalog_json(bytes: &[u8], root: &str) -> Result<DeclarationGroups> {
    parse_catalog_kind(bytes, root, false)
}

fn parse_catalog_kind(bytes: &[u8], root: &str, toolchains: bool) -> Result<DeclarationGroups> {
    let targets: BTreeMap<String, serde_json::Value> =
        serde_json::from_slice(bytes).context("gn desc produced invalid metadata JSON")?;
    let mut declarations = Vec::new();
    for (label, target) in targets {
        let directory = label
            .split('(')
            .next()
            .unwrap_or(&label)
            .rsplit_once(':')
            .map(|(dir, _)| dir);
        if directory != Some(root) {
            continue;
        }
        if let Some(values) = target
            .get("metadata")
            .and_then(|m| m.get("gnrt_declarations"))
        {
            let values: Vec<Declaration> = serde_json::from_value(values.clone())
                .with_context(|| format!("invalid gnrt_declarations on {label}"))?;
            declarations.extend(
                values
                    .into_iter()
                    .filter(|d| matches!(d, Declaration::Toolchain(_)) == toolchains),
            );
        }
    }
    Ok(group_by_origin(declarations))
}

/// Returns files consumed by GN, including imports and script dependencies.
///
/// # Errors
/// Returns an error if the generated dependency file is missing or invalid.
pub fn gn_inputs(out_dir: &Path) -> Result<Vec<PathBuf>> {
    let file = out_dir.join("build.ninja.d");
    let contents = std::fs::read_to_string(&file)
        .with_context(|| format!("failed to read GN input dependencies {}", file.display()))?;
    let dependencies = contents
        .split_once(':')
        .context("invalid GN dependency file")?
        .1;
    let mut paths = Vec::new();
    let mut current = String::new();
    let mut escaped = false;
    for ch in dependencies.chars() {
        if escaped {
            if ch != '\n' {
                current.push(ch);
            }
            escaped = false;
        } else if ch == '\\' {
            escaped = true;
        } else if ch.is_whitespace() {
            if !current.is_empty() {
                paths.push(out_dir.join(std::mem::take(&mut current)));
            }
        } else {
            current.push(ch);
        }
    }
    if !current.is_empty() {
        paths.push(out_dir.join(current));
    }
    Ok(paths)
}

#[derive(Serialize)]
struct DeclarationFile<'a> {
    version: u32,
    declarations: &'a DeclarationGroups,
    scopes: &'a [ResolutionScope],
}

/// Writes the collect-stage interface file without adding file metadata to
/// `SyncContext`.
fn write_declarations(
    gnrt_out_dir: &Path,
    declarations: &DeclarationGroups,
    scopes: &[ResolutionScope],
) -> Result<()> {
    crate::util::create_dirs_if_needed(gnrt_out_dir)?;
    let output_path = gnrt_out_dir.join("declarations.json");
    let file = DeclarationFile {
        version: 3,
        declarations,
        scopes,
    };
    let json =
        serde_json::to_string_pretty(&file).context("failed to serialize declarations.json")?;
    std::fs::write(&output_path, json + "\n")
        .with_context(|| format!("failed to write {}", output_path.display()))?;
    println!("wrote {}", output_path.display());
    Ok(())
}

fn join_args(extra: &[String]) -> String {
    let mut joined = String::new();
    for (i, arg) in extra.iter().enumerate() {
        if i > 0 {
            joined.push(' ');
        }
        joined.push_str(arg);
    }
    joined
}

/// Runs `gn gen` for the collection output directory.
fn generate_build_dir(out_dir: &Path, args: &[String], root: Option<&str>) -> Result<()> {
    let arguments = gen_arguments(out_dir, args, root);
    let arguments: Vec<&str> = arguments.iter().map(String::as_str).collect();
    run_gn_with_output(&arguments).map(|_| ())
}

fn gen_arguments(out_dir: &Path, args: &[String], root: Option<&str>) -> Vec<String> {
    let mut collect_args = args.to_vec();
    collect_args.push("gnrt_mode=\"collect\"".to_owned());
    let mut arguments = vec![
        "gen".to_owned(),
        path_str(out_dir),
        format!("--args={}", join_args(&collect_args)),
    ];
    if let Some(root) = root {
        arguments.push(format!("--root-target={root}"));
        if let Some(pattern) = root_pattern(root) {
            arguments.push(pattern);
        }
    }
    arguments
}

/// Returns the `--root-pattern` argument for `root`, or `None` when `gn`
/// invocations must omit it.
///
/// Directory-style roots carry no pattern: `gn` would interpret the pattern
/// with the implicit `:<directory-name>` target and prune the wrong subgraph.
fn root_pattern(root: &str) -> Option<String> {
    root.contains(':').then(|| format!("--root-pattern={root}"))
}

/// Runs `gn meta` and returns the parsed, validated declarations reachable
/// from `entry`.
fn extract_declarations(out_dir: &Path, entry: &str) -> Result<DeclarationGroups> {
    let out = path_str(out_dir);
    let root_target = format!("--root-target={entry}");
    let root_pattern_arg = root_pattern(entry);
    let mut arguments: Vec<&str> = vec![
        "meta",
        &out,
        entry,
        "--data=gnrt_declarations",
        "--walk=",
        &root_target,
    ];
    if let Some(pattern) = &root_pattern_arg {
        arguments.push(pattern);
    }
    let output = run_gn_with_output(&arguments)?;
    let stdout = String::from_utf8(output.stdout).context("gn meta produced non-UTF-8 output")?;
    let mut declarations = parse_gn_meta_output(&stdout)?;
    declarations.cargo = dedupe_cargo(declarations.cargo);
    validate(&declarations)?;
    Ok(declarations)
}

fn path_str(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

/// Runs `gn` with `args` and returns its raw output. The executable comes
/// from `GNRT_GN_BIN` when set, otherwise `PATH`.
fn run_gn_with_output(args: &[&str]) -> Result<Output> {
    let gn = match std::env::var_os("GNRT_GN_BIN") {
        Some(path) => PathBuf::from(path),
        None => which("gn").context("gn not found in PATH (set GNRT_GN_BIN to override)")?,
    };
    let mut cmd = Command::new(gn);
    cmd.args(args);
    let msg = format!("gn {}", args.join(" "));
    let output = cmd
        .output()
        .with_context(|| format!("failed to start {msg}"))?;
    if !output.status.success() {
        bail!(
            "command '{msg}' failed with {}. stdout:\n\n{}\nstderr:\n{}",
            exit_code_text(&output),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(output)
}

fn exit_code_text(output: &Output) -> String {
    match output.status.code() {
        Some(code) => format!("exit code {code}"),
        None => "no exit code".to_owned(),
    }
}

fn which(program: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join(program))
        .find(|candidate| candidate.is_file())
}

/// Parses the output of `gn meta`.
///
/// The output consists of a "Metadata values" section with one GN-scope block
/// per collected declaration, followed by an "Extracted from" section listing
/// the labels that contributed metadata.
///
/// GN may print warnings (e.g. about unused build arguments) to stdout before
/// the metadata section, so the parser locates the "Metadata values" header
/// instead of assuming the output starts with it.
fn parse_gn_meta_output(stdout: &str) -> Result<DeclarationGroups> {
    let body = stdout
        .split_once("\nMetadata values\n")
        .map(|(_, rest)| rest)
        .or_else(|| stdout.strip_prefix("Metadata values\n"))
        .ok_or_else(|| anyhow::format_err!("gn meta output missing 'Metadata values' header"))?;
    let (blocks_text, _) = body
        .split_once("\nExtracted from:\n")
        .ok_or_else(|| anyhow::format_err!("gn meta output missing 'Extracted from' header"))?;

    let mut declarations = Vec::new();
    for block in split_scope_blocks(blocks_text) {
        let scope = parse_scope(&block)
            .with_context(|| format!("failed to parse gn meta block:\n{block}"))?;
        declarations.push(declaration_from_scope(scope)?);
    }

    Ok(group_by_origin(declarations))
}

/// Splits declaration scopes, ignoring braces inside quoted values.
fn split_scope_blocks(text: &str) -> Vec<String> {
    let mut blocks = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;
    for (index, ch) in unquoted_chars(text) {
        match ch {
            '{' => {
                if depth == 0 {
                    start = index;
                }
                depth += 1;
            }
            '}' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    blocks.push(text[start..=index].to_owned());
                }
            }
            _ => {}
        }
    }
    blocks
}

/// Returns characters outside GN string literals for delimiter matching.
fn unquoted_chars(text: &str) -> impl Iterator<Item = (usize, char)> + '_ {
    let mut quoted = false;
    let mut escaped = false;
    text.char_indices().filter(move |(_, ch)| {
        if escaped {
            escaped = false;
            return false;
        }
        if quoted && *ch == '\\' {
            escaped = true;
            return false;
        }
        if *ch == '"' {
            quoted = !quoted;
            return false;
        }
        !quoted
    })
}

fn delimiter_balance(text: &str) -> i32 {
    unquoted_chars(text)
        .map(|(_, ch)| match ch {
            '[' | '{' => 1,
            ']' | '}' => -1,
            _ => 0,
        })
        .sum()
}

type Scope = Vec<(String, ScopeValue)>;

#[derive(Debug)]
enum ScopeValue {
    String(String),
    Bool(bool),
    List(Vec<ScopeValue>),
    Scope(Scope),
}

/// Parses a flat GN scope like `key = value` lines. Nested scopes appear as a
/// multi-line `key = { ... }` block, which is parsed recursively.
fn parse_scope(block: &str) -> Result<Scope> {
    let block = block.trim();
    let inner = block
        .strip_prefix('{')
        .and_then(|b| b.strip_suffix('}'))
        .ok_or_else(|| anyhow::format_err!("not a scope block"))?;

    let mut scope = Vec::new();
    let mut lines = inner.lines().peekable();
    while let Some(line) = lines.next() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let (key, value) = line
            .split_once(" = ")
            .ok_or_else(|| anyhow::format_err!("no '=' in line: {line}"))?;
        if value.trim_start_matches(' ').trim() == "{ }" || value == "{}" {
            scope.push((key.trim().to_owned(), ScopeValue::Scope(Vec::new())));
            continue;
        }
        if value.starts_with("[") {
            // Multi-line list: consume lines until bracket and brace depth
            // both return to zero (a list may contain string items,
            // list-of-scopes items, or a mix). Scope items are then split at
            // the character level (a line may close one scope and open
            // another, e.g. "}, {").
            let mut depth = delimiter_balance(value);
            let mut body = String::from(value);
            if depth > 0 {
                for nested in lines.by_ref() {
                    depth += delimiter_balance(nested);
                    body.push('\n');
                    body.push_str(nested);
                    if depth == 0 {
                        break;
                    }
                }
            }
            let value = parse_value(body.trim())?;
            scope.push((key.trim().to_owned(), value));
            continue;
        }
        if value == "{" {
            // Consume lines until the matching closing brace. Nested scope
            // blocks inside declarations are flat, so one brace of depth
            // suffices; track nesting anyway to stay correct.
            let mut depth = 1usize;
            let mut body = String::new();
            for nested in lines.by_ref() {
                for (_, ch) in unquoted_chars(nested) {
                    match ch {
                        '{' => depth += 1,
                        '}' => depth -= 1,
                        _ => {}
                    }
                }
                if depth == 0 {
                    break;
                }
                body.push_str(nested);
                body.push('\n');
            }
            let block = format!("{{\n{body}}}");
            scope.push((
                key.trim().to_owned(),
                ScopeValue::Scope(parse_scope(&block)?),
            ));
            continue;
        }
        scope.push((key.trim().to_owned(), parse_value(value)?));
    }
    Ok(scope)
}

fn parse_value(value: &str) -> Result<ScopeValue> {
    let value = value.trim();
    if value.starts_with('[') {
        if !value.ends_with(']') {
            bail!("unterminated list: {value}");
        }
        let inner = &value[1..value.len() - 1];
        return Ok(ScopeValue::List(split_list_items(inner)?));
    }
    if value.starts_with('{') {
        return Ok(ScopeValue::Scope(parse_scope(value)?));
    }
    if value == "true" {
        return Ok(ScopeValue::Bool(true));
    }
    if value == "false" {
        return Ok(ScopeValue::Bool(false));
    }
    if value.starts_with('"') {
        return Ok(ScopeValue::String(unquote(value)?));
    }
    bail!("unsupported value: {value}")
}

/// Splits a list body on top-level commas, respecting strings and nested scopes.
fn split_list_items(inner: &str) -> Result<Vec<ScopeValue>> {
    let mut items = Vec::new();
    let mut current = String::new();
    let mut in_string = false;
    let mut escaped = false;
    let mut depth = 0usize;
    for ch in inner.chars() {
        if escaped {
            current.push(ch);
            escaped = false;
            continue;
        }
        match ch {
            '\\' if in_string => {
                current.push(ch);
                escaped = true;
            }
            '"' => {
                in_string = !in_string;
                current.push(ch);
            }
            '[' | '{' if !in_string => {
                depth += 1;
                current.push(ch);
            }
            ']' | '}' if !in_string => {
                depth = depth.checked_sub(1).context("unmatched list delimiter")?;
                current.push(ch);
            }
            ',' if !in_string && depth == 0 => {
                let item = current.trim();
                if !item.is_empty() {
                    items.push(parse_value(item)?);
                }
                current.clear();
            }
            _ => current.push(ch),
        }
    }
    if in_string || depth != 0 {
        bail!("unterminated list item");
    }
    let item = current.trim();
    if !item.is_empty() {
        items.push(parse_value(item)?);
    }
    Ok(items)
}

/// Unquotes a GN string literal. GN escapes are JSON-like, except control
/// characters (tab, newline) are printed raw inside the string, which the
/// per-character handling accepts.
fn unquote(value: &str) -> Result<String> {
    if !(value.starts_with('"') && value.ends_with('"') && value.len() >= 2) {
        bail!("not a quoted string: {value}");
    }
    let inner = &value[1..value.len() - 1];
    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            Some(other) => out.push(other),
            None => bail!("trailing backslash in string: {value}"),
        }
    }
    Ok(out)
}

fn scope_get<'a>(scope: &'a Scope, key: &str) -> Result<&'a ScopeValue> {
    scope
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v)
        .with_context(|| format!("declaration missing field '{key}'"))
}

fn scope_get_opt<'a>(scope: &'a Scope, key: &str) -> Option<&'a ScopeValue> {
    scope.iter().find(|(k, _)| k == key).map(|(_, v)| v)
}

fn as_string(value: &ScopeValue) -> Result<String> {
    match value {
        ScopeValue::String(s) => Ok(s.clone()),
        other => bail!("expected string, got {other:?}"),
    }
}

fn as_bool(value: &ScopeValue) -> Result<bool> {
    match value {
        ScopeValue::Bool(b) => Ok(*b),
        other => bail!("expected bool, got {other:?}"),
    }
}

/// Reads an optional string field, defaulting to empty when absent.
fn optional_string(scope: &Scope, key: &str) -> Result<String> {
    match scope_get_opt(scope, key) {
        Some(v) => as_string(v),
        None => Ok(String::new()),
    }
}

fn as_string_list(value: &ScopeValue) -> Result<Vec<String>> {
    match value {
        ScopeValue::List(items) => items.iter().map(as_string).collect(),
        other => bail!("expected list, got {other:?}"),
    }
}

/// Reads strings and conditional scopes without evaluating their GN expressions.
fn as_configurable_list(value: &ScopeValue) -> Result<Vec<ConfigurableValue>> {
    let ScopeValue::List(items) = value else {
        bail!("expected configurable list, got {value:?}");
    };
    items
        .iter()
        .map(|item| match item {
            ScopeValue::String(value) => Ok(ConfigurableValue::Value(value.clone())),
            ScopeValue::Scope(scope) => {
                for (key, _) in scope {
                    if key != "condition" && key != "values" {
                        bail!("unknown conditional value key '{key}'");
                    }
                }
                Ok(ConfigurableValue::Conditional {
                    condition: as_string(scope_get(scope, "condition")?)?,
                    values: as_string_list(scope_get(scope, "values")?)?,
                })
            }
            other => bail!("expected string or conditional scope, got {other:?}"),
        })
        .collect()
}

fn declaration_from_scope(scope: Scope) -> Result<Declaration> {
    let type_ = as_string(scope_get(&scope, "type")?)?;
    let origin = as_string(scope_get(&scope, "origin")?)?;
    if scope_get_opt(&scope, "conditions").is_some() {
        bail!("put conditional entries inside features or rustflags");
    }
    match (origin.as_str(), type_.as_str()) {
        ("cargo", "crate") => Ok(Declaration::Crate(CrateDeclaration {
            origin,
            label: as_string(scope_get(&scope, "label")?)?,
            package: as_string(scope_get(&scope, "package")?)?,
            version: as_string(scope_get(&scope, "version")?)?,
            features: as_configurable_list(scope_get(&scope, "features")?)?,
            rustflags: match scope_get_opt(&scope, "rustflags") {
                Some(value) => as_configurable_list(value)?,
                None => Vec::new(),
            },
            default_features: as_bool(scope_get(&scope, "default_features")?)?,
            isolation: match scope_get_opt(&scope, "isolation") {
                Some(value) => serde_json::from_value(serde_json::Value::String(as_string(value)?))
                    .context("invalid cargo_spec isolation")?,
                None => Isolation::None,
            },
            patches: as_string_list(scope_get(&scope, "patches")?)?,
            git: optional_string(&scope, "git")?,
            rev: optional_string(&scope, "rev")?,
            branch: optional_string(&scope, "branch")?,
            tag: optional_string(&scope, "tag")?,
        })),
        ("gn", "toolchain") => Ok(Declaration::Toolchain(ToolchainDeclaration {
            origin,
            role: match scope_get_opt(&scope, "role") {
                Some(v) => as_string(v)?,
                None => "target".to_owned(),
            },
            cc: as_string(scope_get(&scope, "cc")?)?,
            cxx: as_string(scope_get(&scope, "cxx")?)?,
            ar: as_string(scope_get(&scope, "ar")?)?,
            rustc: as_string(scope_get(&scope, "rustc")?)?,
            llvm_target: as_string(scope_get(&scope, "llvm_target")?)?,
            target_triple: as_string(scope_get(&scope, "target_triple")?)?,
            label: as_string(scope_get(&scope, "label")?)?,
        })),
        (origin, type_) => {
            bail!("unsupported declaration origin='{origin}' type='{type_}'")
        }
    }
}

fn group_by_origin(declarations: Vec<Declaration>) -> DeclarationGroups {
    let mut cargo = Vec::new();
    let mut gn = Vec::new();
    for declaration in declarations {
        let is_gn = matches!(declaration, Declaration::Toolchain(_));
        if is_gn {
            gn.push(declaration);
        } else {
            cargo.push(declaration);
        }
    }
    DeclarationGroups { cargo, gn }
}

/// Drops repeated crate declarations, keeping the first for each label.
///
/// `gn meta --walk` emits a declaration once per path that reaches it, so a
/// target reachable through several dependents appears more than once.
fn dedupe_cargo(declarations: Vec<Declaration>) -> Vec<Declaration> {
    let mut seen = std::collections::HashSet::new();
    declarations
        .into_iter()
        .filter(|declaration| match declaration {
            Declaration::Crate(d) => seen.insert(d.label.clone()),
            _ => true,
        })
        .collect()
}

/// Minimal validation of required fields. Full validation happens in later
/// sync stages.
fn validate(declarations: &DeclarationGroups) -> Result<()> {
    let mut labels = std::collections::HashSet::new();
    let mut host_labels = BTreeSet::new();
    let all = declarations.cargo.iter().chain(declarations.gn.iter());
    for declaration in all {
        let label = match declaration {
            Declaration::Crate(d) => &d.label,
            Declaration::Toolchain(d) => {
                if d.target_triple.is_empty() {
                    bail!("toolchain declaration has empty target_triple");
                }
                // One BUILD.gn serves every board, so host-context edges can
                // only reference a single host toolchain label.
                if d.role == "host" {
                    host_labels.insert(d.label.clone());
                    ensure!(
                        host_labels.len() == 1,
                        "conflicting host toolchain labels: {}",
                        host_labels.iter().cloned().collect::<Vec<_>>().join(", ")
                    );
                }
                continue;
            }
        };
        if !labels.insert(label.as_str()) {
            bail!("duplicate declaration label: {label}");
        }
        if let Declaration::Crate(crate_) = declaration {
            for value in crate_.features.iter().chain(&crate_.rustflags) {
                if value
                    .condition()
                    .is_some_and(|condition| condition.trim().is_empty())
                {
                    bail!("empty configurable value condition in {label}");
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validate_rejects_conflicting_host_toolchain_labels() {
        let toolchain = |label: &str, role: &str| {
            Declaration::Toolchain(ToolchainDeclaration {
                origin: "//build/toolchain".to_owned(),
                label: label.to_owned(),
                role: role.to_owned(),
                cc: "clang".to_owned(),
                cxx: "clang++".to_owned(),
                ar: "llvm-ar".to_owned(),
                rustc: "rustc".to_owned(),
                llvm_target: "riscv32".to_owned(),
                target_triple: "riscv32imac-unknown-none-elf".to_owned(),
            })
        };
        let same_label = DeclarationGroups {
            gn: vec![
                toolchain("//build/toolchain:host", "host"),
                toolchain("//build/toolchain:host", "host"),
            ],
            ..Default::default()
        };
        assert!(validate(&same_label).is_ok());
        let conflicting = DeclarationGroups {
            gn: vec![
                toolchain("//build/toolchain:host", "host"),
                toolchain("//build/rust:host_x64", "host"),
            ],
            ..Default::default()
        };
        assert!(validate(&conflicting).is_err());
    }

    #[test]
    fn collection_prunes_scoped_graphs_and_keeps_complete_catalogs() {
        let scoped = gen_arguments(Path::new("out"), &[], Some("//apps/shell:shell"));
        assert!(scoped
            .iter()
            .any(|arg| arg == "--root-pattern=//apps/shell:shell"));
        let catalog = gen_arguments(Path::new("out"), &[], Some("//external/rust"));
        assert!(!catalog.iter().any(|arg| arg.starts_with("--root-pattern=")));
    }

    #[test]
    fn root_patterns_match_target_and_directory_entries() {
        assert_eq!(
            root_pattern("//apps/shell:app"),
            Some("--root-pattern=//apps/shell:app".to_owned())
        );
        assert_eq!(root_pattern("//external/rust"), None);
    }

    #[test]
    fn scope_graph_collects_reachable_nested_entries() {
        let graph = serde_json::json!({
            "//app:app": {
                "toolchain": "//toolchain:target",
                "deps": ["//app:library"],
            },
            "//app:library": {
                "toolchain": "//toolchain:target",
                "public_deps": ["//macros:derive(//toolchain:host)"],
            },
            "//macros:derive(//toolchain:host)": {
                "toolchain": "//toolchain:host",
                "data_deps": ["//app:child"],
                "deps": ["//app:library"],
            },
            "//app:child": {
                "toolchain": "//toolchain:target",
                "metadata": {"gnrt_nested_builds": [{
                    "entry": "//app:child_pass",
                    "args": ["product=\"child\""],
                    "inputs": [],
                }]},
            },
            "//app:child_pass": {"toolchain": "//toolchain:target"},
            "//unrelated:unit": {
                "toolchain": "//toolchain:target",
                "deps": ["//missing:target"],
            },
        });
        let nested = parse_scope_graph(&serde_json::to_vec(&graph).unwrap(), "//app:app").unwrap();
        assert_eq!(nested.len(), 1);
        assert_eq!(nested[0].entry, "//app:child_pass");
        assert_eq!(nested[0].args, ["product=\"child\""]);
        let qualified_nested = parse_scope_graph(
            &serde_json::to_vec(&graph).unwrap(),
            "//app(//toolchain:target)",
        )
        .unwrap();
        assert_eq!(qualified_nested.len(), nested.len());
        assert_eq!(qualified_nested[0].entry, nested[0].entry);
        assert_eq!(qualified_nested[0].args, nested[0].args);
    }

    #[test]
    fn scope_graph_rejects_missing_targets_and_invalid_nested_metadata() {
        let mut graph = serde_json::json!({
            "//app:app": {
                "toolchain": "//toolchain:target",
                "deps": ["//missing:target"],
            },
        });
        let error =
            parse_scope_graph(&serde_json::to_vec(&graph).unwrap(), "//app:app").unwrap_err();
        assert!(error.to_string().contains("//missing:target"));
        graph["//app:app"]["deps"] = serde_json::json!([]);
        graph["//app:app"]["metadata"] = serde_json::json!({"gnrt_nested_builds": [{
            "entry": "//child:app",
        }]});
        let error =
            parse_scope_graph(&serde_json::to_vec(&graph).unwrap(), "//app:app").unwrap_err();
        assert!(error.to_string().contains("invalid nested build metadata"));
    }
    use pretty_assertions::assert_eq;

    fn sample_meta_output() -> String {
        [
            "Metadata values",
            "",
            "{",
            "  llvm_target = \"thumbv7m-none-eabi\"",
            "  ar = \"llvm-ar\"",
            "  cc = \"clang --target=x86_64-unknown-linux-gnu\"",
            "  cxx = \"clang++ --target=x86_64-unknown-linux-gnu\"",
            "  label = \"//build/toolchain:blueos_thumbv7m\"",
            "  origin = \"gn\"",
            "  role = \"target\"",
            "  rustc = \"rustc --target=thumbv7m-vivo-blueos\"",
            "  target_triple = \"thumbv7m-vivo-blueos\"",
            "  type = \"toolchain\"",
            "}",
            "",
            "{",
            "  default_features = true",
            "  features = [\"derive\", \"quo\\\"te\\\\\"]",
            "  label = \"//test:test_crate\"",
            "  origin = \"cargo\"",
            "  package = \"serde\"",
            "  patches = []",
            "  type = \"crate\"",
            "  version = \"1.0.219\"",
            "}",
            "",
            "Extracted from:",
            "//:default(//build/toolchain:host)",
            "//test:test_crate(//build/toolchain:host)",
            "",
            "using data keys:",
            "gnrt_declarations",
            "",
        ]
        .join("\n")
    }

    #[test]
    fn parse_groups_and_fields() {
        let declarations = parse_gn_meta_output(&sample_meta_output()).unwrap();
        assert_eq!(declarations.gn.len(), 1);
        assert_eq!(declarations.cargo.len(), 1);

        let Declaration::Toolchain(toolchain) = &declarations.gn[0] else {
            panic!("expected toolchain");
        };
        assert_eq!(toolchain.llvm_target, "thumbv7m-none-eabi");
        assert_eq!(toolchain.role, "target");
        assert_eq!(toolchain.label, "//build/toolchain:blueos_thumbv7m");
        assert_eq!(toolchain.target_triple, "thumbv7m-vivo-blueos");
        assert_eq!(toolchain.cc, "clang --target=x86_64-unknown-linux-gnu");

        let Declaration::Crate(crate_) = &declarations.cargo[0] else {
            panic!("expected crate");
        };
        assert_eq!(crate_.package, "serde");
        assert_eq!(
            crate_
                .features
                .iter()
                .flat_map(ConfigurableValue::values)
                .collect::<Vec<_>>(),
            vec!["derive", "quo\"te\\"]
        );
        assert!(crate_.default_features);
    }

    #[test]
    fn isolation_defaults_and_rejects_unknown_modes() {
        for (mode, expected) in [
            ("none", Isolation::None),
            ("root", Isolation::Root),
            ("closure", Isolation::Closure),
        ] {
            let output = sample_meta_output().replace(
                "  default_features = true",
                &format!("  default_features = true\n  isolation = {mode:?}"),
            );
            let declarations = parse_gn_meta_output(&output).unwrap();
            let Declaration::Crate(declaration) = &declarations.cargo[0] else {
                unreachable!()
            };
            assert_eq!(declaration.isolation, expected);
            let json = serde_json::to_value(&declaration).unwrap();
            assert_eq!(json["isolation"], mode);
            assert_eq!(
                serde_json::from_value::<CrateDeclaration>(json).unwrap(),
                *declaration
            );
        }
        let declarations = parse_gn_meta_output(&sample_meta_output()).unwrap();
        let Declaration::Crate(declaration) = &declarations.cargo[0] else {
            unreachable!()
        };
        assert_eq!(declaration.isolation, Isolation::None);
        for mode in ["true", "\"invalid\"", "[\"root\"]"] {
            let output = sample_meta_output().replace(
                "  default_features = true",
                &format!("  default_features = true\n  isolation = {mode}"),
            );
            assert!(parse_gn_meta_output(&output).is_err());
        }
    }

    #[test]
    fn catalog_toolchains_keep_compiler_commands() {
        let metadata = serde_json::json!({
            "//build/toolchain:custom_metadata": {"metadata": {"gnrt_declarations": [{
                "type": "toolchain", "origin": "gn", "label": "//build/toolchain:custom",
                "role": "target", "cc": "clang", "cxx": "clang++", "ar": "llvm-ar",
                "rustc": "rustc --target=custom -Ctarget-feature=+m",
                "target_triple": "custom", "llvm_target": "riscv32"
            }]}}
        });
        let declarations = parse_catalog_kind(
            &serde_json::to_vec(&metadata).unwrap(),
            "//build/toolchain",
            true,
        )
        .unwrap();
        assert!(declarations.cargo.is_empty());
        let Declaration::Toolchain(toolchain) = &declarations.gn[0] else {
            unreachable!()
        };
        assert_eq!(toolchain.rustc, "rustc --target=custom -Ctarget-feature=+m");
        assert!(
            parse_catalog_json(&serde_json::to_vec(&metadata).unwrap(), "//build/toolchain")
                .unwrap()
                .cargo
                .is_empty()
        );
    }

    #[test]
    fn parse_rejects_missing_field() {
        let output = sample_meta_output().replace("  label = \"//test:test_crate\"\n", "");
        let err = parse_gn_meta_output(&output).unwrap_err();
        assert!(err.to_string().contains("missing field 'label'"));
    }

    #[test]
    fn parse_rejects_toolchain_without_label() {
        let output =
            sample_meta_output().replace("  label = \"//build/toolchain:blueos_thumbv7m\"\n", "");
        let err = parse_gn_meta_output(&output).unwrap_err();
        assert!(err.to_string().contains("missing field 'label'"));
    }

    #[test]
    fn parse_rejects_unknown_type() {
        let output = sample_meta_output().replace("type = \"crate\"", "type = \"other\"");
        let err = parse_gn_meta_output(&output).unwrap_err();
        assert!(err.to_string().contains("unsupported declaration"));
    }

    #[test]
    fn parse_rejects_manifest_declaration() {
        let output = sample_meta_output().replace("type = \"crate\"", "type = \"manifest\"");
        let err = parse_gn_meta_output(&output).unwrap_err();
        assert!(err.to_string().contains("unsupported declaration"));
    }

    #[test]
    fn parse_crate_without_git_fields_defaults_to_empty() {
        let declarations = parse_gn_meta_output(&sample_meta_output()).unwrap();
        let Declaration::Crate(crate_decl) = &declarations.cargo[0] else {
            panic!("expected crate");
        };
        assert_eq!(crate_decl.git, "");
        assert_eq!(crate_decl.rev, "");
        assert_eq!(crate_decl.branch, "");
        assert_eq!(crate_decl.tag, "");
        assert!(crate_decl.rustflags.is_empty());
    }

    #[test]
    fn parse_crate_rustflags_preserves_order_and_rejects_non_strings() {
        let flags = ["--cfg", "custom=\"value with spaces\""];
        let output = sample_meta_output().replace(
            "  package = \"serde\"",
            &format!(
                "  package = \"serde\"\n  rustflags = {}",
                serde_json::to_string(&flags).unwrap()
            ),
        );
        let declarations = parse_gn_meta_output(&output).unwrap();
        let Declaration::Crate(declaration) = &declarations.cargo[0] else {
            panic!("expected crate");
        };
        assert_eq!(
            declaration
                .rustflags
                .iter()
                .flat_map(ConfigurableValue::values)
                .collect::<Vec<_>>(),
            flags.iter().collect::<Vec<_>>()
        );
        let invalid = output.replace(&serde_json::to_string(&flags).unwrap(), "[\"--cfg\", true]");
        assert!(parse_gn_meta_output(&invalid).is_err());
    }

    #[test]
    fn configurable_lists_preserve_order_in_meta_and_json() {
        let features = r#"["alloc", {
          condition = "board == \"foo\""
          values = [ "extra", "other" ]
        }]"#;
        let flags = r#"["--cfg=base", "--cfg=quoted=\"},[\"", {
          condition = "board == \"foo\""
          values = [ "--cfg=extra", "-Copt-level=2" ]
        }, "-Copt-level=3"]"#;
        let output = sample_meta_output()
            .replace(
                sample_meta_output()
                    .lines()
                    .find(|line| line.starts_with("  features ="))
                    .unwrap(),
                &format!("  features = {features}"),
            )
            .replace(
                "  package = \"serde\"",
                &format!("  package = \"serde\"\n  rustflags = {flags}"),
            );
        let groups = parse_gn_meta_output(&output).unwrap();
        let Declaration::Crate(declaration) = &groups.cargo[0] else {
            panic!("expected crate")
        };
        assert_eq!(declaration.features.len(), 2);
        assert_eq!(
            declaration.features[0],
            ConfigurableValue::Value("alloc".into())
        );
        assert_eq!(
            declaration.features[1].condition(),
            Some("board == \"foo\"")
        );
        assert_eq!(declaration.features[1].values(), ["extra", "other"]);
        assert_eq!(declaration.rustflags.len(), 4);
        assert_eq!(
            declaration.rustflags[2].values(),
            ["--cfg=extra", "-Copt-level=2"]
        );
        assert_eq!(declaration.rustflags[3].values(), ["-Copt-level=3"]);
        let document = serde_json::json!({"//test:test_crate": {"metadata": {"gnrt_declarations": groups.cargo}}});
        let json_groups =
            parse_catalog_json(&serde_json::to_vec(&document).unwrap(), "//test").unwrap();
        assert_eq!(json_groups.cargo, groups.cargo);
    }

    #[test]
    fn configurable_lists_reject_malformed_entries() {
        for item in [
            "true",
            r#"{ values = [ "extra" ] }"#,
            r#"{ condition = "true" }"#,
            "{\n condition = \"true\"\n values = [true]\n}",
            "{\n condition = \"true\"\n values = []\n unexpected = \"bad\"\n}",
        ] {
            let scope = parse_scope(&format!("{{\n features = [{item}]\n}}"));
            assert!(
                scope
                    .and_then(|scope| as_configurable_list(scope_get(&scope, "features")?))
                    .is_err(),
                "{item}"
            );
        }
        for item in [
            serde_json::json!(true),
            serde_json::json!({"values": ["extra"]}),
            serde_json::json!({"condition": "true"}),
            serde_json::json!({"condition": "true", "values": [true]}),
            serde_json::json!({"condition": "true", "values": [], "unexpected": "bad"}),
        ] {
            assert!(serde_json::from_value::<ConfigurableValue>(item).is_err());
        }
        let mut declarations = parse_gn_meta_output(&sample_meta_output()).unwrap();
        let Declaration::Crate(crate_) = &mut declarations.cargo[0] else {
            panic!("expected crate");
        };
        crate_.features.push(ConfigurableValue::Conditional {
            condition: " ".to_owned(),
            values: Vec::new(),
        });
        assert!(validate(&declarations).is_err());
    }

    #[test]
    fn parse_crate_with_git_source() {
        let crate_block = [
            "{",
            "  default_features = false",
            "  features = []",
            "  git = \"https://github.com/mattnenterprise/rust-ftp\"",
            "  label = \"//test:git_crate\"",
            "  origin = \"cargo\"",
            "  package = \"ftp\"",
            "  patches = []",
            "  rev = \"abc123\"",
            "  type = \"crate\"",
            "  version = \"3.0.1\"",
            "}",
            "",
        ]
        .join("\n");
        let sample = sample_meta_output();
        let (head, tail) = sample.split_once("\nExtracted from:\n").unwrap();
        let output = format!("{}\n{}\nExtracted from:\n{}", head, crate_block, tail);
        let declarations = parse_gn_meta_output(&output).unwrap();
        let Declaration::Crate(crate_decl) = &declarations.cargo[1] else {
            panic!("expected crate");
        };
        assert_eq!(
            crate_decl.git,
            "https://github.com/mattnenterprise/rust-ftp"
        );
        assert_eq!(crate_decl.rev, "abc123");
        assert_eq!(crate_decl.branch, "");
        assert_eq!(crate_decl.tag, "");
    }

    #[test]
    fn parse_rejects_duplicate_label() {
        let crate_block = [
            "{",
            "  default_features = true",
            "  features = [\"derive\", \"quo\\\"te\\\\\"]",
            "  label = \"//test:test_crate\"",
            "  origin = \"cargo\"",
            "  package = \"serde\"",
            "  patches = []",
            "  type = \"crate\"",
            "  version = \"1.0.219\"",
            "}",
            "",
        ]
        .join("\n");
        let output = sample_meta_output().replace(&crate_block, &crate_block.repeat(2));
        let declarations = parse_gn_meta_output(&output).unwrap();
        let err = validate(&declarations).unwrap_err();
        assert!(err.to_string().contains("duplicate declaration label"));
    }

    #[test]
    fn parse_rejects_missing_header() {
        let err = parse_gn_meta_output("garbage").unwrap_err();
        assert!(err.to_string().contains("Metadata values"));
    }

    #[test]
    fn declaration_serializes_with_type_tag() {
        let declarations = parse_gn_meta_output(&sample_meta_output()).unwrap();
        let json = serde_json::to_value(&declarations).unwrap();
        assert_eq!(json["gn"][0]["type"], "toolchain");
        assert_eq!(json["cargo"][0]["type"], "crate");
        // origin is retained inside the entries
        assert_eq!(json["cargo"][0]["origin"], "cargo");
    }

    #[test]
    fn declaration_groups_json_shape() {
        let declarations = parse_gn_meta_output(&sample_meta_output()).unwrap();
        let json = serde_json::to_value(&declarations).unwrap();
        assert!(json["cargo"].is_array());
        assert!(json["gn"].is_array());
    }

    #[test]
    fn registration_rejects_paths_outside_project_and_other_filenames() {
        for path in [
            "/tmp/BUILD.gn",
            "../BUILD.gn",
            "external/../BUILD.gn",
            "external/crates.gni",
        ] {
            assert!(declaration_root(Path::new(path)).is_err(), "{path}");
        }
        assert_eq!(
            declaration_root(Path::new("external/rust/BUILD.gn")).unwrap(),
            "//external/rust"
        );
    }

    #[test]
    fn catalog_collects_unreferenced_targets_and_resets_stale_arguments() {
        let gn = std::env::var_os("GNRT_GN_BIN")
            .map(PathBuf::from)
            .or_else(|| which("gn"));
        let Some(gn) = gn else { return };
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path();
        std::fs::create_dir(root.join("catalog")).unwrap();
        std::fs::create_dir(root.join("tools")).unwrap();
        std::fs::create_dir(root.join("out")).unwrap();
        std::fs::write(root.join(".gn"), "buildconfig = \"//config.gn\"\n").unwrap();
        std::fs::write(
            root.join("config.gn"),
            r#"
            declare_args() {
                gnrt_mode = "build"
                stale = false
            }
            assert(gnrt_mode == "collect")
            assert(!stale)
            set_default_toolchain("//tools:host")
        "#,
        )
        .unwrap();
        std::fs::write(
            root.join("tools/BUILD.gn"),
            r#"
            toolchain("host") {
                tool("stamp") { command = "touch {{output}}" }
            }
        "#,
        )
        .unwrap();
        let fields = format!(
            r#"
            type = "crate"
            origin = "cargo"
            label = "//catalog:unreferenced"
            package = "{}"
            version = "{}"
            features = []
            default_features = true
            git = ""
            rev = ""
            branch = ""
            tag = ""
            patches = []
        "#,
            "serde", "1.0.219"
        );
        std::fs::write(root.join("catalog/BUILD.gn"), format!(
            "group(\"unreferenced\") {{ metadata = {{ gnrt_declarations = [ {{ {fields} }} ] }} }}")).unwrap();
        std::fs::write(root.join("out/args.gn"), "stale = true\n").unwrap();
        let output = Command::new(&gn)
            .current_dir(root)
            .args(gen_arguments(Path::new("out"), &[], Some("//catalog")))
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&gn)
            .current_dir(root)
            .args([
                "desc",
                "out",
                "*",
                "metadata",
                "--format=json",
                "--default-toolchain",
                "--root-target=//catalog",
            ])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
        let catalog = parse_catalog_json(&output.stdout, "//catalog").unwrap();
        assert_eq!(catalog.cargo.len(), 1);
        assert_eq!(
            declaration_label(&catalog.cargo[0]),
            "//catalog:unreferenced"
        );
        assert!(gn_inputs(&root.join("out"))
            .unwrap()
            .iter()
            .any(|path| path.canonicalize().unwrap()
                == root.join("catalog/BUILD.gn").canonicalize().unwrap()));
    }
    #[test]
    fn effective_arguments_include_defaults_and_overrides() {
        let values = parse_effective_args(
            br#"[
            {"name":"board","current":{"value":"\"example\""},"default":{"value":"\"none\""}},
            {"name":"build_type","default":{"value":"\"debug\""}},
            {"name":"gnrt_mode","current":{"value":"\"collect\""}}
        ]"#,
        )
        .unwrap();
        assert_eq!(
            values,
            BTreeMap::from([
                ("board".to_owned(), "\"example\"".to_owned()),
                ("build_type".to_owned(), "\"debug\"".to_owned()),
            ])
        );
    }

    #[test]
    fn catalog_excludes_declarations_from_loaded_dependencies() {
        let declaration = parse_gn_meta_output(&sample_meta_output())
            .unwrap()
            .cargo
            .remove(0);
        let declaration_json = serde_json::to_value(declaration).unwrap();
        let target = serde_json::json!({"metadata":{"gnrt_declarations":[declaration_json]}});
        let document = serde_json::json!({
            "//catalog:direct": target,
            "//catalog/nested:unregistered": target,
            "//elsewhere:dependency": target,
        });
        let catalog =
            parse_catalog_json(&serde_json::to_vec(&document).unwrap(), "//catalog").unwrap();
        assert_eq!(catalog.cargo.len(), 1);
    }
}
