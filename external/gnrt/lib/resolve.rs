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

//! Assembles a temporary Cargo workspace from the collected declarations
//! and vendors third-party crate sources.
//!
//! Declarations share feature closures unless explicitly isolated. Version
//! policy uses the full catalog, while source preparation uses only the selected
//! declarations.

use crate::collect::{
    ConfigurableValue, CrateDeclaration, Declaration, DeclarationGroups, Isolation,
};
use crate::config::BuildConfig;
use crate::deps::{self, DependencyKind};
use crate::group::Group;
use crate::package::{
    ConditionAtom, Dependency, FeatureGroup, Package, Removal, ResolutionContext, SymbolicCondition,
};
use crate::paths::GnrtPaths;
pub use crate::sync_context::{CrateInfo, SyncContext};
use crate::util::exit_code_text;
use anyhow::{bail, ensure, Context, Result};
use guppy::graph::feature::{FeatureEdge, FeatureId, FeatureLabel, FeatureSet};
use guppy::graph::{DependencyDirection, PackageGraph};
use guppy::platform::PlatformStatus;
use semver::Version;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Path, PathBuf};

#[path = "resolve_oracle.rs"]
mod oracle;

/// Returns a `git` command resolved from `PATH`.
fn git_command() -> Result<std::process::Command> {
    let git = which("git").context("git not found in PATH")?;
    Ok(std::process::Command::new(git))
}

fn git_command_in(cwd: &Path) -> Result<std::process::Command> {
    let directory = cwd
        .canonicalize()
        .with_context(|| format!("resolving Git working directory {}", cwd.display()))?;
    let ceiling = directory
        .parent()
        .context("Git working directory has no parent")?;
    let mut command = git_command()?;
    // Parent repositories make git apply silently skip crate-relative paths.
    command
        .current_dir(&directory)
        .env_remove("GIT_DIR")
        .env_remove("GIT_WORK_TREE")
        .env("GIT_CEILING_DIRECTORIES", ceiling);
    Ok(command)
}

/// Runs `git` with `args` in `cwd` and returns its stdout.
fn run_git_with_output(cwd: &Path, args: &[&str]) -> Result<String> {
    let mut cmd = git_command_in(cwd)?;
    cmd.args(args);
    let msg = format!("git {}", args.join(" "));
    log::debug!("running: {msg} in {}", cwd.display());
    let output = cmd
        .output()
        .with_context(|| format!("failed to start `{msg}`"))?;
    if !output.status.success() {
        bail!(
            "command `{msg}` failed with {}. stdout:\n\n{}\nstderr:\n\n{}",
            exit_code_text(&output.status),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    String::from_utf8(output.stdout).context("command produced non-UTF-8 output")
}

/// Returns the cargo binary to invoke: `GNRT_CARGO_BIN` if set, else `cargo`
/// from PATH.
fn cargo_bin() -> Result<PathBuf> {
    match std::env::var_os("GNRT_CARGO_BIN") {
        Some(path) => Ok(PathBuf::from(path)),
        None => which("cargo").context("cargo not found in PATH (set GNRT_CARGO_BIN to override)"),
    }
}

/// Runs `cargo` with `args` in `workspace_dir`, returning stdout while
/// forwarding progress and errors from stderr to the terminal.
fn run_cargo_capture_stdout(workspace_dir: &Path, args: &[&str]) -> Result<String> {
    let cargo = cargo_bin()?;
    let mut cmd = std::process::Command::new(cargo);
    cmd.args(args)
        .current_dir(workspace_dir)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::inherit());
    let msg = format!("cargo {}", args.join(" "));
    log::debug!("running: {msg} in {}", workspace_dir.display());
    let output = cmd
        .output()
        .with_context(|| format!("failed to start `{msg}`"))?;
    if !output.status.success() {
        bail!(
            "command `{msg}` failed with {}",
            exit_code_text(&output.status)
        );
    }
    String::from_utf8(output.stdout).context("command produced non-UTF-8 output")
}

fn run_cargo_vendor(workspace_dir: &Path, args: &[&str]) -> Result<String> {
    let cargo = cargo_bin()?;
    let mut cmd = std::process::Command::new(cargo);
    cmd.args(args)
        .current_dir(workspace_dir)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let msg = format!("cargo {}", args.join(" "));
    log::debug!("running: {msg} in {}", workspace_dir.display());
    let mut child = cmd
        .spawn()
        .with_context(|| format!("failed to start `{msg}`"))?;
    let stderr = child
        .stderr
        .take()
        .context("cargo stderr was not captured")?;
    let stderr_thread = std::thread::spawn(move || forward_stderr_without_vendor_hint(stderr));
    let output = child
        .wait_with_output()
        .with_context(|| format!("failed to wait for `{msg}`"))?;
    stderr_thread
        .join()
        .map_err(|_| anyhow::anyhow!("failed to forward cargo stderr"))??;
    if !output.status.success() {
        bail!(
            "command `{msg}` failed with {}",
            exit_code_text(&output.status)
        );
    }
    String::from_utf8(output.stdout).context("command produced non-UTF-8 output")
}

fn forward_stderr_without_vendor_hint(mut stderr: impl std::io::Read) -> std::io::Result<()> {
    use std::io::Write;

    const HINT: &[u8] =
        b"To use vendored sources, add this to your .cargo/config.toml for this project:";

    let mut terminal = std::io::stderr().lock();
    let mut pending = Vec::new();
    let mut buffer = [0; 4096];
    loop {
        let read = stderr.read(&mut buffer)?;
        if read == 0 {
            terminal.write_all(&pending)?;
            return terminal.flush();
        }
        pending.extend_from_slice(&buffer[..read]);
        if let Some(position) = pending
            .windows(HINT.len())
            .position(|window| window == HINT)
        {
            terminal.write_all(&pending[..position])?;
            return terminal.flush();
        }
        let keep = HINT.len() - 1;
        if pending.len() > keep {
            let ready = pending.len() - keep;
            terminal.write_all(&pending[..ready])?;
            pending.drain(..ready);
            terminal.flush()?;
        }
    }
}

fn which(program: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|dir| dir.join(program))
        .find(|candidate| candidate.is_file())
}

/// Resolves canonical versions and vendors the requested declaration closures.
///
/// Returns the full-catalog lockfile snapshot for transactional publication.
///
/// # Errors
///
/// Returns an error if the build config or lockfile path cannot be resolved,
/// the temporary workspace or crate metadata cannot be written, Cargo resolution
/// or vendoring fails, a patch cannot be applied, or the final lockfile diverges
/// from canonical versions.
pub fn resolve(
    context: &mut SyncContext,
    paths: &dyn GnrtPaths,
    gnrt_out_dir: &Path,
) -> Result<String> {
    let root = paths.root();
    let config = BuildConfig::from_path(paths.third_party_config_file())?;
    let workspace_dir = gnrt_out_dir.join("resolve_workspace");
    let vendor_dir = root.join(paths.third_party());
    let lockfile = config.resolve.cargo_lockfile_path(root)?;

    let catalog = crate_decls_of(&context.catalog);
    validate_patch_policies(&catalog)?;
    let selected = crate_decls_of(&context.declarations);
    let workspace_lockfile = workspace_dir.join("Cargo.lock");

    assemble_workspace(&workspace_dir, &catalog)?;
    seed_workspace_lockfile(&lockfile, &workspace_dir)?;
    if workspace_lockfile.exists() {
        run_cargo_capture_stdout(&workspace_dir, &["update", "--workspace"])?;
    } else {
        run_cargo_capture_stdout(&workspace_dir, &["generate-lockfile"])?;
    }
    // The baseline must survive subsequent changes to the workspace lockfile.
    let canonical_lockfile = fs::read_to_string(&workspace_lockfile)
        .with_context(|| format!("reading {}", workspace_lockfile.display()))?;

    if selected != catalog {
        assemble_workspace(&workspace_dir, &selected)?;
        write_file(&workspace_lockfile, &canonical_lockfile)?;
        // Removing synthetic roots changes the lockfile's workspace section.
        run_cargo_capture_stdout(&workspace_dir, &["update", "--workspace"])?;
    }
    validate_subset_lockfile(&canonical_lockfile, &workspace_lockfile)?;

    vendor_crates(root, &workspace_dir, &vendor_dir, &catalog)?;
    apply_config_patches(root, &vendor_dir, &config)?;
    context.crates =
        resolve_graph_and_crates(&context.declarations, root, &workspace_dir, &config)?.1;

    validate_subset_lockfile(&canonical_lockfile, &workspace_lockfile)?;
    write_crates_info(gnrt_out_dir, context)?;
    Ok(canonical_lockfile)
}

/// Seeds the temporary workspace with the configured lockfile when it exists.
/// A missing lockfile is allowed so Cargo can resolve a new dependency set.
fn seed_workspace_lockfile(lockfile: &Path, workspace_dir: &Path) -> Result<()> {
    if !lockfile.exists() {
        return Ok(());
    }
    if !lockfile.is_file() {
        bail!("lockfile {} is not a file", lockfile.display());
    }
    let destination = workspace_dir.join("Cargo.lock");
    fs::copy(lockfile, &destination).with_context(|| {
        format!(
            "copying {} to {}",
            lockfile.display(),
            destination.display()
        )
    })?;
    Ok(())
}

/// Copies the resolved `Cargo.lock` back to the configured location.
#[cfg(test)]
fn write_back_lockfile(lockfile: &Path, workspace_dir: &Path) -> Result<()> {
    let source = workspace_dir.join("Cargo.lock");
    if !source.is_file() {
        bail!("resolved lockfile {} not found", source.display());
    }
    if let Some(parent) = lockfile.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    fs::copy(&source, lockfile)
        .with_context(|| format!("writing resolved lockfile back to {}", lockfile.display()))?;
    log::info!("wrote resolved lockfile to {}", lockfile.display());
    Ok(())
}

/// Verifies that a subset lock retains canonical identities and dependency edges.
fn validate_subset_lockfile(canonical: &str, subset: &Path) -> Result<()> {
    type Identity = (String, String, String);
    fn packages(contents: &str) -> Result<BTreeMap<Identity, toml::Value>> {
        let parsed: toml::Value = toml::from_str(contents)?;
        let entries = parsed
            .get("package")
            .and_then(toml::Value::as_array)
            .context("Cargo.lock lacks package entries")?;
        let mut result = BTreeMap::new();
        for entry in entries {
            let source = entry
                .get("source")
                .and_then(toml::Value::as_str)
                .unwrap_or("");
            if source.is_empty() {
                continue;
            }
            let name = entry
                .get("name")
                .and_then(toml::Value::as_str)
                .context("package name missing")?;
            let version = entry
                .get("version")
                .and_then(toml::Value::as_str)
                .context("package version missing")?;
            result.insert(
                (name.to_owned(), version.to_owned(), source.to_owned()),
                entry.clone(),
            );
        }
        Ok(result)
    }
    fn dependencies(
        entry: &toml::Value,
        packages: &BTreeMap<Identity, toml::Value>,
    ) -> Result<BTreeSet<Identity>> {
        let mut result = BTreeSet::new();
        for dependency in entry
            .get("dependencies")
            .and_then(toml::Value::as_array)
            .into_iter()
            .flatten()
        {
            let text = dependency.as_str().context("invalid lockfile dependency")?;
            let fields: Vec<_> = text.splitn(3, ' ').collect();
            let matches: Vec<_> = packages
                .keys()
                .filter(|(name, version, source)| {
                    name == fields[0]
                        && (fields.len() < 2 || version == fields[1])
                        && (fields.len() < 3
                            || source == fields[2].trim_start_matches('(').trim_end_matches(')'))
                })
                .cloned()
                .collect();
            if matches.len() != 1 {
                bail!("ambiguous or missing lockfile dependency {text}");
            }
            result.insert(matches[0].clone());
        }
        Ok(result)
    }
    let canonical = packages(canonical)?;
    let mut sources = BTreeMap::new();
    for (name, version, source) in canonical.keys() {
        if let Some(previous) = sources.insert((name, version), source) {
            if previous != source {
                bail!("{name} {version} has multiple sources and would collide in the shared vendor directory");
            }
        }
    }
    let subset = packages(&fs::read_to_string(subset)?)?;
    for (identity, entry) in &subset {
        let locked = canonical
            .get(identity)
            .with_context(|| format!("subset resolved noncanonical package {identity:?}"))?;
        if entry.get("checksum") != locked.get("checksum") {
            bail!("checksum differs from canonical lock for {identity:?}");
        }
        let expected = dependencies(locked, &canonical)?;
        if !dependencies(entry, &subset)?.is_subset(&expected) {
            bail!("dependency resolution differs from canonical lock for {identity:?}");
        }
    }
    Ok(())
}

#[derive(Serialize)]
struct CratesInfoFile<'a> {
    version: u32,
    crates: &'a BTreeMap<String, CrateInfo>,
}

/// Serializes the dependency model to `<gnrt_out_dir>/crates-info.json`.
fn write_crates_info(gnrt_out_dir: &Path, context: &SyncContext) -> Result<()> {
    let file = CratesInfoFile {
        version: 3,
        crates: &context.crates,
    };
    let json = serde_json::to_string_pretty(&file).context("serializing crates-info.json")?;
    write_file(&gnrt_out_dir.join("crates-info.json"), &json)
}

/// Recreates `workspace_dir` with one synthetic package per declaration label.
fn assemble_workspace(workspace_dir: &Path, crates: &[&CrateDeclaration]) -> Result<()> {
    if workspace_dir.exists() {
        fs::remove_dir_all(workspace_dir)
            .with_context(|| format!("removing {}", workspace_dir.display()))?;
    }
    fs::create_dir_all(workspace_dir)
        .with_context(|| format!("creating {}", workspace_dir.display()))?;

    validate_unique_crate_declarations(crates)?;
    let mut members = Vec::new();
    for declaration in crates {
        let member = instance_directory(&declaration.label, &declaration.version);
        write_synthetic_manifest(workspace_dir, &member, &[declaration])?;
        members.push(member);
    }

    // Deterministic member order keeps the generated root manifest stable.
    members.sort();

    write_root_manifest(workspace_dir, &members)
}

/// Writes a synthetic package for a spec-only module. Cargo requires at
/// least one target per package; these packages only drive resolution and
/// are never compiled.
fn write_synthetic_manifest(
    workspace_dir: &Path,
    module: &str,
    decls: &[&CrateDeclaration],
) -> Result<()> {
    validate_unique_crate_declarations(decls)?;
    let member_dir = workspace_dir.join(module);
    fs::create_dir_all(member_dir.join("src"))
        .with_context(|| format!("creating {}", member_dir.display()))?;
    write_file(&member_dir.join("src").join("lib.rs"), "")?;

    let mut manifest = format!(
        "[package]\nname = \"{}\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n\
         [dependencies]\n",
        package_name_for(module)
    );
    for decl in decls {
        manifest.push_str(&dependency_line(decl));
        manifest.push('\n');
    }
    write_file(&member_dir.join("Cargo.toml"), &manifest)
}

/// Derives a unique package name from a module path (`kernel/driver` ->
/// `kernel_driver`).
fn package_name_for(module: &str) -> String {
    module.replace(['/', '-'], "_")
}

/// Writes the workspace root manifest listing all member packages.
fn write_root_manifest(workspace_dir: &Path, members: &[String]) -> Result<()> {
    let mut root = String::from("[workspace]\nresolver = \"2\"\nmembers = [\n");
    for member in members {
        root.push_str(&format!("    \"{member}\",\n"));
    }
    root.push_str("]\n");
    write_file(&workspace_dir.join("Cargo.toml"), &root)
}

/// Rejects repeated declaration labels; different labels isolate features.
fn validate_unique_crate_declarations(crates: &[&CrateDeclaration]) -> Result<()> {
    let mut labels = BTreeSet::new();
    for declaration in crates {
        if !labels.insert(&declaration.label) {
            bail!("duplicate cargo_spec label {}", declaration.label);
        }
    }
    Ok(())
}

// Declarations with the same package, version, Git URL, and Git ref must use
// identical patches. A leading `=` is ignored when comparing versions.
fn validate_patch_policies(crates: &[&CrateDeclaration]) -> Result<()> {
    let mut policies = BTreeMap::new();
    for declaration in crates {
        let identity = (
            &declaration.package,
            declaration.version.trim_start_matches('='),
            &declaration.git,
            &declaration.rev,
            &declaration.branch,
            &declaration.tag,
        );
        if let Some(previous) = policies.insert(identity, &declaration.patches) {
            if previous != &declaration.patches {
                bail!(
                    "declarations of {} {} have conflicting source patches",
                    declaration.package,
                    declaration.version
                );
            }
        }
    }
    Ok(())
}

/// Returns a readable, deterministic directory identity for a declaration
/// label and version.
pub fn instance_directory(label: &str, version: &str) -> String {
    let readable_slug = |value: &str, limit: usize| {
        value
            .split(|character: char| !character.is_ascii_alphanumeric())
            .filter(|part| !part.is_empty())
            .collect::<Vec<_>>()
            .join("_")
            .to_ascii_lowercase()
            .chars()
            .take(limit)
            .collect::<String>()
    };
    let readable_label = readable_slug(label, 32);
    let readable_version = match readable_slug(version, 16).as_str() {
        "" => "unspecified".to_owned(),
        version => version.to_owned(),
    };
    let hash = format!("{:x}", Sha256::digest(label.as_bytes()));
    format!("gnrt_{readable_label}_{readable_version}_{}", &hash[..16])
}

fn crate_decls_of(declarations: &DeclarationGroups) -> Vec<&CrateDeclaration> {
    declarations
        .cargo
        .iter()
        .filter_map(|declaration| match declaration {
            Declaration::Crate(declaration) => Some(declaration),
            _ => None,
        })
        .collect()
}

/// Renders a `[dependencies]` entry line for a crate declaration.
fn dependency_line(declaration: &CrateDeclaration) -> String {
    let mut parts = Vec::new();
    let version = declaration.version.as_str();
    if declaration.git.is_empty() {
        parts.push(format!("version = \"{version}\""));
    } else {
        parts.push(format!("git = \"{}\"", declaration.git));
        if !declaration.rev.is_empty() {
            parts.push(format!("rev = \"{}\"", declaration.rev));
        }
        if !declaration.branch.is_empty() {
            parts.push(format!("branch = \"{}\"", declaration.branch));
        }
        if !declaration.tag.is_empty() {
            parts.push(format!("tag = \"{}\"", declaration.tag));
        }
        parts.push(format!("version = \"{version}\""));
    }
    if !declaration.default_features {
        parts.push("default-features = false".to_owned());
    }
    // Conditions gate features on GN expressions, which Cargo cannot
    // evaluate; union their features with the declared ones so every
    // variant's optional dependencies are vendored and resolved. The GN
    // expressions are re-applied verbatim by the generate stage.
    let features: BTreeSet<&str> = declaration
        .features
        .iter()
        .flat_map(ConfigurableValue::values)
        .map(String::as_str)
        .collect();
    if !features.is_empty() {
        let rendered = features
            .iter()
            .map(|f| format!("\"{f}\""))
            .collect::<Vec<_>>()
            .join(", ");
        parts.push(format!("features = [{rendered}]"));
    }
    format!("{} = {{ {} }}", declaration.package, parts.join(", "))
}

/// Runs `cargo vendor` into `vendor_dir`, applies each crate declaration's
/// patches to its vendored source directory, then writes a cargo config
/// pointing every registry and git source at the vendored directory so later
/// commands resolve offline.
fn vendor_crates(
    root: &Path,
    workspace_dir: &Path,
    vendor_dir: &Path,
    catalog: &[&CrateDeclaration],
) -> Result<()> {
    fs::create_dir_all(vendor_dir).with_context(|| format!("creating {}", vendor_dir.display()))?;
    let vendor_arg = vendor_dir
        .to_str()
        .with_context(|| format!("non-UTF-8 vendor dir {}", vendor_dir.display()))?;
    println!(
        "downloading third-party crate sources to {} ...",
        vendor_dir.display()
    );
    let mut vendor_args = vec!["vendor", "--locked", "--no-delete", "--versioned-dirs"];
    // One-shot lock updates run without --locked so Cargo may add the entries
    // required by newly declared crates; regular syncs assert the lock.

    vendor_args.push(vendor_arg);
    let cargo_config = run_cargo_vendor(workspace_dir, &vendor_args)?;

    let locked_packages = locked_package_versions(&workspace_dir.join("Cargo.lock"))?;
    apply_catalog_patches(root, vendor_dir, catalog, &locked_packages)?;

    write_cargo_source_config(workspace_dir, &cargo_config)
}

fn locked_package_versions(path: &Path) -> Result<BTreeSet<(String, Version)>> {
    let lock: toml::Value = toml::from_str(&fs::read_to_string(path)?)?;
    let packages = lock
        .get("package")
        .and_then(toml::Value::as_array)
        .context("Cargo.lock lacks package entries")?;
    let mut result = BTreeSet::new();
    for package in packages {
        let name = package
            .get("name")
            .and_then(toml::Value::as_str)
            .context("package name missing from Cargo.lock")?;
        let version = package
            .get("version")
            .and_then(toml::Value::as_str)
            .context("package version missing from Cargo.lock")?
            .parse()?;
        result.insert((name.to_owned(), version));
    }
    Ok(result)
}

fn apply_catalog_patches(
    root: &Path,
    vendor_dir: &Path,
    catalog: &[&CrateDeclaration],
    locked_packages: &BTreeSet<(String, Version)>,
) -> Result<()> {
    for declaration in catalog {
        if declaration.patches.is_empty() {
            continue;
        }
        let requirement = semver::VersionReq::parse(&declaration.version).with_context(|| {
            format!(
                "invalid Cargo version requirement {} for patched crate {}",
                declaration.version, declaration.package
            )
        })?;
        for (name, version) in locked_packages {
            if name == &declaration.package && requirement.matches(version) {
                apply_patches_at_version(root, vendor_dir, declaration, version)?;
            }
        }
    }
    Ok(())
}

fn write_cargo_source_config(workspace_dir: &Path, config: &str) -> Result<()> {
    write_file(&workspace_dir.join(".cargo").join("config.toml"), config)
}

/// Applies the per-crate `patches` from `gnrt_config.toml` to vendored
/// sources. Unlike `cargo_spec` patches (applied per collected declaration),
/// these run for every configured crate present in the vendor dir, covering
/// crates that are only transitive dependencies or whose declarations cannot
/// be collected uniquely. Keys are `name` or `name@vEpoch`; the vendored
/// directory `<name>-<epoch>` must exist.
fn apply_config_patches(root: &Path, vendor_dir: &Path, config: &BuildConfig) -> Result<()> {
    for (key, crate_config) in config.iter_per_crate() {
        if crate_config.patches.is_empty() {
            continue;
        }
        let package = key.split('@').next().unwrap_or(key);
        for entry in fs::read_dir(vendor_dir)? {
            let entry = entry?;
            if !entry.file_type()?.is_dir() {
                continue;
            }
            let dir_name = entry.file_name();
            let dir_name = dir_name
                .to_str()
                .with_context(|| format!("non-UTF-8 vendored dir {}", entry.path().display()))?;
            // Config keys with an epoch (`heapless@v0_9`) patch every
            // vendored version of that epoch (heapless-0.9.*): the patch must
            // apply cleanly to each. Keys without an epoch patch every vendored
            // version of the package, unless the name is a prefix of another
            // configured package (e.g. `esp-hal` vs `esp-hal-procmacros`).
            let mut epoch_dir = None;
            if let Some((_, v)) = key.split_once('@') {
                let Ok(epoch) = v.parse::<crate::crates::Epoch>() else {
                    continue;
                };
                let prefix = match &epoch {
                    crate::crates::Epoch::Minor(m) => format!("{package}-0.{m}."),
                    crate::crates::Epoch::Patch(p) => format!("{package}-0.0.{p}."),
                    _ => format!("{package}-"),
                };
                if dir_name.starts_with(&prefix) {
                    epoch_dir = Some(dir_name.to_owned());
                }
            }
            if epoch_dir.is_none() && !key.contains('@') {
                let prefix_shadowed = config.iter_per_crate().any(|(other, _)| {
                    other != key
                        && other.starts_with(&format!("{package}-"))
                        && dir_name.starts_with(&format!("{other}-"))
                });
                if !prefix_shadowed && dir_name.starts_with(&format!("{package}-")) {
                    epoch_dir = Some(dir_name.to_owned());
                }
            }
            let Some(crate_dir) = epoch_dir.map(|_| vendor_dir.join(dir_name)) else {
                continue;
            };
            for patch in &crate_config.patches {
                let patch_path = crate::util::gn_path_label_to_path(root, patch)?;
                if !patch_path.is_file() {
                    bail!("patch file {} not found", patch_path.display());
                }
                let patch_arg = patch_path
                    .to_str()
                    .with_context(|| format!("non-UTF-8 patch path {}", patch_path.display()))?;
                let can_apply = git_apply_check(&crate_dir, patch_arg, false)?;
                if can_apply {
                    log::info!(
                        "applying patch {} to {}",
                        patch_path.display(),
                        crate_dir.display()
                    );
                    run_git_with_output(&crate_dir, &["apply", "-p1", patch_arg])?;
                } else if git_apply_check(&crate_dir, patch_arg, true)? {
                    log::info!(
                        "patch {} is already applied to {}",
                        patch_path.display(),
                        crate_dir.display()
                    );
                } else {
                    bail!(
                        "patch {} neither applies cleanly nor matches the current contents of {}",
                        patch_path.display(),
                        crate_dir.display()
                    );
                }
            }
        }
    }
    Ok(())
}

/// Applies each crate declaration's `patches` to its vendored source
/// directory (`<vendor_dir>/<package>-<version>/`) in declaration order
/// using `git apply -p1`. Patch paths are GN root-relative labels.
#[cfg(test)]
fn apply_patches(root: &Path, vendor_dir: &Path, crates: &[&CrateDeclaration]) -> Result<()> {
    for decl in crates {
        if decl.patches.is_empty() {
            continue;
        }
        // A pinned requirement (`=1.2.3`) names the same vendored directory as
        // the bare resolved version.
        let version = Version::parse(decl.version.trim_start_matches('='))?;
        apply_patches_at_version(root, vendor_dir, decl, &version)?;
    }
    Ok(())
}

fn apply_patches_at_version(
    root: &Path,
    vendor_dir: &Path,
    declaration: &CrateDeclaration,
    version: &Version,
) -> Result<()> {
    let crate_dir = vendor_dir.join(format!("{}-{version}", declaration.package));
    if !crate_dir.is_dir() {
        bail!(
            "vendored source dir {} missing for patched crate {} {}",
            crate_dir.display(),
            declaration.package,
            version
        );
    }
    for patch in &declaration.patches {
        let patch_path = crate::util::gn_path_label_to_path(root, patch)?;
        if !patch_path.is_file() {
            bail!("patch file {} not found", patch_path.display());
        }
        let patch_arg = patch_path
            .to_str()
            .with_context(|| format!("non-UTF-8 patch path {}", patch_path.display()))?;
        let can_apply = git_apply_check(&crate_dir, patch_arg, false)?;
        if can_apply {
            log::info!(
                "applying patch {} to {}",
                patch_path.display(),
                crate_dir.display()
            );
            run_git_with_output(&crate_dir, &["apply", "-p1", patch_arg])?;
        } else if git_apply_check(&crate_dir, patch_arg, true)? {
            log::info!(
                "patch {} is already applied to {}",
                patch_path.display(),
                crate_dir.display()
            );
        } else {
            bail!(
                "patch {} neither applies cleanly nor matches the current contents of {}",
                patch_path.display(),
                crate_dir.display()
            );
        }
    }
    Ok(())
}

fn git_apply_check(crate_dir: &Path, patch_arg: &str, reverse: bool) -> Result<bool> {
    let mut cmd = git_command_in(crate_dir)?;
    cmd.arg("apply");
    if reverse {
        cmd.arg("--reverse");
    }
    let output = cmd
        .args(["--check", "-p1", patch_arg])
        .output()
        .with_context(|| format!("checking patch {patch_arg}"))?;
    Ok(output.status.success())
}

/// Writes `contents` to `path`, creating parent directories as needed.
fn write_file(path: &Path, contents: &str) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).with_context(|| format!("creating {}", parent.display()))?;
    }
    fs::write(path, contents).with_context(|| format!("writing {}", path.display()))
}

/// Resolves declarations against a materialized workspace and compares the
/// result with the Cargo oracle.
///
/// # Errors
///
/// Returns an error if the workspace cannot be resolved or the oracle finds a
/// resolver divergence.
pub fn verify_resolution(
    declarations: &DeclarationGroups,
    root: &Path,
    workspace_dir: &Path,
    config: &BuildConfig,
) -> Result<()> {
    let (graph, crates) = resolve_graph_and_crates(declarations, root, workspace_dir, config)?;
    oracle::validate(&graph, declarations, &crates, config)
}

/// Builds the Cargo package graph and resolves declarations into crate instances.
///
/// # Errors
///
/// Returns an error if Cargo metadata fails or a declaration cannot be
/// resolved against the workspace.
fn resolve_graph_and_crates(
    declarations: &DeclarationGroups,
    root: &Path,
    workspace_dir: &Path,
    config: &BuildConfig,
) -> Result<(PackageGraph, BTreeMap<String, CrateInfo>)> {
    let mut command = guppy::MetadataCommand::new();
    command.cargo_path(cargo_bin()?);
    command.current_dir(workspace_dir);
    command.other_options(vec!["--locked".to_owned(), "--offline".to_owned()]);
    let metadata = command.exec().context("running cargo metadata")?;
    let graph = metadata.build_graph().context("building package graph")?;
    let crates = canonicalize_instances(resolve_instances(&graph, declarations, root, config)?)?;
    Ok((graph, crates))
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ResolveSpace {
    Shared,
    Root(String),
    Closure(String),
}

impl ResolveSpace {
    fn for_declaration(declaration: &CrateDeclaration) -> Self {
        match declaration.isolation {
            Isolation::None => Self::Shared,
            Isolation::Root => Self::Root(declaration.label.clone()),
            Isolation::Closure => Self::Closure(declaration.label.clone()),
        }
    }

    fn dependency(&self) -> Self {
        match self {
            Self::Root(_) => Self::Shared,
            _ => self.clone(),
        }
    }

    fn instance(&self, domain: ResolutionContext) -> String {
        let label = match self {
            Self::Shared => "shared",
            Self::Root(label) | Self::Closure(label) => label.as_str(),
        };
        match domain {
            ResolutionContext::Target => label.to_owned(),
            ResolutionContext::Host => format!("{label}#host"),
        }
    }
}

fn resolve_instances(
    graph: &guppy::graph::PackageGraph,
    declarations: &DeclarationGroups,
    root: &Path,
    config: &BuildConfig,
) -> Result<BTreeMap<String, CrateInfo>> {
    // Start from each synthetic root to associate features with its declaration.
    let roots = crate_decls_of(declarations)
        .into_iter()
        .map(|declaration| {
            let member = instance_directory(&declaration.label, &declaration.version);
            let synthetic = graph
                .packages()
                .find(|package| {
                    package.in_workspace() && package.name() == package_name_for(&member)
                })
                .with_context(|| format!("synthetic root for {} missing", declaration.label))?;
            let package = synthetic
                .direct_links()
                .find(|link| link.to().name() == declaration.package)
                .with_context(|| format!("root package for {} missing", declaration.label))?
                .to();
            Ok((
                FeatureRoot {
                    package: synthetic,
                    declaration,
                    context: if package.is_proc_macro() {
                        ResolutionContext::Host
                    } else {
                        ResolutionContext::Target
                    },
                },
                package,
            ))
        })
        .collect::<Result<Vec<_>>>()?;
    // Expand ordinary roots for host and target consumers; proc-macro roots
    // are host-only.
    let requests: Vec<_> = roots
        .iter()
        .flat_map(|(request, _)| {
            [ResolutionContext::Target, ResolutionContext::Host]
                .into_iter()
                .filter(|context| {
                    *context == ResolutionContext::Host
                        || request.context == ResolutionContext::Target
                })
                .map(|context| FeatureRoot {
                    package: request.package,
                    declaration: request.declaration,
                    context,
                })
        })
        .collect();
    let conditions =
        scoped_feature_conditions(&graph.feature_graph().resolve_all(), &requests, config);
    let mut domains: BTreeMap<(ResolveSpace, ResolutionContext), FeatureConditions> =
        BTreeMap::new();
    for ((space, feature, domain), condition) in conditions {
        domains
            .entry((space, domain))
            .or_default()
            .insert(feature, condition);
    }
    let mut sources = BTreeMap::new();
    let mut crates = BTreeMap::new();
    for ((space, domain), active) in domains {
        let empty = HashMap::new();
        let (target_conditions, host_conditions) = match domain {
            ResolutionContext::Target => (&active, &empty),
            ResolutionContext::Host => (&empty, &active),
        };
        for package in graph.packages().filter(|package| {
            !package.in_workspace() && active.contains_key(&FeatureId::base(package.id()))
        }) {
            let id = package.id().repr();
            if let Some(previous) = sources.insert((package.name(), package.version()), id) {
                ensure!(
                    previous == id,
                    "packages {previous} and {id} have identical source directory names"
                );
            }
            let instance = space.instance(domain);
            let direct: Vec<_> = roots
                .iter()
                .filter(|(request, actual)| {
                    actual.id() == package.id()
                        && ResolveSpace::for_declaration(request.declaration) == space
                })
                .map(|(request, _)| request.declaration)
                .collect();
            let rustflags = direct
                .first()
                .map(|declaration| declaration.rustflags.clone())
                .unwrap_or_default();
            ensure!(
                direct
                    .iter()
                    .all(|declaration| declaration.rustflags == rustflags),
                "shared package {} has conflicting rustflags in {}; use explicit isolation",
                package.name(),
                direct
                    .iter()
                    .map(|declaration| declaration.label.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            let mut dependencies = package_dependencies(
                package,
                DependencyKind::Normal,
                config,
                &instance,
                target_conditions,
                host_conditions,
            )?;
            let mut build_dependencies = package_dependencies(
                package,
                DependencyKind::Build,
                config,
                &instance,
                target_conditions,
                host_conditions,
            )?;
            for edge in dependencies.iter_mut().chain(&mut build_dependencies) {
                if domain == ResolutionContext::Host {
                    edge.context = ResolutionContext::Host;
                }
                edge.instance = space.dependency().instance(edge.context);
            }
            let deps::BuildTargets {
                lib_target,
                bin_targets,
                build_script,
            } = deps::get_build_targets(&package, config)?;
            let source = external_source(package);
            let path = crate_gn_path(root, package.manifest_path().as_str())?;
            crates.insert(
                format!("{instance}|{id}"),
                CrateInfo {
                    instance,
                    context: domain,
                    rule_dir: path.clone(),
                    source: source.clone(),
                    path,
                    package: Package {
                        package_name: package.name().to_owned(),
                        version: package.version().clone(),
                        declared_by: direct
                            .iter()
                            .map(|declaration| declaration.label.clone())
                            .collect(),
                        description: package.description().map(str::to_owned),
                        links: package.links().map(str::to_owned),
                        authors: package.authors().to_vec(),
                        edition: package.edition().to_owned(),
                        rustflags,
                        repository: package.repository().map(str::to_owned),
                        homepage: package.homepage().map(str::to_owned),
                        license: package.license().map(str::to_owned),
                        license_file: package.license_file().map(|path| path.to_string()),
                        rust_version: package
                            .minimum_rust_version()
                            .map(|version| version.to_string()),
                        readme: package.readme().map(|path| path.to_string()),
                        dependencies,
                        build_dependencies,
                        target_features: package_feature_groups(target_conditions, package),
                        host_features: package_feature_groups(host_conditions, package),
                        declared_conditions: Vec::new(),
                        lib_target,
                        bin_targets,
                        build_script,
                        group: config
                            .get_crate_config(package.name(), package.version())
                            .and_then(|config| config.group)
                            .unwrap_or(Group::Safe),
                        is_local: source.is_none(),
                        is_toplevel_dep: !direct.is_empty(),
                    },
                },
            );
        }
    }
    Ok(crates)
}

/// Verifies that every dependency binds to its resolved scope and context.
fn canonicalize_instances(
    crates: BTreeMap<String, CrateInfo>,
) -> Result<BTreeMap<String, CrateInfo>> {
    let identities: BTreeSet<_> = crates
        .values()
        .map(|info| {
            (
                info.instance.as_str(),
                info.package.package_name.as_str(),
                &info.package.version,
            )
        })
        .collect();
    for info in crates.values() {
        for edge in info
            .package
            .dependencies
            .iter()
            .chain(&info.package.build_dependencies)
        {
            ensure!(
                identities.contains(&(
                    edge.instance.as_str(),
                    edge.package_name.as_str(),
                    &edge.version
                )),
                "missing resolved dependency {} -> {} in {}",
                info.package.package_name,
                edge.package_name,
                edge.instance
            );
        }
    }
    Ok(crates)
}

type Conditions = SymbolicCondition;
type FeatureConditions<'g> = HashMap<FeatureId<'g>, Conditions>;

struct FeatureRoot<'g, 'd> {
    package: guppy::graph::PackageMetadata<'g>,
    declaration: &'d CrateDeclaration,
    context: ResolutionContext,
}

/// Propagates feature activation conditions within each scope and compilation
/// context.
fn scoped_feature_conditions<'g>(
    features: &FeatureSet<'g>,
    roots: &[FeatureRoot<'g, '_>],
    config: &BuildConfig,
) -> HashMap<(ResolveSpace, FeatureId<'g>, ResolutionContext), Conditions> {
    // Weak links wait for their optional dependency to activate.
    let weak_links: BTreeSet<_> = features
        .links(DependencyDirection::Forward)
        .filter_map(|(from, to, edge)| {
            matches!(
                edge,
                FeatureEdge::NamedFeatureWithSlash {
                    weak_index: Some(_),
                    ..
                }
            )
            .then_some((from, to))
        })
        .collect();
    // Each key is (scope, feature, context); each value is an OR of AND terms.
    // `None` means the feature is enabled unconditionally.
    let mut conditions = HashMap::new();
    // Include shared scope for dependencies of root-isolated declarations.
    let spaces: BTreeSet<_> = roots
        .iter()
        .map(|root| ResolveSpace::for_declaration(root.declaration))
        .chain([ResolveSpace::Shared])
        .collect();
    let declarations: HashMap<_, _> = roots
        .iter()
        .map(|root| (root.package.id(), root.declaration))
        .collect();
    // Each synthetic root starts with its base feature enabled unconditionally.
    for root in roots {
        conditions.insert(
            (
                ResolveSpace::for_declaration(root.declaration),
                FeatureId::base(root.package.id()),
                root.context,
            ),
            None,
        );
    }
    // Revisit feature links until transitive activation adds no new conditions.
    loop {
        let mut changed = false;
        // Propagate same-package feature links without crossing package edges.
        for (from, to, _edge) in features.links(DependencyDirection::Forward) {
            if weak_links.contains(&(from, to)) {
                continue;
            }
            for (space, context) in spaces.iter().flat_map(|space| {
                [ResolutionContext::Target, ResolutionContext::Host].map(|context| (space, context))
            }) {
                let Some(from_condition) = conditions.get(&(space.clone(), from, context)).cloned()
                else {
                    continue;
                };
                if from.package_id() == to.package_id() {
                    changed |= merge_symbolic(
                        &mut conditions,
                        (space.clone(), to, context),
                        from_condition,
                    );
                }
            }
        }
        // Conditional links apply declaration and dependency conditions.
        for link in features.conditional_links(DependencyDirection::Forward) {
            let package_link = link.package_link();
            let from = link.from().feature_id();
            let to = link.to().feature_id();
            if !accept_dependency(&package_link, config)
                || link.dev_only()
                || (from.package_id() == to.package_id() && !weak_links.contains(&(from, to)))
            {
                continue;
            }
            for (space, context) in spaces.iter().flat_map(|space| {
                [ResolutionContext::Target, ResolutionContext::Host].map(|context| (space, context))
            }) {
                let Some(mut from_condition) =
                    conditions.get(&(space.clone(), from, context)).cloned()
                else {
                    continue;
                };
                // Apply GN conditions from the root declaration to requested features.
                if let Some(declaration) = declarations.get(from.package_id()) {
                    if let FeatureLabel::Named(name) = to.label() {
                        if (name != "default" || !declaration.default_features)
                            && !declaration.features.iter().any(|entry| {
                                entry.condition().is_none()
                                    && entry.values().iter().any(|feature| feature == name)
                            })
                        {
                            let terms: Vec<_> = declaration
                                .features
                                .iter()
                                .filter(|entry| {
                                    entry.values().iter().any(|feature| feature == name)
                                })
                                .filter_map(ConfigurableValue::condition)
                                .map(|condition| {
                                    vec![ConditionAtom::Gn {
                                        expression: condition.to_owned(),
                                    }]
                                })
                                .collect();
                            if terms.is_empty() {
                                continue;
                            }
                            from_condition = and_conditions(&from_condition, &Some(terms));
                        }
                    }
                }
                let package_link = link.package_link();
                let weak = weak_links.contains(&(from, to));
                if weak {
                    // Weak links require the optional dependency's activation condition.
                    let optional =
                        FeatureId::optional_dependency(from.package_id(), package_link.dep_name());
                    let Some(available) = conditions.get(&(space.clone(), optional, context))
                    else {
                        continue;
                    };
                    from_condition = and_conditions(&from_condition, available);
                }
                for kind in [guppy::DependencyKind::Normal, guppy::DependencyKind::Build] {
                    // Cargo evaluates build-dependency selectors on the host.
                    let selector_context = if kind == guppy::DependencyKind::Build {
                        ResolutionContext::Host
                    } else {
                        context
                    };
                    let Some(edge) =
                        status_conditions(link.status_for_kind(kind), selector_context)
                    else {
                        continue;
                    };
                    let crosses_package = from.package_id() != to.package_id();
                    // Cross-package build dependencies and proc macros use Host context.
                    let destination = if crosses_package
                        && (kind == guppy::DependencyKind::Build
                            || link.to().package().is_proc_macro())
                    {
                        ResolutionContext::Host
                    } else {
                        context
                    };
                    // Direct roots keep their scope; transitive crates follow the scope policy.
                    changed |= merge_symbolic(
                        &mut conditions,
                        (
                            if crosses_package && !declarations.contains_key(from.package_id()) {
                                space.dependency()
                            } else {
                                space.clone()
                            },
                            to,
                            destination,
                        ),
                        and_conditions(&from_condition, &edge),
                    );
                }
            }
        }
        if !changed {
            break;
        }
    }
    conditions
}

fn merge_symbolic<'g>(
    conditions: &mut HashMap<(ResolveSpace, FeatureId<'g>, ResolutionContext), Conditions>,
    feature: (ResolveSpace, FeatureId<'g>, ResolutionContext),
    condition: Conditions,
) -> bool {
    let merged = match conditions.get(&feature) {
        Some(previous) => or_conditions(previous, &condition),
        None => condition,
    };
    if conditions.get(&feature) == Some(&merged) {
        false
    } else {
        conditions.insert(feature, merged);
        true
    }
}

#[cfg(test)]
fn symbolic_feature_conditions<'g>(
    features: &FeatureSet<'g>,
    roots: &[FeatureRoot<'g, '_>],
    config: &BuildConfig,
) -> (FeatureConditions<'g>, FeatureConditions<'g>) {
    let mut target = HashMap::new();
    let mut host = HashMap::new();
    for ((_, feature, domain), condition) in scoped_feature_conditions(features, roots, config) {
        let output = if domain == ResolutionContext::Target {
            &mut target
        } else {
            &mut host
        };
        let merged = output
            .get(&feature)
            .map(|previous| or_conditions(previous, &condition))
            .unwrap_or(condition);
        output.insert(feature, merged);
    }
    (target, host)
}

/// Renders a parsed target spec back into its raw Cargo selector form.
///
/// `TargetSpec`'s `Display` drops the `cfg(...)` wrapper, so expressions are
/// re-wrapped to keep the selector the generate stage translates.
fn selector_string(spec: &target_spec::TargetSpec) -> String {
    match spec {
        target_spec::TargetSpec::Expression(expression) => {
            let inner = expression.expression_str();
            if inner.starts_with("cfg(") {
                inner.to_owned()
            } else {
                format!("cfg({inner})")
            }
        }
        target_spec::TargetSpec::PlainString(triple) => triple.as_str().to_owned(),
    }
}

/// Converts a link's `PlatformStatus` into a raw condition. `None` means the
/// link is never enabled.
fn status_conditions(status: PlatformStatus<'_>, context: ResolutionContext) -> Option<Conditions> {
    if status.is_never() {
        return None;
    }
    if status.is_always() {
        return Some(None);
    }
    match status {
        PlatformStatus::PlatformDependent { eval } => {
            let terms = eval
                .target_specs()
                .iter()
                .map(|spec| {
                    vec![ConditionAtom::Cargo {
                        selector: selector_string(spec),
                        context,
                    }]
                })
                .collect();
            Some(normalize_conditions(terms))
        }
        PlatformStatus::Always | PlatformStatus::Never => unreachable!(),
    }
}

/// ANDs two conditions (cartesian product of their terms).
fn and_conditions(left: &Conditions, right: &Conditions) -> Conditions {
    match (left, right) {
        (None, _) => right.clone(),
        (_, None) => left.clone(),
        (Some(left), Some(right)) => {
            let mut terms = Vec::with_capacity(left.len() * right.len());
            for lhs in left {
                for rhs in right {
                    let mut term = lhs.clone();
                    term.extend(rhs.iter().cloned());
                    terms.push(term);
                }
            }
            normalize_conditions(terms)
        }
    }
}

/// ORs two conditions (union of their terms).
fn or_conditions(left: &Conditions, right: &Conditions) -> Conditions {
    match (left, right) {
        (None, _) | (_, None) => None,
        (Some(left), Some(right)) => {
            let mut terms = left.clone();
            terms.extend(right.iter().cloned());
            normalize_conditions(terms)
        }
    }
}

/// Sorts and dedups a condition. A term that is an empty AND makes the whole
/// condition unconditional.
fn normalize_conditions(mut terms: Vec<Vec<ConditionAtom>>) -> Conditions {
    if terms.iter().any(|term| term.is_empty()) {
        return None;
    }
    for term in &mut terms {
        term.sort();
        term.dedup();
    }
    terms.sort();
    terms.dedup();
    let simplified = terms
        .iter()
        .filter(|term| {
            !terms.iter().any(|other| {
                other.len() < term.len() && other.iter().all(|atom| term.contains(atom))
            })
        })
        .cloned()
        .collect();
    Some(simplified)
}

/// Groups a package's enabled named features by their condition.
fn package_feature_groups<'g>(
    conditions: &HashMap<FeatureId<'g>, Conditions>,
    package: guppy::graph::PackageMetadata<'g>,
) -> Vec<FeatureGroup> {
    let mut grouped: BTreeMap<Conditions, BTreeSet<String>> = BTreeMap::new();
    for (feature, condition) in conditions {
        if feature.package_id() != package.id() {
            continue;
        }
        if let FeatureLabel::Named(name) = feature.label() {
            grouped
                .entry(condition.clone())
                .or_default()
                .insert(name.to_owned());
        }
    }
    grouped
        .into_iter()
        .map(|(condition, features)| FeatureGroup {
            condition,
            features: features.into_iter().collect(),
        })
        .collect()
}

fn accept_dependency(link: &guppy::graph::PackageLink<'_>, config: &BuildConfig) -> bool {
    !config.resolve.remove_crates.contains(link.to().name())
        && !config
            .get_combined_set(link.from().name(), link.from().version(), |crate_config| {
                &crate_config.remove_deps
            })
            .contains(link.to().name())
}

fn package_dependencies<'g>(
    package: guppy::graph::PackageMetadata<'g>,
    kind: DependencyKind,
    config: &BuildConfig,
    instance: &str,
    target_conditions: &FeatureConditions<'g>,
    host_conditions: &FeatureConditions<'g>,
) -> Result<Vec<Dependency>> {
    let mut dependencies = package
        .direct_links()
        .filter(|link| !link.to().in_workspace())
        .filter(|link| accept_dependency(link, config))
        .filter(|link| link.req_for_kind(kind.into()).is_present())
        .map(|link| {
            Ok(Dependency {
                instance: instance.to_owned(),
                target_condition: dependency_activation(
                    &link,
                    kind,
                    target_conditions,
                    ResolutionContext::Target,
                ),
                host_condition: dependency_activation(
                    &link,
                    kind,
                    host_conditions,
                    ResolutionContext::Host,
                ),
                package_name: link.to().name().to_owned(),
                use_name: link.resolved_name().to_owned(),
                version: link.to().version().clone(),
                condition: None,
                context: dependency_context(&link, kind),
                removal: dependency_removal(&link, config)?,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    dependencies.retain(|edge| {
        edge.target_condition != Some(Vec::new()) || edge.host_condition != Some(Vec::new())
    });
    dependencies.sort_by(|lhs, rhs| {
        lhs.package_name
            .cmp(&rhs.package_name)
            .then(lhs.use_name.cmp(&rhs.use_name))
            .then(lhs.version.cmp(&rhs.version))
    });
    Ok(dependencies)
}

fn dependency_activation<'g>(
    link: &guppy::graph::PackageLink<'g>,
    kind: DependencyKind,
    conditions: &FeatureConditions<'g>,
    context: ResolutionContext,
) -> Conditions {
    let status = link.req_for_kind(kind.into()).status();
    let selector_context = if kind == DependencyKind::Build {
        ResolutionContext::Host
    } else {
        context
    };
    let mut enabled = Some(Vec::new());
    for (feature, status) in [
        (FeatureId::base(link.from().id()), status.required_status()),
        (
            FeatureId::optional_dependency(link.from().id(), link.dep_name()),
            status.optional_status(),
        ),
    ] {
        if let (Some(from), Some(edge)) = (
            conditions.get(&feature),
            status_conditions(status, selector_context),
        ) {
            enabled = or_conditions(&enabled, &and_conditions(from, &edge));
        }
    }
    enabled
}

/// Returns the build side `link` of `kind` is resolved for.
///
/// Build-script and proc-macro dependencies execute on the host, so their own
/// target selectors are resolved for the host.
fn dependency_context(
    link: &guppy::graph::PackageLink<'_>,
    kind: DependencyKind,
) -> ResolutionContext {
    let host = match kind {
        DependencyKind::Build => true,
        DependencyKind::Normal => link.to().is_proc_macro(),
    };
    if host {
        ResolutionContext::Host
    } else {
        ResolutionContext::Target
    }
}

/// Returns the conditional-removal rule recorded for `link`, if any.
fn dependency_removal(
    link: &guppy::graph::PackageLink<'_>,
    config: &BuildConfig,
) -> Result<Option<Removal>> {
    let package = link.to().name();
    let global = config
        .resolve
        .remove_crates_when
        .iter()
        .filter(|rule| rule.package == package)
        .map(|rule| ("resolve.remove_crates_when", rule.when.as_str()));
    let local = config
        .get_combined_conditional_removals(link.from().name(), link.from().version())
        .into_iter()
        .filter(|rule| rule.package == package)
        .map(|rule| ("remove_deps_when", rule.when.as_str()));

    let mut reasons = BTreeSet::new();
    let mut when = Vec::new();
    for (reason, selector) in global.chain(local) {
        reasons.insert(reason);
        let spec = target_spec::TargetSpec::new(selector.to_owned()).with_context(|| {
            format!(
                "parsing conditional removal for {} -> {package}",
                link.from().name()
            )
        })?;
        when.push(selector_string(&spec));
    }
    if when.is_empty() {
        return Ok(None);
    }
    when.sort();
    when.dedup();
    Ok(Some(Removal {
        reason: reasons.into_iter().collect::<Vec<_>>().join(", "),
        when,
    }))
}

fn external_source(package: guppy::graph::PackageMetadata<'_>) -> Option<String> {
    match package.source() {
        guppy::graph::PackageSource::External(source) => Some(source.to_owned()),
        _ => None,
    }
}

fn crate_gn_path(root: &Path, manifest_path: &str) -> Result<String> {
    let manifest_path = Path::new(manifest_path);
    let crate_dir = manifest_path
        .parent()
        .context("crate manifest has no parent directory")?;
    let relative = crate_dir.strip_prefix(root).with_context(|| {
        format!(
            "crate directory {} is outside project root {}",
            crate_dir.display(),
            root.display()
        )
    })?;
    Ok(format!(
        "//{}",
        crate::paths::normalize_unix_path_separator(relative)
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collect::{DeclarationGroups, ToolchainDeclaration};

    fn crate_decl(package: &str, version: &str, features: &[&str]) -> CrateDeclaration {
        CrateDeclaration {
            origin: "cargo".to_owned(),
            label: format!("//test:{package}"),
            package: package.to_owned(),
            version: version.to_owned(),
            features: features
                .iter()
                .map(|f| ConfigurableValue::Value(f.to_string()))
                .collect(),
            rustflags: Vec::new(),
            isolation: Isolation::None,
            default_features: true,
            patches: vec![],
            git: String::new(),
            rev: String::new(),
            branch: String::new(),
            tag: String::new(),
        }
    }

    fn sample_toolchain(role: &str) -> ToolchainDeclaration {
        ToolchainDeclaration {
            origin: "gn".to_owned(),
            role: role.to_owned(),
            cc: "clang".to_owned(),
            cxx: "clang++".to_owned(),
            ar: "llvm-ar".to_owned(),
            rustc: "rustc".to_owned(),
            llvm_target: "thumbv7m-none-eabi".to_owned(),
            target_triple: "thumbv7m-vivo-blueos".to_owned(),
            label: "//build/toolchain:blueos_thumbv7m".to_owned(),
        }
    }

    fn sample_declarations() -> DeclarationGroups {
        let toolchain = sample_toolchain("target");
        DeclarationGroups {
            cargo: vec![
                Declaration::Crate(crate_decl("log", "0.4.28", &["std"])),
                Declaration::Crate(crate_decl("spin", "0.9.8", &[])),
            ],
            gn: vec![Declaration::Toolchain(toolchain)],
        }
    }

    fn fixture_package(root: &Path, name: &str, manifest: &str) {
        let dir = root.join(name);
        fs::create_dir_all(dir.join("src")).unwrap();
        fs::write(
            dir.join("Cargo.toml"),
            format!(
                "[package]\nname = {name:?}\nversion = \"1.0.0\"\nedition = \"2021\"\n{manifest}"
            ),
        )
        .unwrap();
        fs::write(dir.join("src/lib.rs"), "").unwrap();
    }

    fn instance_fixture(
        conditional: bool,
    ) -> (
        tempfile::TempDir,
        guppy::graph::PackageGraph,
        DeclarationGroups,
    ) {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path();
        let mut declarations = DeclarationGroups {
            cargo: Vec::new(),
            gn: Vec::new(),
        };
        let mut members = Vec::new();
        for feature in ["a", "b"] {
            let mut declaration = crate_decl("library", "=1.0.0", &[]);
            if !conditional {
                declaration
                    .features
                    .push(ConfigurableValue::Value(feature.to_owned()));
            }
            declaration.label = format!("//test:library_{feature}");
            declaration.isolation = Isolation::Closure;
            declaration.default_features = false;
            if conditional {
                declaration.features.push(ConfigurableValue::Conditional {
                    condition: format!("product == \"{feature}\""),
                    values: vec![feature.to_owned()],
                });
            }
            let member = instance_directory(&declaration.label, &declaration.version);
            members.push(member.clone());
            fixture_package(root, &member, &format!("[dependencies]\nlibrary = {{ path = \"../library\", default-features = false, features = [{feature:?}] }}\n"));
            declarations.cargo.push(Declaration::Crate(declaration));
            fixture_package(root, &format!("chip-{feature}"), "");
        }
        write_root_manifest(root, &members).unwrap();
        let manifest = fs::read_to_string(root.join("Cargo.toml")).unwrap();
        fs::write(root.join("Cargo.toml"), format!("{manifest}exclude = [\"library\", \"shared\", \"chip-a\", \"chip-b\", \"helper\"]\n")).unwrap();
        fixture_package(
            root,
            "shared",
            "[features]\na = []\nb = []\nweak = []\nbuild = []\n",
        );
        fixture_package(
            root,
            "helper",
            "[lib]\nproc-macro = true\n[features]\na = []\nb = []\n",
        );
        fixture_package(
            root,
            "library",
            r#"
links = "fixture_native"
[dependencies]
chip-a = { path = "../chip-a", optional = true }
chip-b = { path = "../chip-b", optional = true }
shared = { path = "../shared", optional = true, default-features = false }
helper = { path = "../helper", default-features = false }
[build-dependencies]
shared = { path = "../shared", default-features = false, features = ["build"] }
[features]
a = ["dep:chip-a", "shared/a", "helper/a"]
b = ["dep:chip-b", "shared/b", "helper/b"]
weakonly = ["shared?/weak"]
"#,
        );
        fs::write(root.join("library/build.rs"), "fn main() {}\n").unwrap();
        let mut command = guppy::MetadataCommand::new();
        command.cargo_path(env!("CARGO"));
        command.current_dir(root);
        command.other_options(vec!["--offline".to_owned()]);
        let graph = command.exec().unwrap().build_graph().unwrap();
        (fixture, graph, declarations)
    }

    #[test]
    fn joint_symbolic_roots_match_cargo_set_and_preserve_conditions() {
        use guppy::graph::cargo::{CargoOptions, CargoResolverVersion};
        use guppy::graph::feature::StandardFeatures;

        for conditional in [false, true] {
            let (_fixture, graph, declarations) = instance_fixture(conditional);
            let declarations = crate_decls_of(&declarations);
            let roots: Vec<_> = declarations
                .iter()
                .map(|declaration| {
                    let name = package_name_for(&instance_directory(
                        &declaration.label,
                        &declaration.version,
                    ));
                    FeatureRoot {
                        package: graph
                            .packages()
                            .find(|package| package.name() == name)
                            .unwrap(),
                        declaration,
                        context: ResolutionContext::Target,
                    }
                })
                .collect();
            let (target, host) = symbolic_feature_conditions(
                &graph.feature_graph().resolve_all(),
                &roots,
                &BuildConfig::default(),
            );
            for product in if conditional {
                vec!["a", "b"]
            } else {
                vec!["both"]
            } {
                let ids: Vec<_> = roots
                    .iter()
                    .filter(|root| {
                        product == "both"
                            || root.declaration.label.ends_with(&format!("_{product}"))
                    })
                    .map(|root| root.package.id())
                    .collect();
                let initials = graph
                    .resolve_ids(ids)
                    .unwrap()
                    .to_feature_set(StandardFeatures::Default);
                let mut options = CargoOptions::new();
                options.set_resolver(CargoResolverVersion::V2);
                let oracle = initials.into_cargo_set(&options).unwrap();
                let enabled = |condition: &Conditions| {
                    condition.as_ref().is_none_or(|terms| {
                        terms.iter().any(|term| {
                            term.iter().all(|atom| match atom {
                                ConditionAtom::Gn { expression } => {
                                    expression == &format!("product == \"{product}\"")
                                }
                                ConditionAtom::Cargo { .. } => {
                                    panic!("fixture has no platform selectors")
                                }
                            })
                        })
                    })
                };
                for (conditions, expected) in [
                    (&target, oracle.target_features()),
                    (&host, oracle.host_features()),
                ] {
                    for package in graph.packages().filter(|package| !package.in_workspace()) {
                        let feature_list = expected.features_for(package.id()).unwrap();
                        let active = conditions
                            .get(&FeatureId::base(package.id()))
                            .is_some_and(enabled);
                        assert_eq!(
                            active,
                            feature_list.is_some(),
                            "package {} / {product}",
                            package.name()
                        );
                        let actual: BTreeSet<_> = package_feature_groups(conditions, package)
                            .into_iter()
                            .filter(|group| enabled(&group.condition))
                            .flat_map(|group| group.features)
                            .collect();
                        let expected: BTreeSet<_> = feature_list
                            .map(|list| list.named_features().map(str::to_owned).collect())
                            .unwrap_or_default();
                        assert_eq!(actual, expected, "features {} / {product}", package.name());
                    }
                }
            }
            if conditional {
                for name in ["a", "b"] {
                    let package = graph
                        .packages()
                        .find(|package| package.name() == "library")
                        .unwrap();
                    let condition = &target[&FeatureId::named(package.id(), name)];
                    assert_eq!(
                        condition,
                        &Some(vec![vec![ConditionAtom::Gn {
                            expression: format!("product == \"{name}\"")
                        }]])
                    );
                }
            }
        }
    }

    #[test]
    fn declaration_instances_isolate_features_and_transitive_dependencies() {
        let (fixture, graph, declarations) = instance_fixture(false);
        let instances = resolve_instances(
            &graph,
            &declarations,
            &fixture.path().canonicalize().unwrap(),
            &BuildConfig::default(),
        )
        .unwrap();
        for feature in ["a", "b"] {
            let label = format!("//test:library_{feature}");
            let find = |name: &str| {
                instances
                    .values()
                    .find(|info| {
                        info.instance
                            .strip_suffix("#host")
                            .unwrap_or(&info.instance)
                            == label
                            && info.package.package_name == name
                            && info.context
                                == if name == "helper" {
                                    ResolutionContext::Host
                                } else {
                                    ResolutionContext::Target
                                }
                    })
                    .unwrap()
            };
            let library = find("library");
            assert_eq!(library.package.links.as_deref(), Some("fixture_native"));
            assert!(find("shared").package.links.is_none());
            let features: Vec<_> = library
                .package
                .target_features
                .iter()
                .flat_map(|group| group.features.clone())
                .collect();
            assert!(features.contains(&feature.to_owned()));
            assert!(!features.contains(&if feature == "a" { "b" } else { "a" }.to_owned()));
            assert!(library
                .package
                .dependencies
                .iter()
                .any(|dependency| dependency.package_name == format!("chip-{feature}")));
            assert!(!instances.values().any(|info| info.instance == label
                && info.package.package_name
                    == format!("chip-{}", if feature == "a" { "b" } else { "a" })));
            assert!(find("helper")
                .package
                .host_features
                .iter()
                .any(|group| group.features.contains(&feature.to_owned())));
            assert!(instances
                .values()
                .find(|info| info.instance == format!("{label}#host")
                    && info.package.package_name == "shared")
                .unwrap()
                .package
                .host_features
                .iter()
                .any(|group| group.features.contains(&"build".to_owned())));
        }
    }

    #[test]
    fn declaration_conditions_propagate_to_optional_transitive_and_host_features() {
        let (fixture, graph, declarations) = instance_fixture(true);
        let instances = resolve_instances(
            &graph,
            &declarations,
            &fixture.path().canonicalize().unwrap(),
            &BuildConfig::default(),
        )
        .unwrap();
        for feature in ["a", "b"] {
            let label = format!("//test:library_{feature}");
            let expected = Some(vec![vec![ConditionAtom::Gn {
                expression: format!("product == \"{feature}\""),
            }]]);
            for name in ["library", "shared", "helper"] {
                let package = &instances
                    .values()
                    .find(|info| {
                        info.instance
                            .strip_suffix("#host")
                            .unwrap_or(&info.instance)
                            == label
                            && info.package.package_name == name
                    })
                    .unwrap()
                    .package;
                let group = package
                    .target_features
                    .iter()
                    .chain(&package.host_features)
                    .find(|group| group.features.contains(&feature.to_owned()))
                    .unwrap();
                assert_eq!(group.condition, expected, "{name}/{feature}");
            }
            let library = &instances
                .values()
                .find(|info| info.instance == label && info.package.package_name == "library")
                .unwrap()
                .package;
            let chip = library
                .dependencies
                .iter()
                .find(|dependency| dependency.package_name == format!("chip-{feature}"))
                .unwrap();
            assert_eq!(chip.target_condition, expected);
        }
    }

    #[test]
    fn unconditional_feature_overrides_matching_conditional_request() {
        let (fixture, graph, mut declarations) = instance_fixture(true);
        let Declaration::Crate(declaration) = &mut declarations.cargo[0] else {
            unreachable!()
        };
        declaration
            .features
            .push(ConfigurableValue::Value("a".to_owned()));
        let instances = resolve_instances(
            &graph,
            &declarations,
            &fixture.path().canonicalize().unwrap(),
            &BuildConfig::default(),
        )
        .unwrap();
        let library = &instances
            .values()
            .find(|info| {
                info.package.package_name == "library" && info.instance == "//test:library_a"
            })
            .unwrap()
            .package;
        assert!(library
            .target_features
            .iter()
            .any(|group| group.condition.is_none() && group.features.contains(&"a".to_owned())));
        assert!(library
            .dependencies
            .iter()
            .find(|dependency| dependency.package_name == "chip-a")
            .unwrap()
            .target_condition
            .is_none());
    }

    #[test]
    fn explicit_default_feature_can_be_conditional() {
        let (fixture, _, mut declarations) = instance_fixture(true);
        let root = fixture.path();
        let Declaration::Crate(declaration) = &mut declarations.cargo[0] else {
            unreachable!()
        };
        let ConfigurableValue::Conditional { values, .. } = &mut declaration.features[0] else {
            unreachable!()
        };
        *values = vec!["default".to_owned()];
        let library = root.join("library/Cargo.toml");
        let text = fs::read_to_string(&library).unwrap();
        fs::write(library, format!("{text}\ndefault = [\"a\"]\n")).unwrap();
        let member = root
            .join(instance_directory(&declaration.label, &declaration.version))
            .join("Cargo.toml");
        let text = fs::read_to_string(&member)
            .unwrap()
            .replace("features = [\"a\"]", "features = [\"default\"]");
        fs::write(member, text).unwrap();
        let mut command = guppy::MetadataCommand::new();
        command.cargo_path(env!("CARGO"));
        command.current_dir(root);
        command.other_options(vec!["--offline".to_owned()]);
        let graph = command.exec().unwrap().build_graph().unwrap();
        let instances = resolve_instances(
            &graph,
            &declarations,
            &root.canonicalize().unwrap(),
            &BuildConfig::default(),
        )
        .unwrap();
        let library = &instances
            .values()
            .find(|info| {
                info.package.package_name == "library" && info.instance == "//test:library_a"
            })
            .unwrap()
            .package;
        let expected = Some(vec![vec![ConditionAtom::Gn {
            expression: "product == \"a\"".to_owned(),
        }]]);
        for feature in ["default", "a"] {
            assert_eq!(
                library
                    .target_features
                    .iter()
                    .find(|group| group.features.contains(&feature.to_owned()))
                    .unwrap()
                    .condition,
                expected
            );
        }
    }

    #[test]
    fn optional_build_dependencies_keep_target_feature_activation() {
        let (fixture, _, mut declarations) = instance_fixture(true);
        let root = fixture.path();
        let manifest = root.join("library/Cargo.toml");
        let text = fs::read_to_string(&manifest).unwrap().replace(
            "[build-dependencies]",
            "[build-dependencies]\nbuildhelper = { path = \"../buildhelper\", optional = true }",
        );
        fs::write(
            manifest,
            format!("{text}\nbuildonly = [\"dep:buildhelper\"]\n"),
        )
        .unwrap();
        fixture_package(root, "buildhelper", "");
        let workspace = root.join("Cargo.toml");
        let text = fs::read_to_string(&workspace)
            .unwrap()
            .replace("\"helper\"]", "\"helper\", \"buildhelper\"]");
        fs::write(workspace, text).unwrap();
        let Declaration::Crate(declaration) = &mut declarations.cargo[0] else {
            unreachable!()
        };
        let ConfigurableValue::Conditional { values, .. } = &mut declaration.features[0] else {
            unreachable!()
        };
        values.push("buildonly".to_owned());
        let member = root
            .join(instance_directory(&declaration.label, &declaration.version))
            .join("Cargo.toml");
        let text = fs::read_to_string(&member)
            .unwrap()
            .replace("features = [\"a\"]", "features = [\"a\", \"buildonly\"]");
        fs::write(member, text).unwrap();
        let mut command = guppy::MetadataCommand::new();
        command.cargo_path(env!("CARGO"));
        command.current_dir(root);
        command.other_options(vec!["--offline".to_owned()]);
        let graph = command.exec().unwrap().build_graph().unwrap();
        let instances = resolve_instances(
            &graph,
            &declarations,
            &root.canonicalize().unwrap(),
            &BuildConfig::default(),
        )
        .unwrap();
        let library = &instances
            .values()
            .find(|info| {
                info.instance == "//test:library_a" && info.package.package_name == "library"
            })
            .unwrap()
            .package;
        let dependency = library
            .build_dependencies
            .iter()
            .find(|dependency| dependency.package_name == "buildhelper")
            .unwrap_or_else(|| {
                panic!(
                    "library={library:?};packages={:?}",
                    instances.keys().collect::<Vec<_>>()
                )
            });
        assert_eq!(
            dependency.target_condition,
            Some(vec![vec![ConditionAtom::Gn {
                expression: "product == \"a\"".to_owned()
            }]])
        );
    }

    #[test]
    fn platform_conditions_use_host_for_build_dependencies() {
        let (fixture, _, declarations) = instance_fixture(true);
        let root = fixture.path();
        let shared = root.join("shared/Cargo.toml");
        let text = fs::read_to_string(&shared).unwrap();
        fs::write(
            shared,
            format!("{text}target-build = []\nhost-normal = []\n"),
        )
        .unwrap();
        let library = root.join("library/Cargo.toml");
        let text = fs::read_to_string(&library).unwrap();
        fs::write(library, format!("{text}\n[target.'cfg(unix)'.build-dependencies]\nshared = {{ path = \"../shared\", default-features = false, features = [\"target-build\"] }}\n")).unwrap();
        let helper = root.join("helper/Cargo.toml");
        let text = fs::read_to_string(&helper).unwrap();
        fs::write(helper, format!("{text}\n[target.'cfg(windows)'.dependencies]\nshared = {{ path = \"../shared\", default-features = false, features = [\"host-normal\"] }}\n")).unwrap();
        let mut command = guppy::MetadataCommand::new();
        command.cargo_path(env!("CARGO"));
        command.current_dir(root);
        command.other_options(vec!["--offline".to_owned()]);
        let graph = command.exec().unwrap().build_graph().unwrap();
        let instances = resolve_instances(
            &graph,
            &declarations,
            &root.canonicalize().unwrap(),
            &BuildConfig::default(),
        )
        .unwrap();
        let shared = &instances
            .values()
            .find(|info| {
                info.instance == "//test:library_a#host" && info.package.package_name == "shared"
            })
            .unwrap()
            .package;
        for (feature, selector, context) in [
            ("target-build", "cfg(unix)", ResolutionContext::Host),
            ("host-normal", "cfg(windows)", ResolutionContext::Host),
        ] {
            let group = shared
                .host_features
                .iter()
                .find(|group| group.features.contains(&feature.to_owned()))
                .unwrap();
            assert!(group.condition.as_ref().unwrap().iter().any(|term| {
                term.contains(&ConditionAtom::Cargo {
                    selector: selector.to_owned(),
                    context,
                })
            }));
        }
        let Declaration::Crate(declaration) = &declarations.cargo[0] else {
            unreachable!()
        };
        let name = package_name_for(&instance_directory(
            &declaration.label,
            &declaration.version,
        ));
        let synthetic = graph
            .packages()
            .find(|package| package.name() == name)
            .unwrap();
        let (_, host_conditions) = symbolic_feature_conditions(
            &graph.feature_graph().resolve_all(),
            &[FeatureRoot {
                package: synthetic,
                declaration,
                context: ResolutionContext::Target,
            }],
            &BuildConfig::default(),
        );
        let shared_package = graph
            .packages()
            .find(|package| package.name() == "shared")
            .unwrap();
        for (host_triple, target_triple) in [
            ("x86_64-unknown-linux-gnu", "x86_64-pc-windows-msvc"),
            ("x86_64-pc-windows-msvc", "x86_64-unknown-linux-gnu"),
        ] {
            use guppy::graph::cargo::{CargoOptions, CargoResolverVersion};
            use guppy::graph::feature::StandardFeatures;
            use target_spec::{Platform, TargetFeatures, TargetSpec};

            let host = Platform::new(host_triple, TargetFeatures::Unknown).unwrap();
            let target = Platform::new(target_triple, TargetFeatures::Unknown).unwrap();
            let mut options = CargoOptions::new();
            options
                .set_resolver(CargoResolverVersion::V2)
                .set_host_platform(host.clone())
                .set_target_platform(target.clone());
            let oracle = graph
                .resolve_ids([synthetic.id()])
                .unwrap()
                .to_feature_set(StandardFeatures::Default)
                .into_cargo_set(&options)
                .unwrap();
            let expected: BTreeSet<_> = oracle
                .host_features()
                .features_for(shared_package.id())
                .unwrap()
                .unwrap()
                .named_features()
                .map(str::to_owned)
                .collect();
            let actual: BTreeSet<_> = package_feature_groups(&host_conditions, shared_package)
                .into_iter()
                .filter(|group| {
                    group.condition.as_ref().is_none_or(|terms| {
                        terms.iter().any(|term| {
                            term.iter().all(|atom| match atom {
                                ConditionAtom::Gn { expression } => {
                                    expression == "product == \"a\""
                                }
                                ConditionAtom::Cargo { selector, context } => {
                                    TargetSpec::new(selector.clone())
                                        .unwrap()
                                        .eval(if *context == ResolutionContext::Host {
                                            &host
                                        } else {
                                            &target
                                        })
                                        .unwrap()
                                }
                            })
                        })
                    })
                })
                .flat_map(|group| group.features)
                .collect();
            assert_eq!(
                actual, expected,
                "host={host_triple}, target={target_triple}"
            );
        }
    }

    #[test]
    fn isolation_modes_route_roots_and_transitive_feature_requests() {
        for isolation in [Isolation::None, Isolation::Root, Isolation::Closure] {
            let (fixture, graph, mut declarations) = instance_fixture(false);
            for declaration in &mut declarations.cargo {
                let Declaration::Crate(declaration) = declaration else {
                    unreachable!()
                };
                declaration.isolation = isolation;
            }
            let instances = canonicalize_instances(
                resolve_instances(
                    &graph,
                    &declarations,
                    &fixture.path().canonicalize().unwrap(),
                    &BuildConfig::default(),
                )
                .unwrap(),
            )
            .unwrap();
            let packages = |name: &str, domain| {
                instances
                    .values()
                    .filter(|info| info.package.package_name == name && info.context == domain)
                    .collect::<Vec<_>>()
            };
            let libraries = packages("library", ResolutionContext::Target);
            assert_eq!(
                libraries.len(),
                if isolation == Isolation::None { 1 } else { 2 }
            );
            let shared = packages("shared", ResolutionContext::Target);
            assert_eq!(
                shared.len(),
                if isolation == Isolation::Closure {
                    2
                } else {
                    1
                }
            );
            let macros = packages("helper", ResolutionContext::Host);
            assert_eq!(
                macros.len(),
                if isolation == Isolation::Closure {
                    2
                } else {
                    1
                }
            );
            assert_eq!(
                packages("library", ResolutionContext::Host).len(),
                libraries.len()
            );
            if isolation != Isolation::Closure {
                for feature in ["a", "b"] {
                    assert!(shared[0]
                        .package
                        .target_features
                        .iter()
                        .any(|group| group.features.contains(&feature.to_owned())));
                    assert!(macros[0]
                        .package
                        .host_features
                        .iter()
                        .any(|group| group.features.contains(&feature.to_owned())));
                }
            }
            for library in libraries {
                let edge = library
                    .package
                    .dependencies
                    .iter()
                    .find(|edge| edge.package_name == "shared")
                    .unwrap();
                let child = shared
                    .iter()
                    .find(|info| info.instance == edge.instance)
                    .unwrap();
                assert_eq!(child.context, edge.context);
            }
        }
    }

    #[test]
    fn explicit_isolation_preserves_identity_even_with_identical_features() {
        let (fixture, _, mut declarations) = instance_fixture(false);
        let Declaration::Crate(second) = &mut declarations.cargo[1] else {
            unreachable!()
        };
        second.features = vec![ConfigurableValue::Value("a".to_owned())];
        let manifest = fixture
            .path()
            .join(instance_directory(&second.label, &second.version))
            .join("Cargo.toml");
        let text = fs::read_to_string(&manifest)
            .unwrap()
            .replace("features = [\"b\"]", "features = [\"a\"]");
        fs::write(manifest, text).unwrap();
        let mut command = guppy::MetadataCommand::new();
        command
            .cargo_path(env!("CARGO"))
            .current_dir(fixture.path())
            .other_options(vec!["--offline".to_owned()]);
        let graph = command.exec().unwrap().build_graph().unwrap();
        for isolation in [Isolation::Root, Isolation::Closure] {
            for declaration in &mut declarations.cargo {
                let Declaration::Crate(declaration) = declaration else {
                    unreachable!()
                };
                declaration.isolation = isolation;
            }
            let instances = canonicalize_instances(
                resolve_instances(
                    &graph,
                    &declarations,
                    &fixture.path().canonicalize().unwrap(),
                    &BuildConfig::default(),
                )
                .unwrap(),
            )
            .unwrap();
            let roots: Vec<_> = instances
                .values()
                .filter(|info| {
                    info.package.package_name == "library"
                        && info.context == ResolutionContext::Target
                })
                .collect();
            assert_eq!(roots.len(), 2);
            assert_eq!(roots[0].rule_dir, roots[1].rule_dir);
            assert_eq!(roots[0].rule_dir, roots[0].path);
            assert_ne!(roots[0].instance, roots[1].instance);
            assert_eq!(
                roots[0].package.target_features,
                roots[1].package.target_features
            );
            let children = instances
                .values()
                .filter(|info| {
                    info.package.package_name == "shared"
                        && info.context == ResolutionContext::Target
                })
                .count();
            assert_eq!(
                children,
                if isolation == Isolation::Closure {
                    2
                } else {
                    1
                }
            );
        }
    }

    #[test]
    fn mixed_root_and_closure_keep_children_in_distinct_scopes() {
        let (fixture, graph, mut declarations) = instance_fixture(false);
        let Declaration::Crate(first) = &mut declarations.cargo[0] else {
            unreachable!()
        };
        first.isolation = Isolation::Root;
        let instances = canonicalize_instances(
            resolve_instances(
                &graph,
                &declarations,
                &fixture.path().canonicalize().unwrap(),
                &BuildConfig::default(),
            )
            .unwrap(),
        )
        .unwrap();
        let children: Vec<_> = instances
            .values()
            .filter(|info| {
                info.package.package_name == "shared" && info.context == ResolutionContext::Target
            })
            .collect();
        assert_eq!(children.len(), 2);
        let global = children
            .iter()
            .find(|info| info.instance == "shared")
            .unwrap();
        let private = children
            .iter()
            .find(|info| info.instance == "//test:library_b")
            .unwrap();
        assert!(global
            .package
            .target_features
            .iter()
            .any(|group| group.features == ["a"]));
        assert!(private
            .package
            .target_features
            .iter()
            .any(|group| group.features == ["b"]));
    }

    #[test]
    fn shared_roots_reject_conflicting_rustflags() {
        let (fixture, graph, mut declarations) = instance_fixture(false);
        for declaration in &mut declarations.cargo {
            let Declaration::Crate(declaration) = declaration else {
                unreachable!()
            };
            declaration.isolation = Isolation::None;
        }
        let Declaration::Crate(first) = &mut declarations.cargo[0] else {
            unreachable!()
        };
        first
            .rustflags
            .push(ConfigurableValue::Value("--cfg=custom".to_owned()));
        let error = resolve_instances(
            &graph,
            &declarations,
            &fixture.path().canonicalize().unwrap(),
            &BuildConfig::default(),
        )
        .unwrap_err();
        assert!(error.to_string().contains("conflicting rustflags"));
        assert!(error.to_string().contains("//test:library_a"));
        assert!(error.to_string().contains("//test:library_b"));
    }

    #[test]
    fn explicit_recipe_reuse_preserves_features_and_dependency_closures() {
        for declared_features in [&["a"][..], &["a", "b"][..]] {
            let fixture = tempfile::tempdir().unwrap();
            let root = fixture.path();
            let mut serde = crate_decl("serde", "=1.0.0", declared_features);
            serde.label = "//test:serde".to_owned();
            serde.default_features = false;
            let mut consumer = crate_decl("consumer", "=1.0.0", &[]);
            consumer.label = "//test:consumer".to_owned();
            let declarations = DeclarationGroups {
                cargo: vec![Declaration::Crate(serde), Declaration::Crate(consumer)],
                gn: Vec::new(),
            };
            let members: Vec<_> = declarations
            .cargo
            .iter()
            .map(|declaration| {
                let Declaration::Crate(declaration) = declaration else {
                    unreachable!()
                };
                let member = instance_directory(&declaration.label, &declaration.version);
                fixture_package(
                    root,
                    &member,
                    &format!(
                        "[dependencies]\n{} = {{ path = \"../{}\", default-features = false, features = {:?} }}\n",
                        declaration.package,
                        declaration.package,
                        declaration.features.iter().flat_map(ConfigurableValue::values).collect::<Vec<_>>()
                    ),
                );
                member
            })
            .collect();
            write_root_manifest(root, &members).unwrap();
            let workspace = fs::read_to_string(root.join("Cargo.toml")).unwrap();
            fs::write(
                root.join("Cargo.toml"),
                format!("{workspace}exclude = [\"serde\", \"serde_core\", \"consumer\", \"optional-leaf\"]\n"),
            )
            .unwrap();
            fixture_package(root, "optional-leaf", "");
            fixture_package(root, "serde_core", "[dependencies]\noptional-leaf = { path = \"../optional-leaf\", optional = true }\n[features]\na = []\nb = [\"dep:optional-leaf\"]\n");
            fixture_package(
            root,
            "serde",
            "[dependencies]\nserde_core = { path = \"../serde_core\", default-features = false }\n[features]\na = [\"serde_core/a\"]\nb = [\"serde_core/b\"]\n",
        );
            fixture_package(
            root,
            "consumer",
            "[lib]\nproc-macro = true\n[dependencies]\nserde = { path = \"../serde\", default-features = false, features = [\"b\"] }\n",
        );
            let mut command = guppy::MetadataCommand::new();
            command.cargo_path(env!("CARGO"));
            command.current_dir(root);
            command.other_options(vec!["--offline".to_owned()]);
            let graph = command.exec().unwrap().build_graph().unwrap();
            let instances = canonicalize_instances(
                resolve_instances(
                    &graph,
                    &declarations,
                    &root.canonicalize().unwrap(),
                    &BuildConfig::default(),
                )
                .unwrap(),
            )
            .unwrap();
            let serde_instances: Vec<_> = instances
                .values()
                .filter(|info| info.package.package_name == "serde")
                .collect();
            let shared = declared_features.contains(&"b");
            assert_eq!(serde_instances.len(), 2);
            let serde_core_instances: Vec<_> = instances
                .values()
                .filter(|info| info.package.package_name == "serde_core")
                .collect();
            assert_eq!(serde_core_instances.len(), 2);
            for (feature, context) in [
                ("a", ResolutionContext::Target),
                ("b", ResolutionContext::Host),
            ] {
                let serde = serde_instances
                    .iter()
                    .find(|info| {
                        let features = match context {
                            ResolutionContext::Target => &info.package.target_features,
                            ResolutionContext::Host => &info.package.host_features,
                        };
                        features
                            .iter()
                            .any(|group| group.features.contains(&feature.to_owned()))
                    })
                    .unwrap();
                if !shared && context == ResolutionContext::Target {
                    assert!(!serde
                        .package
                        .target_features
                        .iter()
                        .any(|group| group.features.contains(&"b".to_owned())));
                }
                if context == ResolutionContext::Host {
                    assert!(serde
                        .package
                        .host_features
                        .iter()
                        .any(|group| group.features.contains(&"a".to_owned())));
                }
                let features = match context {
                    ResolutionContext::Target => &serde.package.target_features,
                    ResolutionContext::Host => &serde.package.host_features,
                };
                assert!(features
                    .iter()
                    .any(|group| group.features.contains(&feature.to_owned())));
                let dependencies: Vec<_> = serde
                    .package
                    .dependencies
                    .iter()
                    .filter(|dependency| dependency.use_name == "serde_core")
                    .collect();
                assert_eq!(dependencies.len(), 1, "feature={feature}; serde={serde:?}");
                let serde_core = serde_core_instances
                    .iter()
                    .find(|info| info.instance == dependencies[0].instance)
                    .unwrap();
                assert_eq!(serde_core.instance, dependencies[0].instance);
                let features = match context {
                    ResolutionContext::Target => &serde_core.package.target_features,
                    ResolutionContext::Host => &serde_core.package.host_features,
                };
                assert!(features
                    .iter()
                    .any(|group| group.features.contains(&feature.to_owned())));
                let optional = serde_core
                    .package
                    .dependencies
                    .iter()
                    .find(|edge| edge.package_name == "optional-leaf");
                assert_eq!(
                    optional.is_some(),
                    context == ResolutionContext::Host || shared
                );
                if let Some(edge) = optional {
                    assert!(instances.values().any(|info| info.instance == edge.instance
                        && info.package.package_name == edge.package_name));
                }
            }
            let mut flagged = declarations.clone();
            let Declaration::Crate(serde) = &mut flagged.cargo[0] else {
                unreachable!()
            };
            serde.rustflags = vec![ConfigurableValue::Value("--cfg=custom".to_owned())];
            let separate = canonicalize_instances(
                resolve_instances(
                    &graph,
                    &flagged,
                    &root.canonicalize().unwrap(),
                    &BuildConfig::default(),
                )
                .unwrap(),
            )
            .unwrap();
            assert_eq!(
                separate
                    .values()
                    .filter(|info| info.package.package_name == "serde")
                    .count(),
                2
            );
        }
    }

    #[test]
    fn weak_feature_requires_both_request_and_dependency_activation() {
        let (fixture, _, mut declarations) = instance_fixture(true);
        let Declaration::Crate(declaration) = &mut declarations.cargo[0] else {
            unreachable!()
        };
        declaration.features.push(ConfigurableValue::Conditional {
            condition: "weak_enabled".to_owned(),
            values: vec!["weakonly".to_owned()],
        });
        let member = instance_directory(&declaration.label, &declaration.version);
        let manifest = fixture.path().join(&member).join("Cargo.toml");
        let text = fs::read_to_string(&manifest)
            .unwrap()
            .replace("features = [\"a\"]", "features = [\"a\", \"weakonly\"]");
        fs::write(manifest, text).unwrap();
        let mut command = guppy::MetadataCommand::new();
        command.cargo_path(env!("CARGO"));
        command.current_dir(fixture.path());
        command.other_options(vec!["--offline".to_owned()]);
        let graph = command.exec().unwrap().build_graph().unwrap();
        let instances = resolve_instances(
            &graph,
            &declarations,
            &fixture.path().canonicalize().unwrap(),
            &BuildConfig::default(),
        )
        .unwrap();
        let shared = &instances
            .values()
            .find(|info| {
                info.instance == "//test:library_a" && info.package.package_name == "shared"
            })
            .unwrap()
            .package;
        let weak = shared
            .target_features
            .iter()
            .find(|group| group.features.contains(&"weak".to_owned()))
            .unwrap();
        let condition = weak.condition.as_ref().unwrap();
        assert_eq!(condition.len(), 1);
        assert_eq!(condition[0].len(), 2, "{condition:?};shared={shared:?}");
        assert!(condition[0].contains(&ConditionAtom::Gn {
            expression: "weak_enabled".to_owned()
        }));
        assert!(condition[0].contains(&ConditionAtom::Gn {
            expression: "product == \"a\"".to_owned()
        }));
    }

    #[test]
    fn subset_workspace_retains_canonical_versions_without_full_vendor() {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path();
        let sources = root.join("sources");
        fs::create_dir_all(sources.join(".gnrt/generated")).unwrap();
        for (name, version, dependencies) in [
            ("shared", "1.0.0", ""),
            ("shared", "2.0.0", ""),
            ("first", "1.0.0", "[dependencies]\nshared = \"1\"\n"),
            ("second", "1.0.0", "[dependencies]\nshared = \"2\"\n"),
        ] {
            let directory = sources.join(format!("{name}-{version}"));
            fs::create_dir_all(directory.join("src")).unwrap();
            fs::write(directory.join("src/lib.rs"), "").unwrap();
            fs::write(directory.join("Cargo.toml"), format!("[package]\nname = {name:?}\nversion = {version:?}\nedition = \"2021\"\n{dependencies}")).unwrap();
            fs::write(
                directory.join(".cargo-checksum.json"),
                r#"{"files":{},"package":null}"#,
            )
            .unwrap();
        }
        let first = crate_decl("first", "=1.0.0", &[]);
        let second = crate_decl("second", "=1.0.0", &[]);
        let canonical = root.join("canonical");
        let subset = root.join("subset");
        let source_config = format!(
            "[source.crates-io]\nreplace-with = \"fixture\"\n[source.fixture]\ndirectory = {:?}\n",
            sources.to_str().unwrap()
        );
        assemble_workspace(&canonical, &[&first, &second]).unwrap();
        write_cargo_source_config(&canonical, &source_config).unwrap();
        let cargo = env!("CARGO");
        let status = std::process::Command::new(cargo)
            .args(["generate-lockfile", "--offline"])
            .current_dir(&canonical)
            .status()
            .unwrap();
        assert!(status.success());
        let canonical_bytes = fs::read(canonical.join("Cargo.lock")).unwrap();
        assemble_workspace(&subset, &[&first]).unwrap();
        write_cargo_source_config(&subset, &source_config).unwrap();
        seed_workspace_lockfile(&canonical.join("Cargo.lock"), &subset).unwrap();
        let status = std::process::Command::new(cargo)
            .args(["update", "--workspace", "--offline"])
            .current_dir(&subset)
            .status()
            .unwrap();
        assert!(status.success());
        validate_subset_lockfile(
            &fs::read_to_string(canonical.join("Cargo.lock")).unwrap(),
            &subset.join("Cargo.lock"),
        )
        .unwrap();
        assert_eq!(
            fs::read(canonical.join("Cargo.lock")).unwrap(),
            canonical_bytes
        );
        let subset_text = fs::read_to_string(subset.join("Cargo.lock")).unwrap();
        assert!(!subset_text.contains("name = \"second\""));
        assert!(!subset_text.contains("version = \"2.0.0\""));
        fs::write(
            subset.join("Cargo.lock"),
            subset_text.replace("version = \"1.0.0\"", "version = \"9.0.0\""),
        )
        .unwrap();
        assert!(validate_subset_lockfile(
            &fs::read_to_string(canonical.join("Cargo.lock")).unwrap(),
            &subset.join("Cargo.lock")
        )
        .is_err());
    }

    #[test]
    fn git_subset_retains_canonical_revision_and_optional_platform_edges() {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path();
        let repository = root.join("repository");
        fs::create_dir_all(&repository).unwrap();
        fs::write(
            repository.join("Cargo.toml"),
            "[workspace]\nresolver = \"2\"\nmembers = [\"git-library\", \"git-leaf\"]\n",
        )
        .unwrap();
        fixture_package(&repository, "git-leaf", "");
        fixture_package(
            &repository,
            "git-library",
            r#"
[features]
optional = ["dep:git-leaf"]
[target.'cfg(unix)'.dependencies]
git-leaf = { path = "../git-leaf", optional = true }
"#,
        );
        for args in [
            vec!["init", "-q"],
            vec!["add", "."],
            vec![
                "-c",
                "user.name=Fixture",
                "-c",
                "user.email=fixture@example.invalid",
                "commit",
                "-qm",
                "fixture",
            ],
        ] {
            assert!(std::process::Command::new("git")
                .args(args)
                .current_dir(&repository)
                .status()
                .unwrap()
                .success());
        }
        let revision = run_git_with_output(&repository, &["rev-parse", "HEAD"])
            .unwrap()
            .trim()
            .to_owned();
        let mut first = crate_decl("git-library", "=1.0.0", &["optional"]);
        first.label = "//test:git_first".to_owned();
        first.git = format!("file://{}", repository.canonicalize().unwrap().display());
        first.rev = revision.clone();
        let mut second = first.clone();
        second.label = "//test:git_second".to_owned();
        second.features.clear();
        let canonical = root.join("canonical-git");
        let subset = root.join("subset-git");
        assemble_workspace(&canonical, &[&first, &second]).unwrap();
        let cargo_home = root.join("cargo-home");
        let cargo = env!("CARGO");
        // All git URLs are local file URLs; no registry or network is involved.
        assert!(std::process::Command::new(cargo)
            .args(["generate-lockfile"])
            .env("CARGO_HOME", &cargo_home)
            .current_dir(&canonical)
            .status()
            .unwrap()
            .success());
        assemble_workspace(&subset, &[&second]).unwrap();
        seed_workspace_lockfile(&canonical.join("Cargo.lock"), &subset).unwrap();
        assert!(std::process::Command::new(cargo)
            .args(["update", "--workspace", "--offline"])
            .env("CARGO_HOME", &cargo_home)
            .current_dir(&subset)
            .status()
            .unwrap()
            .success());
        validate_subset_lockfile(
            &fs::read_to_string(canonical.join("Cargo.lock")).unwrap(),
            &subset.join("Cargo.lock"),
        )
        .unwrap();
        let text = fs::read_to_string(subset.join("Cargo.lock")).unwrap();
        assert!(text.contains(&revision));
        let vendor = root.join("vendor-git");
        assert!(std::process::Command::new(cargo)
            .args(["vendor", "--locked", "--offline", "--versioned-dirs"])
            .arg(&vendor)
            .env("CARGO_HOME", &cargo_home)
            .current_dir(&subset)
            .output()
            .unwrap()
            .status
            .success());
        validate_subset_lockfile(
            &fs::read_to_string(canonical.join("Cargo.lock")).unwrap(),
            &subset.join("Cargo.lock"),
        )
        .unwrap();
        assert!(vendor.join("git-library-1.0.0/Cargo.toml").is_file());
    }

    #[test]
    fn dependency_line_registry() {
        let decl = crate_decl("log", "0.4.28", &["std", "serde"]);
        assert_eq!(
            dependency_line(&decl),
            "log = { version = \"0.4.28\", features = [\"serde\", \"std\"] }"
        );
    }

    #[test]
    fn dependency_line_unions_conditional_features() {
        let mut decl = crate_decl("log", "0.4.28", &["std"]);
        decl.features.push(ConfigurableValue::Conditional {
            condition: "board == \"foo\"".to_owned(),
            values: vec!["serde".to_owned(), "std".to_owned()],
        });
        assert_eq!(
            dependency_line(&decl),
            "log = { version = \"0.4.28\", features = [\"serde\", \"std\"] }"
        );
    }

    #[test]
    fn dependency_line_no_default_features() {
        let mut decl = crate_decl("spin", "0.9.8", &[]);
        decl.default_features = false;
        assert_eq!(
            dependency_line(&decl),
            "spin = { version = \"0.9.8\", default-features = false }"
        );
    }

    #[test]
    fn dependency_line_git_source() {
        let mut decl = crate_decl("ftp", "3.0.1", &[]);
        decl.git = "https://github.com/mattnenterprise/rust-ftp".to_owned();
        decl.rev = "abc123".to_owned();
        assert_eq!(
            dependency_line(&decl),
            "ftp = { git = \"https://github.com/mattnenterprise/rust-ftp\", \
             rev = \"abc123\", version = \"3.0.1\" }"
        );
    }

    #[test]
    fn declaration_labels_isolate_duplicate_packages() {
        let a = crate_decl("log", "0.4.28", &["std"]);
        let mut b = crate_decl("log", "0.4.28", &["std"]);
        b.label = "//test:other_log".to_owned();
        validate_unique_crate_declarations(&[&a, &b]).unwrap();

        let c = crate_decl("log", "0.4.27", &["std"]);
        assert!(validate_unique_crate_declarations(&[&a, &c]).is_err());

        let spin = crate_decl("spin", "0.9.8", &[]);
        validate_unique_crate_declarations(&[&a, &spin]).unwrap();
    }

    #[test]
    fn assemble_workspace_synthesizes_spec_only_modules() {
        // Each declaring module gets a synthetic package mirroring its GN
        // label path.
        let mut declarations = sample_declarations();
        // Give the spec declarations distinct modules.
        for decl in declarations.cargo.iter_mut() {
            if let Declaration::Crate(c) = decl {
                c.label = format!("//modules/{}:{}", c.package, c.package);
            }
        }
        let dir = tempfile::tempdir().unwrap();
        let workspace_dir = dir.path().join("resolve_workspace");
        let crates = crate_decls_of(&declarations);
        assemble_workspace(&workspace_dir, &crates).expect("assemble failed");

        let root_manifest = fs::read_to_string(workspace_dir.join("Cargo.toml")).unwrap();
        for declaration in crates {
            let member = instance_directory(&declaration.label, &declaration.version);
            assert!(root_manifest.contains(&member));
            let manifest =
                fs::read_to_string(workspace_dir.join(&member).join("Cargo.toml")).unwrap();
            assert!(manifest.contains(&format!("name = {:?}", package_name_for(&member))));
            assert!(manifest.contains(&dependency_line(declaration)));
        }
    }

    fn crate_decls_of(declarations: &DeclarationGroups) -> Vec<&CrateDeclaration> {
        declarations
            .cargo
            .iter()
            .filter_map(|d| match d {
                Declaration::Crate(c) => Some(c),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn apply_patches_fails_when_crate_dir_missing() {
        let dir = tempfile::tempdir().unwrap();
        let mut decl = crate_decl("log", "0.4.28", &[]);
        decl.patches = vec!["//patches/log.patch".to_owned()];

        let err = apply_patches(dir.path(), dir.path(), &[&decl]).unwrap_err();
        assert!(err.to_string().contains("missing"), "got: {err}");
    }

    #[test]
    fn apply_patches_fails_when_patch_file_missing() {
        let dir = tempfile::tempdir().unwrap();
        let mut decl = crate_decl("log", "0.4.28", &[]);
        decl.patches = vec!["//patches/log.patch".to_owned()];

        fs::create_dir_all(dir.path().join("log-0.4.28")).unwrap();
        let err = apply_patches(dir.path(), dir.path(), &[&decl]).unwrap_err();
        assert!(err.to_string().contains("patch file"), "got: {err}");
    }

    #[test]
    fn apply_patches_inside_parent_repository() {
        let root = tempfile::tempdir().unwrap();
        assert!(std::process::Command::new("git")
            .args(["init", "-q"])
            .current_dir(root.path())
            .status()
            .unwrap()
            .success());
        let vendor = root.path().join("third_party");
        let crate_dir = vendor.join("log-0.4.28");
        fs::create_dir_all(&crate_dir).unwrap();
        let original = "pub fn f() -> i32 { 0 }\n";
        let expected = "pub fn f() -> i32 { 1 }\n";
        let source = crate_dir.join("lib.rs");
        fs::write(&source, original).unwrap();
        let patches = root.path().join("patches");
        fs::create_dir_all(&patches).unwrap();
        fs::write(
            patches.join("log.patch"),
            "--- a/lib.rs\n+++ b/lib.rs\n@@ -1 +1 @@\n-pub fn f() -> i32 { 0 }\n+pub fn f() -> i32 { 1 }\n",
        )
        .unwrap();
        let mut declaration = crate_decl("log", "=0.4.28", &[]);
        declaration.patches = vec!["//patches/log.patch".to_owned()];
        for _attempt in 0..2 {
            apply_patches(root.path(), &vendor, &[&declaration]).unwrap();
            assert_eq!(fs::read_to_string(&source).unwrap(), expected);
        }
        fs::write(&source, original).unwrap();
        let config: BuildConfig = toml::from_str(
            "[resolve]\nroot = \"fixture\"\nremove_crates = []\nremove_crates_when = []\n[crate.log]\npatches = [\"//patches/log.patch\"]\n",
        )
        .unwrap();
        for _attempt in 0..2 {
            apply_config_patches(root.path(), &vendor, &config).unwrap();
            assert_eq!(fs::read_to_string(&source).unwrap(), expected);
        }
    }

    #[test]
    fn apply_patches_applies_git_patch() {
        let dir = tempfile::tempdir().unwrap();
        let mut decl = crate_decl("log", "0.4.28", &[]);
        decl.patches = vec!["//patches/log.patch".to_owned()];

        // A fake git repo for the vendored crate.
        let crate_dir = dir.path().join("log-0.4.28");
        fs::create_dir_all(&crate_dir).unwrap();
        let status = std::process::Command::new("git")
            .args(["init", "-q"])
            .current_dir(&crate_dir)
            .status()
            .unwrap();
        assert!(status.success());

        // A source file the patch will modify.
        let src = crate_dir.join("lib.rs");
        fs::write(&src, "pub fn f() -> i32 { 0 }\n").unwrap();

        // A patch that git apply accepts without a commit (index only).
        let patch_dir = dir.path().join("patches");
        fs::create_dir_all(&patch_dir).unwrap();
        fs::write(
            patch_dir.join("log.patch"),
            "diff --git a/lib.rs b/lib.rs\nindex 1111111..2222222 100644\n--- a/lib.rs\n+++ b/lib.rs\n@@ -1 +1 @@\n-pub fn f() -> i32 { 0 }\n+pub fn f() -> i32 { 1 }\n",
        )
        .unwrap();

        apply_patches(dir.path(), dir.path(), &[&decl]).expect("apply failed");
        apply_patches(dir.path(), dir.path(), &[&decl]).expect("second apply must be a no-op");

        let patched = fs::read_to_string(&src).unwrap();
        assert!(patched.contains("i32 { 1 }"), "got: {patched}");
    }

    #[test]
    fn catalog_patch_applies_to_a_locked_transitive_package() {
        let dir = tempfile::tempdir().unwrap();
        let mut declaration = crate_decl("log", "1.2.3", &[]);
        declaration.patches = vec!["//patches/log.patch".to_owned()];
        let crate_dir = dir.path().join("log-1.2.3");
        fs::create_dir_all(&crate_dir).unwrap();
        assert!(std::process::Command::new("git")
            .args(["init", "-q"])
            .current_dir(&crate_dir)
            .status()
            .unwrap()
            .success());
        let src = crate_dir.join("lib.rs");
        fs::write(&src, "pub fn f() -> i32 { 0 }\n").unwrap();
        let patch_dir = dir.path().join("patches");
        fs::create_dir_all(&patch_dir).unwrap();
        fs::write(
            patch_dir.join("log.patch"),
            "diff --git a/lib.rs b/lib.rs\nindex 1111111..2222222 100644\n--- a/lib.rs\n+++ b/lib.rs\n@@ -1 +1 @@\n-pub fn f() -> i32 { 0 }\n+pub fn f() -> i32 { 1 }\n",
        )
        .unwrap();
        let locked = BTreeSet::from([("log".to_owned(), Version::new(1, 2, 3))]);

        apply_catalog_patches(dir.path(), dir.path(), &[&declaration], &locked).unwrap();

        assert!(fs::read_to_string(src).unwrap().contains("i32 { 1 }"));
    }

    #[test]
    fn cargo_vendor_config_is_preserved_verbatim() {
        let workspace = tempfile::tempdir().unwrap();
        let config = "[source.crates-io]\nreplace-with = \"vendored-sources\"\n\n\
[source.\"git+https://example.com/repo\"]\n\
git = \"https://example.com/repo\"\n\
replace-with = \"vendored-sources\"\n\n\
[source.vendored-sources]\n\
directory = \"/checkout/third_party/crates\"\n";

        write_cargo_source_config(workspace.path(), config).unwrap();

        assert_eq!(
            fs::read_to_string(workspace.path().join(".cargo/config.toml")).unwrap(),
            config
        );
    }

    #[test]
    fn cargo_vendor_config_allows_a_workspace_without_external_sources() {
        let workspace = tempfile::tempdir().unwrap();
        write_cargo_source_config(workspace.path(), "").unwrap();
        assert_eq!(
            fs::read_to_string(workspace.path().join(".cargo/config.toml")).unwrap(),
            ""
        );
    }

    #[test]
    fn seed_workspace_lockfile_uses_configured_lockfile() {
        let checkout = tempfile::tempdir().unwrap();
        let workspace = tempfile::tempdir().unwrap();
        let lockfile = checkout.path().join("locks").join("Cargo.lock");
        fs::create_dir_all(lockfile.parent().unwrap()).unwrap();
        fs::write(&lockfile, "tracked").unwrap();

        seed_workspace_lockfile(&lockfile, workspace.path()).unwrap();

        assert_eq!(
            fs::read_to_string(workspace.path().join("Cargo.lock")).unwrap(),
            "tracked"
        );
    }

    #[test]
    fn seed_workspace_lockfile_allows_a_missing_lockfile() {
        let checkout = tempfile::tempdir().unwrap();
        let workspace = tempfile::tempdir().unwrap();

        seed_workspace_lockfile(&checkout.path().join("missing.lock"), workspace.path()).unwrap();

        assert!(!workspace.path().join("Cargo.lock").exists());
    }

    #[test]
    fn write_back_lockfile_uses_configured_path() {
        let workspace = tempfile::tempdir().unwrap();
        fs::write(workspace.path().join("Cargo.lock"), "resolved").unwrap();

        let checkout = tempfile::tempdir().unwrap();
        let lockfile = checkout.path().join("custom").join("Cargo.lock");
        write_back_lockfile(&lockfile, workspace.path()).unwrap();
        assert_eq!(fs::read_to_string(&lockfile).unwrap(), "resolved");
    }

    #[test]
    fn write_back_lockfile_fails_without_resolved_lockfile() {
        let workspace = tempfile::tempdir().unwrap();
        let checkout = tempfile::tempdir().unwrap();
        let err =
            write_back_lockfile(&checkout.path().join("Cargo.lock"), workspace.path()).unwrap_err();
        assert!(err.to_string().contains("not found"), "got: {err}");
    }

    #[test]
    fn crate_path_is_project_root_relative_gn_path() {
        assert_eq!(
            crate_gn_path(
                Path::new("/checkout"),
                "/checkout/third_party/crates/autocfg-1.5.0/Cargo.toml",
            )
            .unwrap(),
            "//third_party/crates/autocfg-1.5.0"
        );
        assert!(crate_gn_path(
            Path::new("/checkout"),
            "/cargo/registry/autocfg-1.5.0/Cargo.toml",
        )
        .is_err());
    }

    #[test]
    fn crates_info_schema_version_is_three() {
        let dir = tempfile::tempdir().unwrap();
        let context = SyncContext {
            catalog: DeclarationGroups {
                cargo: Vec::new(),
                gn: Vec::new(),
            },
            collect_inputs: Vec::new(),
            scopes: Vec::new(),
            declarations: DeclarationGroups {
                cargo: Vec::new(),
                gn: Vec::new(),
            },
            crates: BTreeMap::new(),
        };

        write_crates_info(dir.path(), &context).unwrap();

        let value: serde_json::Value =
            serde_json::from_slice(&fs::read(dir.path().join("crates-info.json")).unwrap())
                .unwrap();
        assert_eq!(value["version"], 3);
        assert!(value.get("packages").is_none());
    }
}
