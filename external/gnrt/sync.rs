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

//! Synchronizes third-party crates for a BlueKernel GN build.
//!
//! The current working directory is the project root and must contain `.gn`.

use crate::collect;
use crate::config::BuildConfig;
use crate::generate;
use crate::paths;
use crate::resolve;
use crate::SyncCommandArgs;
use anyhow::{bail, ensure, Context, Result};
use gnrt_lib::collect::Declaration;
use gnrt_lib::sync_state::{self, FileRecord, Publication, RequestRecord, SyncLock, SyncState};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

/// Shown when the collection `gn gen` fails.
const COLLECTION_ORDER_HINT: &str = "gnrt could not collect the dependency declarations from GN. BUILD.gn files may reference crate targets that have not been generated. Declare these dependencies with cargo_spec, then run `gnrt sync --all` to generate their GN build files.";

/// Collects declarations, resolves dependencies, and publishes GN rules.
///
/// # Errors
///
/// Returns an error if collection, dependency resolution, generation, state
/// validation, or publication fails.
pub fn sync(args: SyncCommandArgs, paths: &dyn paths::GnrtPaths) -> Result<()> {
    if !paths.root().join(".gn").is_file() {
        bail!(
            "The current directory ({}) does not contain a .gn file.",
            paths.root().display()
        );
    }
    let root = paths.root();
    let gnrt_out_dir = root.join(&args.out);
    let vendor = root.join(paths.third_party());
    let state_path = vendor.join(sync_state::STATE_FILE);
    let marker = vendor.join(sync_state::TRANSACTION_FILE);
    let normalized_args = sync_state::normalize_args(&args.args)?;
    let generator = sync_state::fingerprint(root, &std::env::current_exe()?)?;
    if args.check {
        // Check for an unfinished update from a previous synchronization.
        ensure!(
            !marker.exists(),
            "The previous synchronization did not finish updating the dependency files. Run `gnrt sync --all` to recover."
        );
        // Load the saved synchronization record.
        let state = SyncState::read(&state_path).context(
            "The saved synchronization record is missing or invalid. Run `gnrt sync --all` first.",
        )?;
        // Validate recorded inputs, tool binaries, environment values, and generated artifacts.
        state.validate(root)?;
        ensure!(
            state.inputs.contains(&generator),
            "The gnrt executable has changed. Run `gnrt sync --all` to regenerate the GN build files."
        );
        // Accept a full sync or an exact previously recorded target request.
        if state.complete
            || args
                .target
                .as_deref()
                .is_some_and(|target| state.request(root, target, &normalized_args).is_some())
        {
            println!("The saved synchronization record is valid.");
            return Ok(());
        }
        // Recollect declarations when there is no exact request match.
        let temporary = tempfile::tempdir()?;
        let config = BuildConfig::from_path(paths.third_party_config_file())?;
        let context = collect::collect(
            &temporary.path().join("collect"),
            temporary.path(),
            args.target.as_deref(),
            &args.args,
            &config,
        )
        .context(COLLECTION_ORDER_HINT)?;
        // Confirm the declaration catalog has not changed since synchronization.
        ensure!(
            sync_state::digest(&serde_json::to_vec(&context.catalog)?) == state.catalog_sha256,
            "The collected dependency declarations have changed. Run `gnrt sync --all` to update the dependency sources and GN build files."
        );
        // A subset record cannot satisfy a check without a target.
        ensure!(
            args.target.is_some(),
            "The saved synchronization record covers only some dependency declarations. Run `gnrt sync --all` to process every registered declaration."
        );
        // The saved synchronization result must include every declaration
        // needed by this target.
        ensure!(sync_state::root_labels(&context.declarations).iter().all(|label| state.roots.contains(label)),
            "The saved synchronization record does not cover all requested dependencies. Run `gnrt sync --all` to process every registered declaration.");
        // Ensure another synchronization did not begin publishing during this check.
        ensure!(
            !marker.exists(),
            "Another synchronization started updating files during validation. Run the validation command again after that synchronization finishes."
        );
        println!("The dependency sources and GN build files are available for all requested declarations.");
        return Ok(());
    }

    let _lock = SyncLock::acquire(&vendor)?;
    sync_state::recover(&vendor)?;
    // Reuse the previous record only if its inputs, tools, and environment match.
    let old = SyncState::read(&state_path).ok();
    let previous = old.clone().filter(|state| {
        if !state.inputs.contains(&generator) {
            println!("The gnrt executable has changed. gnrt will regenerate the GN build files.");
            return false;
        }
        match state.validate_inputs(root) {
            Ok(()) => true,
            Err(error) => {
                println!("gnrt will synchronize the dependencies again because validation of the saved record failed: {error:#}");
                false
            }
        }
    });
    if previous.as_ref().is_some_and(|state| {
        state.validate(root).is_ok()
            && ((args.target.is_none() && state.complete)
                || !state.complete
                    && args.target.as_deref().is_some_and(|target| {
                        state.request(root, target, &normalized_args).is_some()
                    }))
    }) {
        println!("The saved synchronization record is valid. gnrt will reuse the existing dependency sources and GN build files.");
        return Ok(());
    }

    println!("gnrt is updating dependency sources and generating GN build files.");
    // Load project settings and collect declarations for this request.
    let config = BuildConfig::from_path(paths.third_party_config_file())?;
    let collection_out_dir = gnrt_out_dir.join("collect");
    let mut context = collect::collect(
        &collection_out_dir,
        &gnrt_out_dir,
        args.target.as_deref(),
        &args.args,
        &config,
    )
    .context(COLLECTION_ORDER_HINT)?;
    let requested_roots = sync_state::root_labels(&context.declarations);
    let catalog_digest = sync_state::digest(&serde_json::to_vec(&context.catalog)?);
    // Previous scoped requests cannot enlarge this request's feature union.
    let prepared_roots = requested_roots.clone();
    // Record GN inputs and effective arguments for this scoped request.
    let mut request_inputs = Vec::new();
    let mut effective_args = BTreeMap::new();
    if args.target.is_some() {
        request_inputs = capture_inputs(root, &gnrt_out_dir, context.collect_inputs.clone())?;
        effective_args = context.scopes[0].args.clone();
    }
    let mut requests = Vec::new();
    if let Some(target) = &args.target {
        requests.push(RequestRecord {
            target: target.clone(),
            args: normalized_args,
            effective_args,
            roots: requested_roots.into_iter().collect(),
            inputs: request_inputs,
        });
    }

    // Create a staging directory and begin a recoverable publication.
    let stage = tempfile::Builder::new()
        .prefix("publish-")
        .tempdir_in(&gnrt_out_dir)?;
    let mut publication = Publication::begin(&vendor)?;
    // Resolve dependencies and vendor the selected sources.
    let canonical_lockfile = resolve::resolve(&mut context, paths, &gnrt_out_dir)?;
    // Generate BUILD.gn files in staging before publishing them.
    let generated = generate::generate_to(&context, paths, stage.path())?;
    let destinations: BTreeSet<_> = generated.iter().cloned().collect();
    // Publish generated files, remove stale rules, and update the canonical lockfile.
    for destination in &generated {
        sync_state::validate_destination(destination)?;
        publication.write(
            &root.join(destination),
            &fs::read(stage.path().join(destination))?,
        )?;
    }
    if let Some(old) = &old {
        for artifact in &old.artifacts {
            let relative = PathBuf::from(&artifact.path);
            if artifact.kind == "file"
                && relative.starts_with(paths.third_party().join(".gnrt"))
                && !destinations.contains(&relative)
            {
                publication.remove(&root.join(relative))?;
            }
        }
    }
    remove_stale_crate_rules(root, &vendor, &destinations, &mut publication)?;
    let lockfile = config.resolve.cargo_lockfile_path(root)?;
    publication.write(&lockfile, canonical_lockfile.as_bytes())?;

    // Fingerprint synchronization inputs, outputs, environment values, and tool binaries.
    let mut inputs = vec![
        paths.third_party_config_file().to_path_buf(),
        root.join(".gn"),
        lockfile,
        std::env::current_exe()?,
    ];
    inputs.extend(context.collect_inputs.iter().cloned());
    for declaration in &context.catalog.gn {
        if let Declaration::Toolchain(toolchain) = declaration {
            let compiler = gnrt_lib::util::rustc_command(&toolchain.rustc).with_context(|| {
                format!(
                    "gnrt could not prepare the Rust compiler command for toolchain {}.",
                    toolchain.label
                )
            })?;
            inputs.push(PathBuf::from(compiler.get_program()));
        }
    }
    let config_dir = paths
        .third_party_config_file()
        .parent()
        .context("The configuration file path has no parent directory.")?;
    if !config.gn_config.build_file_template.as_os_str().is_empty() {
        inputs.push(config_dir.join(&config.gn_config.build_file_template));
    }
    inputs.extend(config.fingerprint.files.iter().map(|path| root.join(path)));
    for declaration in &context.catalog.cargo {
        if let Declaration::Crate(spec) = declaration {
            inputs.extend(
                spec.patches
                    .iter()
                    .map(|path| root.join(path.trim_start_matches("//"))),
            );
        }
    }
    // Patches referenced by the configuration affect the dependency sources.
    let patch_tree = root.join("external/rust/patches");
    if patch_tree.is_dir() {
        inputs.push(patch_tree);
    }
    let inputs = capture_inputs(root, &gnrt_out_dir, inputs)?;
    let mut artifact_paths: Vec<PathBuf> =
        generated.into_iter().map(|path| root.join(path)).collect();
    artifact_paths.extend(
        context
            .crates
            .values()
            .map(|info| root.join(info.path.trim_start_matches("//"))),
    );
    let artifacts = sync_state::fingerprints(root, artifact_paths)?;
    let environment_names: BTreeSet<String> =
        config.fingerprint.environment.iter().cloned().collect();
    let environment = environment_names
        .into_iter()
        .map(|name| {
            let value = sync_state::environment_value(root, &name);
            (name, value)
        })
        .collect();
    let mut tool_names: BTreeSet<String> = config.fingerprint.tools.iter().cloned().collect();
    tool_names.extend(["cargo".to_owned(), "gn".to_owned()]);
    let tools = tool_names
        .into_iter()
        .map(|name| {
            let record = sync_state::fingerprint(root, &sync_state::tool_path(&name)?)?;
            Ok((name, record))
        })
        .collect::<Result<_>>()?;
    let state = SyncState {
        version: sync_state::STATE_VERSION,
        complete: args.target.is_none(),
        catalog_sha256: catalog_digest,
        roots: prepared_roots.into_iter().collect(),
        inputs,
        artifacts,
        environment,
        tools,
        requests,
    };
    // Write the synchronization record last so it only describes fully published outputs.
    publication.commit(&state_path, &state)?;
    println!("gnrt successfully updated the dependency sources, GN build files, Cargo lockfile, and synchronization record.");
    Ok(())
}

/// Fingerprints synchronization inputs outside the mutable output workspace.
fn capture_inputs(root: &Path, output: &Path, inputs: Vec<PathBuf>) -> Result<Vec<FileRecord>> {
    let output = output
        .canonicalize()
        .unwrap_or_else(|_| output.to_path_buf());
    let inputs = inputs.into_iter().filter(|path| {
        let candidate = if path.is_absolute() {
            path.to_path_buf()
        } else {
            root.join(path)
        };
        !candidate
            .canonicalize()
            .unwrap_or(candidate)
            .starts_with(&output)
    });
    sync_state::fingerprints(root, inputs)
}

/// Journals deletion of obsolete generated rules while preserving manual files.
fn remove_stale_crate_rules(
    root: &Path,
    vendor: &Path,
    destinations: &BTreeSet<PathBuf>,
    publication: &mut Publication,
) -> Result<()> {
    for entry in fs::read_dir(vendor)? {
        let entry = entry?;
        let directory = entry.path();
        if !entry.file_type()?.is_dir() {
            continue;
        }
        if entry.file_name() == ".gnrt" {
            remove_legacy_rule_tree(&directory, publication)?;
            continue;
        }
        if entry.file_name().to_string_lossy().starts_with('.') {
            continue;
        }
        let rule = directory.join("BUILD.gn");
        if destinations.contains(rule.strip_prefix(root)?) {
            continue;
        }
        remove_generated_rule(&rule, publication)?;
    }
    Ok(())
}

/// Removes generated rules and empty directories from the legacy rule tree.
fn remove_legacy_rule_tree(directory: &Path, publication: &mut Publication) -> Result<()> {
    for entry in fs::read_dir(directory)? {
        let entry = entry?;
        let kind = entry.file_type()?;
        if kind.is_dir() {
            remove_legacy_rule_tree(&entry.path(), publication)?;
        } else if kind.is_file() && entry.file_name() == "BUILD.gn" {
            remove_generated_rule(&entry.path(), publication)?;
        }
    }
    if fs::read_dir(directory)?.next().is_none() {
        fs::remove_dir(directory)?;
    }
    Ok(())
}

/// Removes a rule only when its header identifies it as generated by gnrt.
fn remove_generated_rule(rule: &Path, publication: &mut Publication) -> Result<()> {
    if let Ok(contents) = fs::read_to_string(rule) {
        if contents.contains("@generated from") && contents.contains("by gnrt") {
            publication.remove(rule)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sync_without_gn_file_fails() {
        struct NoGnPaths {
            root: std::path::PathBuf,
        }
        impl crate::paths::GnrtPaths for NoGnPaths {
            fn root(&self) -> &std::path::Path {
                &self.root
            }
            fn third_party(&self) -> &std::path::Path {
                panic!("not under test")
            }
            fn third_party_cargo_root(&self) -> &std::path::Path {
                panic!("not under test")
            }
            fn third_party_config_file(&self) -> &std::path::Path {
                panic!("not under test")
            }
            fn get_vendor_dir_for_package(
                &self,
                _name: &str,
                _version: &semver::Version,
            ) -> std::path::PathBuf {
                panic!("not under test")
            }
            fn get_build_dir_for_package(
                &self,
                _name: &str,
                _version: &semver::Version,
            ) -> std::path::PathBuf {
                panic!("not under test")
            }
        }

        let dir = tempfile::tempdir().unwrap();
        let paths = NoGnPaths {
            root: dir.path().to_path_buf(),
        };
        let args = SyncCommandArgs {
            out: "out".into(),
            target: None,
            all: false,
            check: false,
            args: vec![],
        };
        let err = sync(args, &paths).expect_err("sync without .gn should fail");
        assert!(err.to_string().contains(".gn"), "got: {err}");
    }
}
