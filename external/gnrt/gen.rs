// Copyright 2023 The Chromium Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use crate::config;
use crate::crates::{self, CrateFiles, VendoredCrate};
use crate::deps;
use crate::gn;
use crate::paths::{self};
use crate::util::{
    check_exit_ok, check_spawn, check_wait_with_output, create_dirs_if_needed,
    get_guppy_package_graph, init_handlebars_with_template_paths, render_handlebars,
};
use crate::GenCommandArgs;

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{format_err, Context, Result};
use rayon::prelude::*;

/// Generate GN build rules for third-party crates.
///
/// 1. Using `cargo` / `guppy` in offline mode to resolve transitive
///    dependencies of `Cargo.toml`
/// 2. Generating all required `BUILD.gn` files
pub fn generate(args: GenCommandArgs, paths: &dyn paths::GnrtPaths) -> Result<()> {
    let config = config::BuildConfig::from_path(paths.third_party_config_file())?;

    let cargo_extra_options = vec!["--offline".to_string(), "--locked".to_string()];

    // Compute the set of all third-party crates.
    let dependencies = deps::collect_dependencies(
        &get_guppy_package_graph(
            paths.third_party_cargo_root().into(),
            cargo_extra_options,
            HashMap::new(),
        )?,
        &config.resolve.root,
        &config,
    )?;

    println!("Discovering `sources` and `inputs` of crates ...");
    let crate_inputs: HashMap<VendoredCrate, CrateFiles> = dependencies
        .iter()
        .map(|p| {
            crates::collect_crate_files(p, &config, crates::IncludeCrateTargets::LibAndBin)
                .unwrap_or_else(|e| {
                    panic!(
                        "missing a crate input file for '{}'. Dependencies are not vendored?\n\
                         note: {}",
                        p.package_name, e
                    )
                })
        })
        .collect();

    // If there are multiple crates with the same epoch, this is unexpected.
    // Bail out.
    {
        let mut found = HashSet::new();
        for dep in &dependencies {
            let epoch = crates::Epoch::from_version(&dep.version);
            if !found.insert((&dep.package_name, epoch)) {
                Err(format_err!(
                    "Two '{}' crates found with the same {} epoch",
                    dep.package_name,
                    epoch
                ))?
            }
        }
    }

    // Split up the dependencies by crate and epoch.
    let all_build_files: HashMap<PathBuf, gn::BuildFile> = {
        let mut map = HashMap::new();
        for dep in &dependencies {
            let build_file = gn::build_file_from_deps(
                std::iter::once(dep),
                paths,
                &config,
                // TODO(danakj): Change to PackageName for consistency?
                gn::NameLibStyle::LibLiteral,
                |crate_id| crate_inputs.get(crate_id).unwrap(),
            )?;
            let path = paths.get_build_dir_for_package(&dep.package_name, &dep.version);
            let previous = map.insert(path, build_file);
            if previous.is_some() {
                Err(format_err!(
                    "multiple versions of crate {} with the same epoch",
                    dep.package_name
                ))?
            }
        }
        map
    };

    for dir in all_build_files.keys() {
        create_dirs_if_needed(dir).context(format!("dir: {}", dir.display()))?;
    }

    if args.dump_template_input {
        for (dir, build_file) in &all_build_files {
            serde_json::to_writer_pretty(
                std::fs::File::create(dir.join("gnrt-template-input.json"))
                    .context("opening dump file")?,
                &build_file,
            )
            .context("dumping gn information")?;
        }
        return Ok(());
    }

    println!("Generating `BUILD.gn` files ...");
    let build_file_template_path = paths
        .third_party_config_file()
        .parent()
        .unwrap()
        .join(&config.gn_config.build_file_template);
    let handlebars = init_handlebars_with_template_paths(&[&build_file_template_path])?;
    all_build_files
        .into_par_iter()
        .try_for_each(|(dir, build_file)| -> Result<()> {
            let build_file_path = dir.join("BUILD.gn");
            render_handlebars(
                &handlebars,
                &build_file_template_path,
                &build_file,
                &build_file_path,
            )?;
            if let Err(err) = format_build_file(&build_file_path) {
                log::warn!(
                    "Ignoring the following `gn format` failure: {err}. \
                 Please format the generated file(s) manually."
                );
            }
            Ok(())
        })?;
    Ok(())
}

/// Generate GN build rules for the Rust std library.
///
/// Uses Chromium's std build configuration to generate BUILD.gn rules
/// from the vendored Rust stdlib sources.
#[cfg(feature = "chromium")]
pub fn generate_for_std(args: GenCommandArgs, paths: &paths::ChromiumPaths) -> Result<()> {
    let config = config::BuildConfig::from_path(paths.std_config_file)?;

    let build_file_template_path = paths
        .std_config_file
        .parent()
        .unwrap()
        .join(&config.gn_config.build_file_template);

    let handlebars = init_handlebars_with_template_paths(&[&build_file_template_path])?;

    let rust_src_root = paths::normalize_unix_path_separator(args.for_std.as_ref().unwrap());
    println!("Generating stdlib GN rules from {rust_src_root}");

    let cargo_config = std::fs::read_to_string(paths.std_fake_root_config_template)
        .unwrap()
        .replace("RUST_SRC_ROOT", &rust_src_root);
    std::fs::write(
        strip_template(paths.std_fake_root_config_template).unwrap(),
        cargo_config,
    )
    .unwrap();

    let cargo_toml = std::fs::read_to_string(paths.std_fake_root_cargo_template)
        .unwrap()
        .replace("RUST_SRC_ROOT", &rust_src_root);
    std::fs::write(
        strip_template(paths.std_fake_root_cargo_template).unwrap(),
        cargo_toml,
    )
    .unwrap();

    let rust_src_root = paths
        .root
        .join(Path::new(&rust_src_root))
        .canonicalize()
        .unwrap();

    let mut std_fake_root_cargo_lock = paths.std_fake_root.to_path_buf();
    std_fake_root_cargo_lock.push("Cargo.lock");
    if let Err(e) = std::fs::remove_file(std_fake_root_cargo_lock) {
        match e.kind() {
            std::io::ErrorKind::NotFound => (),
            _ => panic!("io error while deleting Cargo.lock: {e}"),
        }
    }

    let cargo_extra_env: HashMap<std::ffi::OsString, std::ffi::OsString> =
        [("RUSTC_BOOTSTRAP".into(), "1".into())]
            .into_iter()
            .collect();

    let cargo_extra_options = vec!["--offline".to_string()];

    let mut dependencies = {
        let metadata = get_guppy_package_graph(
            paths.std_fake_root.into(),
            cargo_extra_options,
            cargo_extra_env,
        )
        .with_context(|| {
            format!(
                "Failed to parse cargo metadata in a directory synthesized from \
                         {} and {}",
                paths.std_fake_root_cargo_template.display(),
                paths.std_fake_root_config_template.display(),
            )
        })?;
        deps::collect_dependencies(&metadata, &config.resolve.root, &config)?
    };

    dependencies.retain(|dep| {
        dep.dependency_kinds
            .contains_key(&deps::DependencyKind::Normal)
    });

    for dep in dependencies.iter_mut() {
        let gn_prefix = paths.root.join(paths.rust_src_installed);
        if let Some(lib) = dep.lib_target.as_mut() {
            anyhow::ensure!(
                lib.root.canonicalize().unwrap().starts_with(&rust_src_root),
                "Found dependency that was not locally available: {} {}\n{:?}",
                dep.package_name,
                dep.version,
                dep
            );

            if let Ok(remain) = lib
                .root
                .canonicalize()
                .unwrap()
                .strip_prefix(&rust_src_root)
            {
                lib.root = gn_prefix.join(remain);
            }
        }

        if let Some(path) = dep.build_script.as_mut() {
            if let Ok(remain) = path.canonicalize().unwrap().strip_prefix(&rust_src_root) {
                *path = gn_prefix.join(remain);
            }
        }
    }

    let third_party_deps = dependencies
        .iter()
        .filter(|dep| !dep.is_local)
        .collect::<Vec<_>>();

    let vendored_crates: HashSet<crates::VendoredCrate> =
        crates::collect_std_vendored_crates(&rust_src_root.join(paths.rust_src_vendor_subdir))
            .context("Collecting vendored `std` crates")?
            .into_iter()
            .collect();

    for dep in third_party_deps.iter() {
        if dep.lib_target.is_none() {
            continue;
        }

        vendored_crates
            .get(&crates::VendoredCrate {
                name: dep.package_name.clone(),
                version: dep.version.clone(),
            })
            .ok_or_else(|| {
                anyhow::format_err!(
                    "Resolved dependency does not match any vendored crate: {} {}",
                    dep.package_name,
                    dep.version
                )
            })?;
    }

    let crate_inputs: HashMap<crates::VendoredCrate, crates::CrateFiles> = dependencies
        .iter()
        .filter(|p| p.lib_target.is_some())
        .map(|p| {
            crates::collect_crate_files(p, &config, crates::IncludeCrateTargets::LibOnly)
                .with_context(|| format!("Failed to collect crate files for {p}"))
        })
        .collect::<Result<_>>()?;

    let build_file = gn::build_file_from_deps(
        dependencies.iter(),
        paths,
        &config,
        gn::NameLibStyle::PackageName,
        |crate_id| crate_inputs.get(crate_id).unwrap(),
    )?;

    if args.dump_template_input {
        return serde_json::to_writer_pretty(
            std::fs::File::create("gnrt-template-input.json").context("opening dump file")?,
            &build_file,
        )
        .context("dumping gn information");
    }

    let build_gn_path = paths.std_build.join("BUILD.gn");
    render_handlebars(
        &handlebars,
        &build_file_template_path,
        &build_file,
        &build_gn_path,
    )?;
    format_build_file(&build_gn_path)?;

    Ok(())
}

/// Strips the `.template` extension from a file path.
#[cfg(feature = "chromium")]
fn strip_template(path: &Path) -> Option<PathBuf> {
    if path.extension()? != "template" {
        None
    } else {
        let mut buf = path.to_owned();
        buf.set_file_name(path.file_stem()?);
        Some(buf)
    }
}

/// Runs `gn format` command to format a `BUILD.gn` file at the given path.
pub fn format_build_file(path_to_build_gn_file: &Path) -> Result<()> {
    let cmd_name = "gn format";
    check_spawn(
        Command::new(if cfg!(windows) { "gn.bat" } else { "gn" })
            .arg("format")
            .arg(path_to_build_gn_file)
            // Discard `Wrote formatted to '//.../BUILD>gn'` messages.
            .stdout(Stdio::null()),
        cmd_name,
    )
    .and_then(|child| check_wait_with_output(child, cmd_name))
    .and_then(|output| check_exit_ok(&output, cmd_name))
    .with_context(|| format!("Error formatting `{}`", path_to_build_gn_file.display()))
}
