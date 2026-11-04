// Copyright 2022 The Chromium Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Paths and helpers for running within a Chromium or BlueOS checkout.

use crate::crates::{Epoch, NormalizedName};
use itertools::Itertools;
use std::env;
use std::io;
use std::path::{Path, PathBuf};

/// Common paths shared by Chromium and BlueOS checkout layouts.
///
/// All members other than `root` are relative to `root`.
pub trait GnrtPaths {
    /// The checkout root, as an absolute path.
    fn root(&self) -> &Path;

    /// Directory where BUILD.gn files are generated for third-party crates.
    fn third_party(&self) -> &Path;

    /// Cargo workspace root with Cargo.toml and Cargo.lock.
    // FIXME: Remove this compatibility root with the legacy Chromium commands.
    fn third_party_cargo_root(&self) -> &Path;

    /// The gnrt config file path.
    fn third_party_config_file(&self) -> &Path;

    /// Converts an absolute checkout path into a GN path.
    ///
    /// # Errors
    ///
    /// Returns an error if `path` is outside the checkout root.
    fn to_gn_abs_path(&self, path: &Path) -> Result<String, std::path::StripPrefixError> {
        Ok(normalize_unix_path_separator(
            path.strip_prefix(self.root())?,
        ))
    }

    /// Returns the metadata directory for a GN build output directory.
    fn gnrt_out_dir(&self, build_out_dir: &Path) -> PathBuf {
        build_out_dir.join("gnrt")
    }

    /// Returns the name of a directory where we want to vendor a third-party
    /// crate with the given `name` and `version`.
    fn get_vendor_dir_for_package(&self, name: &str, version: &semver::Version) -> PathBuf;

    /// Returns the name of a directory where we generate `BUILD.gn` and `README.chromium`.
    fn get_build_dir_for_package(&self, name: &str, version: &semver::Version) -> PathBuf;
}

/// Chromium source tree paths. All members other than `root` are relative to
/// `root`.
pub struct ChromiumPaths {
    /// The chromium/src checkout root, as an absolute path.
    pub root: PathBuf,
    /// The third_party/rust directory.
    pub third_party: &'static Path,
    /// The library directory relative to the root of the Rust source tree.
    pub rust_src_library_subdir: &'static Path,
    /// The vendor directory relative to the root of the Rust source tree.
    pub rust_src_vendor_subdir: &'static Path,
    /// The root of the Rust source tree that is installed in //third_party and
    /// used in the Chromium GN build.
    pub rust_src_installed: &'static Path,

    pub std_config_file: &'static Path,
    pub std_build: &'static Path,
    pub std_fake_root: &'static Path,
    pub std_fake_root_config_template: &'static Path,
    pub std_fake_root_cargo_template: &'static Path,

    pub third_party_cargo_root: &'static Path,
    pub third_party_config_file: &'static Path,
}

impl GnrtPaths for ChromiumPaths {
    fn root(&self) -> &Path {
        &self.root
    }

    fn third_party(&self) -> &Path {
        self.third_party
    }

    fn third_party_cargo_root(&self) -> &Path {
        self.third_party_cargo_root
    }

    fn third_party_config_file(&self) -> &Path {
        self.third_party_config_file
    }

    fn get_vendor_dir_for_package(&self, name: &str, version: &semver::Version) -> PathBuf {
        let epoch = Epoch::from_version(version);
        self.third_party_cargo_root()
            .join("vendor")
            .join(Path::new(&format!("{name}-{epoch}")))
    }

    fn get_build_dir_for_package(&self, name: &str, version: &semver::Version) -> PathBuf {
        self.third_party()
            .join(NormalizedName::from_crate_name(name).to_string())
            .join(Epoch::from_version(version).to_string())
    }
}

impl ChromiumPaths {
    /// Creates the Chromium path resolver from the current directory.
    ///
    /// # Errors
    ///
    /// Returns an error if the current directory or a required path is
    /// unavailable.
    pub fn new() -> io::Result<ChromiumPaths> {
        // We should be invoked from the repository root.
        let cur_dir = env::current_dir()?;

        Ok(ChromiumPaths {
            root: cur_dir.clone(),
            third_party: check_path(&cur_dir, RUST_THIRD_PARTY_DIR)?,
            // We tolerate the Rust sources being missing, as they are only used to generate
            // rules for the stdlib during Clang/Rust rolls, and they are not checked out for
            // most machines.
            rust_src_library_subdir: Path::new(RUST_SRC_LIBRARY_SUBDIR),
            // We tolerate the Rust sources being missing, as they are only used to generate
            // rules for the stdlib during Clang/Rust rolls, and they are not checked out for
            // most machines.
            rust_src_vendor_subdir: Path::new(RUST_SRC_VENDOR_SUBDIR),
            // We tolerate the toolchain package dir being missing, as it's not checked out
            // on the bots that generate Clang/Rust rolls.
            rust_src_installed: Path::new(RUST_SRC_INSTALLED_DIR),
            std_config_file: check_path(&cur_dir, STD_CONFIG_FILE)?,
            std_build: check_path(&cur_dir, STD_BUILD_DIR)?,
            std_fake_root: check_path(&cur_dir, STD_FAKE_ROOT)?,
            std_fake_root_config_template: check_path(&cur_dir, STD_FAKE_ROOT_CONFIG_TEMPLATE)?,
            std_fake_root_cargo_template: check_path(&cur_dir, STD_FAKE_ROOT_CARGO_TEMPLATE)?,

            third_party_cargo_root: check_path(&cur_dir, THIRD_PARTY_CARGO_ROOT)?,
            third_party_config_file: check_path(&cur_dir, THIRD_PARTY_CONFIG_FILE)?,
        })
    }
}

/// BlueOS source tree paths. All members other than `root` are relative to
/// `root`.
pub struct BlueOsPaths {
    /// The blueos checkout root, as an absolute path.
    pub root: PathBuf,
    /// The directory containing vendored crate sources and generated rules.
    pub third_party: PathBuf,
    /// The root containing the `vendor` directory.
    pub third_party_cargo_root: PathBuf,
    /// The gnrt config file path.
    pub third_party_config_file: PathBuf,
}

impl GnrtPaths for BlueOsPaths {
    fn root(&self) -> &Path {
        &self.root
    }

    fn third_party(&self) -> &Path {
        &self.third_party
    }

    fn third_party_cargo_root(&self) -> &Path {
        &self.third_party_cargo_root
    }

    fn third_party_config_file(&self) -> &Path {
        &self.third_party_config_file
    }

    fn to_gn_abs_path(&self, path: &Path) -> Result<String, std::path::StripPrefixError> {
        Ok(normalize_unix_path_separator(
            if let Ok(result) = path.strip_prefix(self.root()) {
                result
            } else {
                path
            },
        ))
    }

    fn get_vendor_dir_for_package(&self, name: &str, version: &semver::Version) -> PathBuf {
        let epoch = Epoch::from_version(version);
        self.third_party_cargo_root()
            .join("vendor")
            .join(Path::new(&format!("{name}-{epoch}")))
    }

    fn get_build_dir_for_package(&self, name: &str, version: &semver::Version) -> PathBuf {
        self.third_party().join(format!("{name}-{version}"))
    }
}

impl BlueOsPaths {
    /// Creates BlueOS paths from the current checkout and environment overrides.
    ///
    /// # Errors
    ///
    /// Returns an error if the current directory cannot be read.
    pub fn new() -> io::Result<BlueOsPaths> {
        let cur_dir = env::current_dir()?;

        Ok(BlueOsPaths {
            root: cur_dir.clone(),
            third_party: PathBuf::from(
                env::var("GNRT_THIRD_PARTY_DIR")
                    .unwrap_or_else(|_| BLUE_THIRD_PARTY_DIR.to_owned()),
            ),
            third_party_cargo_root: PathBuf::from(
                env::var("GNRT_THIRD_PARTY_CARGO_ROOT")
                    .unwrap_or_else(|_| BLUE_THIRD_PARTY_CARGO_ROOT.to_owned()),
            ),
            third_party_config_file: PathBuf::from(
                env::var("GNRT_THIRD_PARTY_CONFIG_FILE")
                    .unwrap_or_else(|_| BLUE_THIRD_PARTY_CONFIG_FILE.to_owned()),
            ),
        })
    }
}

/// Creates a paths implementation for the requested checkout layout.
///
/// - `"blueos"` (default) returns `BlueOsPaths`.
/// - `"chromium"` returns `ChromiumPaths`.
///
/// # Errors
///
/// Returns an error if the selected checkout paths cannot be initialized.
pub fn create_paths(kind: &str) -> io::Result<Box<dyn GnrtPaths>> {
    match kind {
        "chromium" => Ok(Box::new(ChromiumPaths::new()?)),
        _ => Ok(Box::new(BlueOsPaths::new()?)),
    }
}

// Chromium paths
static RUST_THIRD_PARTY_DIR: &str = "third_party/rust";
static RUST_SRC_LIBRARY_SUBDIR: &str = "library";
static RUST_SRC_VENDOR_SUBDIR: &str = "library/vendor";
static RUST_SRC_INSTALLED_DIR: &str = "third_party/rust-toolchain/lib/rustlib/src/rust";

static STD_CONFIG_FILE: &str = "build/rust/std/gnrt_config.toml";
static STD_BUILD_DIR: &str = "build/rust/std/rules";
static STD_FAKE_ROOT: &str = "build/rust/std/fake_root";
static STD_FAKE_ROOT_CONFIG_TEMPLATE: &str = "build/rust/std/fake_root/.cargo/config.toml.template";
static STD_FAKE_ROOT_CARGO_TEMPLATE: &str = "build/rust/std/fake_root/Cargo.toml.template";

static THIRD_PARTY_CARGO_ROOT: &str = "third_party/rust/chromium_crates_io";
static THIRD_PARTY_CONFIG_FILE: &str = "third_party/rust/chromium_crates_io/gnrt_config.toml";

// BlueOS paths
static BLUE_THIRD_PARTY_DIR: &str = "external/vendor";
// FIXME: Remove this compatibility root with the legacy Chromium commands.
static BLUE_THIRD_PARTY_CARGO_ROOT: &str = "external";
static BLUE_THIRD_PARTY_CONFIG_FILE: &str = "external/gnrt_config.toml";

fn check_path<'a>(root: &Path, p_str: &'a str) -> io::Result<&'a Path> {
    let p = Path::new(p_str);
    if !root.join(p).exists() {
        return Err(io::Error::other(format!(
            "could not find {} (invoked from Chromium checkout root?)",
            p.display()
        )));
    }

    Ok(p)
}

/// Normalizes path separators to `/` for use in GN files.
pub fn normalize_unix_path_separator(path: impl AsRef<Path>) -> String {
    // `Path`s on windows use `\` separators and we need to use `/` in GN strings.
    let path = path.as_ref();
    path.iter()
        .map(|comp| {
            comp.to_str()
                .unwrap_or_else(|| panic!("non-UTF-8 in path {path:?}"))
        })
        .join("/")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normalize() {
        assert_eq!(normalize_unix_path_separator(Path::new("rel")), "rel");
        assert_eq!(
            normalize_unix_path_separator(&Path::new("a").join("b")),
            "a/b"
        );
    }

    #[test]
    fn blueos_crate_paths_share_vendor_root() {
        let paths = BlueOsPaths {
            root: PathBuf::new(),
            third_party: PathBuf::from(BLUE_THIRD_PARTY_DIR),
            third_party_cargo_root: PathBuf::from(BLUE_THIRD_PARTY_CARGO_ROOT),
            third_party_config_file: PathBuf::from(BLUE_THIRD_PARTY_CONFIG_FILE),
        };
        let paths: &dyn GnrtPaths = &paths;
        let version = semver::Version::new(1, 2, 3);

        assert_eq!(
            paths.get_vendor_dir_for_package("serde", &version),
            PathBuf::from("external/vendor/serde-v1")
        );
        assert_eq!(
            paths.get_build_dir_for_package("serde", &version),
            PathBuf::from("external/vendor/serde-1.2.3")
        );
        assert_eq!(
            paths.third_party_config_file(),
            Path::new("external/gnrt_config.toml")
        );
    }

    #[test]
    fn blueos_build_paths_preserve_crate_names_and_versions() {
        let paths = BlueOsPaths {
            root: PathBuf::new(),
            third_party: PathBuf::from("custom/crates"),
            third_party_cargo_root: PathBuf::from("custom/cargo"),
            third_party_config_file: PathBuf::from("custom/config.toml"),
        };

        assert_eq!(
            paths.get_build_dir_for_package("proc-macro2", &semver::Version::new(1, 0, 103)),
            PathBuf::from("custom/crates/proc-macro2-1.0.103")
        );
        assert_ne!(
            paths.get_build_dir_for_package("proc-macro2", &semver::Version::new(1, 0, 103)),
            paths.get_build_dir_for_package("proc-macro2", &semver::Version::new(1, 0, 104))
        );
    }
}
