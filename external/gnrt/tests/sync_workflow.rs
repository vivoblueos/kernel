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

//! Exercises synchronization, offline validation, and native GN builds.

use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// An isolated GN project with local Git dependencies and explicit tool bindings.
struct Fixture {
    directory: tempfile::TempDir,
    gn: PathBuf,
    cargo: PathBuf,
    rustc: PathBuf,
}

/// Finds a test prerequisite on PATH.
fn find_tool(name: &str) -> PathBuf {
    std::env::split_paths(&std::env::var_os("PATH").expect("PATH is required"))
        .map(|directory| directory.join(name))
        .find(|path| path.is_file())
        .unwrap_or_else(|| panic!("integration tests require {name} on PATH"))
}

/// Resolves the selected tool before fixture commands change their working directory.
fn selected_tool(name: &str) -> PathBuf {
    let executable = gnrt_lib::sync_state::tool_path(name)
        .unwrap()
        .canonicalize()
        .unwrap();
    if executable.file_stem().and_then(|name| name.to_str()) != Some("rustup") {
        return executable;
    }
    let output = Command::new(executable)
        .args(["which", name])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .unwrap();
    assert_success(&output);
    PathBuf::from(String::from_utf8(output.stdout).unwrap().trim())
        .canonicalize()
        .unwrap()
}

/// Reports child-process output when a test command fails.
fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

impl Fixture {
    /// Creates declarations, toolchain metadata, and an offline Cargo source cache.
    fn new() -> Self {
        let fixture = Self {
            directory: tempfile::tempdir().unwrap(),
            gn: std::env::var_os("GNRT_GN_BIN")
                .map(PathBuf::from)
                .unwrap_or_else(|| find_tool("gn")),
            cargo: selected_tool("cargo"),
            rustc: selected_tool("rustc"),
        };
        fixture.write(
            "source/Cargo.toml",
            r#"
[package]
name = "variant-lib"
version = "1.0.0"
edition = "2021"
[features]
a = []
b = []
probe = []
"#,
        );
        fixture.write(
            "source/src/lib.rs",
            r#"
#[cfg(all(feature = "a", feature = "b"))]
compile_error!("features a and b are mutually exclusive");
#[cfg(all(feature = "a", not(gnrt_probe_a)))]
compile_error!("declaration a rustflags are missing");
#[cfg(all(feature = "b", not(gnrt_probe_b)))]
compile_error!("declaration b rustflags are missing");
pub fn value() -> u8 { 1 }
#[cfg(not(feature = "probe"))]
compile_error!("conditional feature is missing");
#[cfg(gnrt_unexpected)]
compile_error!("inactive conditional rustflags were enabled");
"#,
        );
        for arguments in [
            vec!["init", "--quiet"],
            vec!["add", "."],
            vec![
                "-c",
                "user.name=Fixture",
                "-c",
                "user.email=fixture@example.invalid",
                "commit",
                "--quiet",
                "-m",
                "fixture",
            ],
        ] {
            assert_success(
                &Command::new(find_tool("git"))
                    .current_dir(fixture.root().join("source"))
                    .args(arguments)
                    .output()
                    .unwrap(),
            );
        }
        fixture.write(
            ".gn",
            "buildconfig = \"//build/BUILDCONFIG.gn\"\nscript_executable = \"python3\"\n",
        );
        fixture.write(
            "build/BUILDCONFIG.gn",
            r#"
declare_args() {
  gnrt_mode = "build"
  product = "default"
}
set_default_toolchain("//build/toolchain:host")
build_ctx = { toolchain_cfgs = [] }
host_build_ctx = build_ctx
"#,
        );
        fixture.write(
            "build/toolchain/BUILD.gn",
            r#"
toolchain("host") {
  tool("stamp") { command = "touch {{output}}" }
  tool("action") {}
}
"#,
        );
        fixture.write(
            "external/gnrt_config.toml",
            r#"
[collect]
declaration_files = ["catalog/BUILD.gn"]
[resolve]
root = "fixture_crates_io"
cargo_lockfile = "external/rust/Cargo.lock"
remove_crates = []
remove_crates_when = []
[gn]
build_file_template = "../build/CARGO_BUILD.gn.hbs"
"#,
        );
        fixture.write(
            "build/CARGO_BUILD.gn.hbs",
            &fs::read_to_string(
                Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/CARGO_BUILD.gn.hbs"),
            )
            .unwrap(),
        );
        fixture.write(
            "build/templates/cargo_crate.gni",
            r#"
template("cargo_crate") {
  _sources = invoker.sources
  action(target_name) {
    script = "//build/compile.py"
    sources = invoker.sources
    outputs = [ "$target_gen_dir/${target_name}.rlib" ]
    args = [ rebase_path(_sources[0], root_build_dir),
             rebase_path(outputs[0], root_build_dir), invoker.rustc_metadata ]
    foreach(feature, invoker.features) { args += [ feature ] }
    args += [ "--" ] + invoker.rustflags
  }
  not_needed(invoker, "*")
}
"#,
        );
        fixture.write(
            "build/compile.py",
            r#"
import os
import pathlib
import subprocess
import sys
source, output, metadata, *arguments = sys.argv[1:]
separator = arguments.index('--')
features = arguments[:separator]
rustflags = arguments[separator + 1:]
pathlib.Path(output).parent.mkdir(parents=True, exist_ok=True)
args = [os.environ['RUSTC'], source, '--crate-name=variant_lib', '--crate-type=rlib',
        '--edition=2021', '-C', 'metadata=' + metadata, '-o', output]
args += rustflags
for feature in features:
    args += ['--cfg', 'feature="' + feature + '"']
subprocess.run(args, check=True)
"#,
        );
        let git_url = format!("file://{}", fixture.root().join("source").display());
        // Populate Cargo's Git cache using only the local file URL. The sync
        // commands below then run with network access disabled by Cargo.
        fixture.write("seed/Cargo.toml", &format!(
            "[package]\nname = \"seed\"\nversion = \"0.1.0\"\nedition = \"2021\"\n[dependencies]\nvariant-lib = {{ git = \"{git_url}\" }}\n"));
        fixture.write("seed/src/lib.rs", "");
        assert_success(
            &fixture
                .command(&fixture.cargo)
                .current_dir(fixture.root().join("seed"))
                .env("CARGO_NET_OFFLINE", "false")
                .arg("fetch")
                .output()
                .unwrap(),
        );
        fixture.write(
            "build/templates/cargo.gni",
            &fs::read_to_string(
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("tests/fixtures/build/templates/cargo.gni"),
            )
            .unwrap()
            .replace("//external/rust", "//catalog"),
        );
        fixture.write(
            "build/scripts/check_gnrt_sync.py",
            &fs::read_to_string(
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("tests/fixtures/build/scripts/check_gnrt_sync.py"),
            )
            .unwrap(),
        );
        fixture.write(
            "build/config/gnrt_sync.gni",
            &fs::read_to_string(
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("tests/fixtures/build/config/gnrt_sync.gni"),
            )
            .unwrap(),
        );
        let declarations = "import(\"//build/templates/cargo.gni\")\n".to_owned()
            + &["a", "b"]
                .into_iter()
                .map(|feature| {
                    format!(
                        r#"
cargo_spec("library_{feature}") {{
  package = "variant-lib"
  version = "=1.0.0"
  features = [
    "{feature}",
    {{
      condition = "product != \"disabled\""
      values = [ "probe" ]
    }},
  ]
  rustflags = [
    "--cfg=gnrt_base",
    {{
      condition = "product != \"disabled\""
      values = [ "--cfg=gnrt_probe_{feature}", "-Copt-level=1" ]
    }},
    {{
      condition = "product == \"disabled\""
      values = [ "--cfg=gnrt_unexpected" ]
    }},
    "-Copt-level=2",
  ]
  default_features = false
  isolation = "closure"
  git = "{git_url}"
}}
"#
                    )
                })
                .collect::<String>();
        fixture.write("catalog/BUILD.gn", &declarations);
        fixture.write("product_b.txt", "product b input\n");
        fixture.write(
            "BUILD.gn",
            r#"
_a = "//catalog:library_a"
_b = "//catalog:library_b"
if (product == "b") {
  _input = read_file("//product_b.txt", "string")
  not_needed([ "_input" ])
}
if (gnrt_mode != "collect") {
  _index = read_file("//third_party/gnrt_crate_index.json", "json")
  foreach(entry, _index.crates) {
    if (entry.proxy == _a) { _a = entry.target_label }
    if (entry.proxy == _b) { _b = entry.target_label }
  }
}
group("product_a") { deps = [ _a ] }
group("product_b") { deps = [ _b ] }
group("default") { deps = [ ":product_a", ":product_b" ] }
"#,
        );
        fixture
    }

    /// Returns the temporary project root.
    fn root(&self) -> &Path {
        self.directory.path()
    }

    /// Writes a fixture file and creates its parent directories.
    fn write(&self, relative: &str, contents: &str) {
        let path = self.root().join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    /// Creates a command with isolated Cargo storage and selected tool overrides.
    fn command(&self, executable: impl AsRef<std::ffi::OsStr>) -> Command {
        let mut command = Command::new(executable);
        command
            .current_dir(self.root())
            .env("GNRT_GN_BIN", &self.gn)
            .env("GNRT_CARGO_BIN", &self.cargo)
            .env("GNRT_THIRD_PARTY_DIR", "third_party")
            .env("GNRT_THIRD_PARTY_CARGO_ROOT", "third_party")
            .env_remove("GNRT_THIRD_PARTY_CONFIG_FILE")
            .env("CARGO_HOME", self.root().join("cargo-home"))
            .env("RUSTC", &self.rustc)
            .env("CARGO_NET_OFFLINE", "true")
            .env_remove("GNRT_TEST_FLAG");
        command
    }

    /// Runs the gnrt binary under test against this fixture.
    fn sync(&self, arguments: &[&str]) -> Output {
        self.command(env!("CARGO_BIN_EXE_gnrt"))
            .arg("sync")
            .args(arguments)
            .output()
            .unwrap()
    }

    /// Reads the published declaration-to-target index.
    fn index(&self) -> Value {
        serde_json::from_slice(
            &fs::read(self.root().join("third_party/gnrt_crate_index.json")).unwrap(),
        )
        .unwrap()
    }

    /// Validates the state through the independent offline checker.
    fn native_check(&self) -> Value {
        let checker = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/build/scripts/check_gnrt_sync.py");
        let output = self
            .command(find_tool("python3"))
            .arg(checker)
            .arg("--root")
            .arg(self.root())
            .args([
                "--state",
                "third_party/gnrt_sync_state.json",
                "--args-file",
                "out/native/args.gn",
            ])
            .output()
            .unwrap();
        assert_success(&output);
        serde_json::from_slice(&output.stdout).unwrap()
    }

    /// Generates and compiles the fixture with GN and Ninja.
    fn native_build(&self) {
        assert_success(
            &self
                .command(&self.gn)
                .args(["gen", "out/native", "--args=gnrt_mode=\"build\""])
                .output()
                .unwrap(),
        );
        assert_success(
            &self
                .command(find_tool("ninja"))
                .args(["-C", "out/native"])
                .output()
                .unwrap(),
        );
    }
}

#[test]
fn full_sync_collects_the_catalog_without_product_entries() {
    let fixture = Fixture::new();
    fixture.write(
        "BUILD.gn",
        r#"
group("default") {
  if (product == "b") {
    deps = [ "//catalog:library_b" ]
  } else {
    deps = [ "//catalog:library_a" ]
  }
}
"#,
    );
    assert_success(&fixture.sync(&["--all", "--args", "product=\"default\""]));
    let collection: Value = serde_json::from_slice(
        &fs::read(fixture.root().join("out/gnrt-sync/declarations.json")).unwrap(),
    )
    .unwrap();
    assert!(collection["scopes"].as_array().unwrap().is_empty());
    assert_eq!(
        collection["declarations"]["cargo"]
            .as_array()
            .unwrap()
            .len(),
        2
    );
    assert_eq!(fixture.index()["crates"].as_array().unwrap().len(), 2);
}

#[test]
fn full_sync_is_portable_and_compiles_mutually_exclusive_instances() {
    let fixture = Fixture::new();
    let toolchains = fs::read_to_string(fixture.root().join("build/toolchain/BUILD.gn")).unwrap();
    fixture.write(
        "build/toolchain/BUILD.gn",
        &format!(
            r#"{toolchains}
group("host_metadata") {{
  metadata = {{ gnrt_declarations = [{{
    type = "toolchain"
    origin = "gn"
    label = "//build/toolchain:host"
    role = "host"
    cc = "clang"
    cxx = "clang++"
    ar = "llvm-ar"
    rustc = {}
    target_triple = "declared"
    llvm_target = "host"
  }}] }}
}}
"#,
            serde_json::to_string(&format!("{} --target=declared", fixture.rustc.display()))
                .unwrap()
        ),
    );
    let config = fs::read_to_string(fixture.root().join("external/gnrt_config.toml")).unwrap();
    fixture.write(
        "external/gnrt_config.toml",
        &config.replace(
            "[resolve]",
            "[fingerprint]\nfiles = [\"sync-input.txt\"]\nenvironment = [\"GNRT_TEST_FLAG\"]\ntools = [\"python3\"]\n[resolve]\ntoolchain_file = \"build/toolchain/BUILD.gn\"",
        ),
    );
    fixture.write("sync-input.txt", "original settings\n");
    assert_success(&fixture.sync(&["--all"]));
    let index = fixture.index();
    assert_eq!(index["version"], 1);
    let state: Value = serde_json::from_slice(
        &fs::read(fixture.root().join("third_party/gnrt_sync_state.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(state["version"], 1);
    assert!(state["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .any(|input| input["path"].as_str() == fixture.rustc.to_str()));
    assert_eq!(index["crates"].as_array().unwrap().len(), 2);
    assert_ne!(
        index["crates"][0]["target_label"],
        index["crates"][1]["target_label"]
    );
    let mut target_names = std::collections::BTreeSet::new();
    for entry in index["crates"].as_array().unwrap() {
        assert_ne!(entry["target_label"], entry["host_label"]);
        for context in ["target", "host"] {
            let label = entry[format!("{context}_label")].as_str().unwrap();
            let (directory, target_name) = label.trim_start_matches("//").split_once(':').unwrap();
            assert_eq!(directory, "third_party/variant-lib-1.0.0");
            assert!(target_names.insert(target_name));
            let hash = target_name
                .strip_prefix(&format!("variant_lib_variant_{context}_"))
                .unwrap();
            assert_eq!(hash.len(), 12);
            assert!(hash.bytes().all(|value| value.is_ascii_hexdigit()));
            let generated =
                fs::read_to_string(fixture.root().join(directory).join("BUILD.gn")).unwrap();
            assert!(!generated.contains(fixture.root().to_str().unwrap()));
            assert!(generated.contains("CARGO_MANIFEST_DIR=\" + rebase_path("));
            assert!(generated.contains(&format!("context = \"{context}\"")));
            let compact = generated.split_whitespace().collect::<String>();
            assert!(compact.contains(&format!("cargo_crate(\"{target_name}\")")));
            assert!(generated.contains("crate_name = \"variant_lib\""));
            assert_eq!(generated.matches("cargo_crate(").count(), 4);
        }
    }
    assert_eq!(target_names.len(), 4);
    assert!(!fixture.root().join("third_party/.gnrt").exists());

    let sources = fs::read_dir(fixture.root().join("third_party"))
        .unwrap()
        .filter_map(Result::ok)
        .filter(|entry| {
            entry
                .file_name()
                .to_string_lossy()
                .starts_with("variant-lib-")
        })
        .count();
    assert_eq!(sources, 1);
    fixture.native_build();
    let checked = fixture.native_check();
    assert_eq!(checked["valid"], true, "{checked}");
    let index_path = fixture.root().join("third_party/gnrt_crate_index.json");
    let modified = fs::metadata(&index_path).unwrap().modified().unwrap();
    let lock = fs::read(fixture.root().join("external/rust/Cargo.lock")).unwrap();
    assert_success(&fixture.sync(&[]));
    assert_eq!(
        fs::metadata(&index_path).unwrap().modified().unwrap(),
        modified
    );
    assert_eq!(
        fs::read(fixture.root().join("external/rust/Cargo.lock")).unwrap(),
        lock
    );
    assert_success(&fixture.sync(&["--check"]));
    let source_path = fixture
        .root()
        .join("third_party/variant-lib-1.0.0/src/lib.rs");
    let source = fs::read(&source_path).unwrap();
    fs::remove_file(&source_path).unwrap();
    assert_eq!(fixture.native_check()["valid"], false);
    assert!(!fixture.sync(&["--check"]).status.success());
    fs::write(source_path, source).unwrap();
    let checked = fixture.native_check();
    assert_eq!(checked["valid"], true, "{checked}");

    fixture.write("sync-input.txt", "changed settings\n");
    assert!(!fixture.sync(&["--check"]).status.success());
    fixture.write("sync-input.txt", "original settings\n");

    let environment_check = fixture
        .command(env!("CARGO_BIN_EXE_gnrt"))
        .args(["sync", "--check"])
        .env("GNRT_TEST_FLAG", "changed")
        .output()
        .unwrap();
    assert!(!environment_check.status.success());
    assert!(String::from_utf8_lossy(&environment_check.stderr)
        .contains("The value of environment variable GNRT_TEST_FLAG has changed"));

    let tool_check = fixture
        .command(env!("CARGO_BIN_EXE_gnrt"))
        .args(["sync", "--check"])
        .env("GNRT_CARGO_BIN", &fixture.rustc)
        .output()
        .unwrap();
    assert!(!tool_check.status.success());
    assert!(
        String::from_utf8_lossy(&tool_check.stderr).contains("The cargo executable has changed")
    );
    assert_success(&fixture.sync(&["--check"]));
}

#[test]
fn sync_migrates_legacy_rules_and_removes_obsolete_instances() {
    let fixture = Fixture::new();
    assert_success(&fixture.sync(&["--all"]));
    let index = fixture.index();
    let obsolete = index["crates"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["proxy"] == "//catalog:library_b")
        .unwrap();
    let legacy = "third_party/.gnrt/legacy/variant-lib-1.0.0/BUILD.gn";
    let header = "# @generated from build/CARGO_BUILD.gn.hbs by gnrt\n";
    fixture.write(legacy, header);
    let unrecorded = "third_party/.gnrt/unrecorded/variant-lib-1.0.0/BUILD.gn";
    fixture.write(unrecorded, header);
    fixture.write(
        "third_party/.gnrt/notes.txt",
        "Retain files not generated by gnrt.\n",
    );
    fixture.write("third_party/obsolete-1.0.0/BUILD.gn", header);
    fixture.write(
        "third_party/manual-1.0.0/BUILD.gn",
        "group(\"manual\") {}\n",
    );
    let state_path = fixture.root().join("third_party/gnrt_sync_state.json");
    let mut state = gnrt_lib::sync_state::SyncState::read(&state_path).unwrap();
    state
        .artifacts
        .push(gnrt_lib::sync_state::fingerprint(fixture.root(), Path::new(legacy)).unwrap());
    fs::write(&state_path, serde_json::to_vec_pretty(&state).unwrap()).unwrap();

    let catalog = fs::read_to_string(fixture.root().join("catalog/BUILD.gn")).unwrap();
    fixture.write(
        "catalog/BUILD.gn",
        &catalog[..catalog.find("cargo_spec(\"library_b\")").unwrap()],
    );
    fixture.write(
        "BUILD.gn",
        r#"
_a = "//catalog:library_a"
if (gnrt_mode != "collect") {
  _index = read_file("//third_party/gnrt_crate_index.json", "json")
  foreach(entry, _index.crates) {
    if (entry.proxy == _a) { _a = entry.target_label }
  }
}
group("default") { deps = [ _a ] }
"#,
    );
    assert_success(&fixture.sync(&["--all"]));
    assert!(!fixture.root().join(legacy).exists());
    assert!(!fixture.root().join(unrecorded).exists());
    assert!(!fixture.root().join("third_party/.gnrt/legacy").exists());
    assert!(!fixture.root().join("third_party/.gnrt/unrecorded").exists());
    assert!(fixture.root().join("third_party/.gnrt/notes.txt").exists());
    assert!(!fixture
        .root()
        .join("third_party/obsolete-1.0.0/BUILD.gn")
        .exists());
    assert!(fixture
        .root()
        .join("third_party/manual-1.0.0/BUILD.gn")
        .exists());
    let generated = fs::read_to_string(
        fixture
            .root()
            .join("third_party/variant-lib-1.0.0/BUILD.gn"),
    )
    .unwrap();
    assert_eq!(generated.matches("cargo_crate(").count(), 2);
    for context in ["target", "host"] {
        let label = obsolete[format!("{context}_label")].as_str().unwrap();
        let name = label.split_once(':').unwrap().1;
        assert!(!generated.contains(name));
    }
    assert_eq!(fixture.index()["crates"].as_array().unwrap().len(), 1);
    fixture.native_build();
    assert_success(&fixture.sync(&["--check"]));
}
