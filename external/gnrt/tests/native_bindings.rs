// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn tool(name: &str) -> PathBuf {
    std::env::split_paths(&std::env::var_os("PATH").unwrap())
        .map(|path| path.join(name))
        .find(|path| path.is_file())
        .unwrap()
}

fn find_tool(name: &str) -> Option<PathBuf> {
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|path| path.join(name))
        .find(|path| path.is_file())
}

/// Identifies missing native binding files or host tools.
///
/// The fixture uses the checkout's native Cargo bindings and requires
/// `rustup`, `gn`, `ninja`, and `python3` on `PATH`.
fn missing_prerequisite() -> Option<String> {
    let build = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../build");
    for relative in [
        "templates/rust.gni",
        "templates/cargo_crate.gni",
        "scripts/resolve_cargo_aliases.py",
        "scripts/run_build_script.py",
        "scripts/action_helpers.py",
    ] {
        if !build.join(relative).is_file() {
            return Some(format!(
                "missing native binding file {}",
                build.join(relative).display()
            ));
        }
    }
    for name in ["rustup", "ninja", "python3"] {
        if find_tool(name).is_none() {
            return Some(format!("missing executable: {name}"));
        }
    }
    let rustup = tool("rustup");
    let lookup = match Command::new(&rustup)
        .args(["which", "--toolchain", "stable", "rustc"])
        .output()
    {
        Ok(output) => output,
        Err(error) => {
            return Some(format!(
                "could not query the stable Rust toolchain: {error}"
            ))
        }
    };
    if !lookup.status.success() {
        return Some("no stable toolchain installed via rustup".to_owned());
    }
    let Some(gn) = std::env::var_os("GNRT_GN_BIN")
        .map(PathBuf::from)
        .or_else(|| find_tool("gn"))
    else {
        return Some("missing executable: gn".to_owned());
    };
    if !gn.is_file() {
        return Some(format!("gn executable missing at {}", gn.display()));
    }
    None
}

fn write(root: &Path, path: &str, source: &str) {
    let path = root.join(path);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, source).unwrap();
}

#[test]
fn native_bindings_preserve_aliases_domains_and_build_script_outputs() {
    if let Some(reason) = missing_prerequisite() {
        panic!("native binding prerequisites are unavailable: {reason}");
    }
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let output = Command::new(tool("rustup"))
        .args(["which", "--toolchain", "stable", "rustc"])
        .output()
        .unwrap();
    assert_success(&output);
    let rustc = String::from_utf8(output.stdout).unwrap().trim().to_owned();
    let output = Command::new(&rustc).arg("-vV").output().unwrap();
    assert_success(&output);
    let version = String::from_utf8(output.stdout).unwrap();
    let host = version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .unwrap();
    let build = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../build");
    for relative in [
        "templates/rust.gni",
        "templates/cargo_crate.gni",
        "scripts/resolve_cargo_aliases.py",
        "scripts/run_build_script.py",
        "scripts/action_helpers.py",
    ] {
        write(
            root,
            &format!("build/{relative}"),
            &fs::read_to_string(build.join(relative)).unwrap(),
        );
    }
    write(
        root,
        ".gn",
        &r###"buildconfig = "//build/BUILDCONFIG.gn"
script_executable = "python3"
"###
        .replace("@RUSTC@", &rustc)
        .replace("@HOST@", host),
    );
    write(
        root,
        "build/BUILDCONFIG.gn",
        &r###"set_default_toolchain("//build/toolchain:host")
gnrt_mode = "build"
build_ctx = {
 toolchain_cfgs = [ "unix" ]
 toolchain_target_triple = "@HOST@"
 toolchain_rustc = "@RUSTC@"
 toolchain_cc = "clang -DGN_TARGET_NATIVE"
 toolchain_cxx = "clang++ -DGN_TARGET_NATIVE"
 toolchain_ar = "llvm-ar"
 toolchain_arflags = [ "--format=gnu" ]
 build_config_cflags = []
 build_config_cflags_c = [ "-DGN_TARGET_CFLAGS" ]
 build_config_cflags_cc = [ "-DGN_TARGET_CXXFLAGS" ]
 build_config_rustflags = [ "-Copt-level=0" ]
 build_config_rust_profile = "debug"
}
host_build_ctx = build_ctx
host_build_ctx.toolchain_cc = "clang -DGN_HOST_NATIVE"
host_build_ctx.toolchain_cxx = "clang++ -DGN_HOST_NATIVE"
host_build_ctx.build_config_cflags_c = []
host_build_ctx.build_config_cflags_c = [ "-DGN_HOST_CFLAGS" ]
host_build_ctx.build_config_cflags_cc = []
host_build_ctx.build_config_cflags_cc = [ "-DGN_HOST_CXXFLAGS" ]
"###
        .replace("@RUSTC@", &rustc)
        .replace("@HOST@", host),
    );
    write(root, "build/toolchain/BUILD.gn", &r###"toolchain("host") {
 tool("stamp") { command = "touch {{output}}" }
 tool("action") {}
 tool("rust_rlib") {
 command = "env {{rustenv}} @RUSTC@ --crate-name {{crate_name}} {{source}} --crate-type=rlib {{externs}} {{rustdeps}} {{rustflags}} -o {{output}}"
 outputs = [ "{{target_out_dir}}/lib{{target_output_name}}.rlib" ]
 }
 tool("rust_macro") {
 command = "env {{rustenv}} @RUSTC@ --crate-name {{crate_name}} {{source}} --crate-type=proc-macro {{externs}} {{rustdeps}} {{rustflags}} -o {{output}}"
 outputs = [ "{{target_out_dir}}/lib{{target_output_name}}.@DYLIB@" ]
 }
 tool("rust_bin") {
 command = "env {{rustenv}} @RUSTC@ --crate-name {{crate_name}} {{source}} --crate-type=bin {{externs}} {{rustdeps}} {{rustflags}} -o {{output}}"
 outputs = [ "{{root_out_dir}}/bin/{{target_output_name}}" ]
 }
}
"###.replace("@RUSTC@", &rustc).replace("@HOST@", host).replace("@DYLIB@", std::env::consts::DLL_EXTENSION));
    write(root, "build/config/gnrt_sync.gni", &r###"gnrt_crate_index = {
 crates = [
 { proxy = "//catalog:a" target_label = "//library:a" host_label = "//library:h" crate_type = "rlib" },
 { proxy = "//catalog:b" target_label = "//library:b" host_label = "//library:h" crate_type = "rlib" },
 { proxy = "//catalog:exported" target_label = "//library:exported" host_label = "//library:exported_host" crate_type = "rlib" },
 { proxy = "//catalog:export_macro" host_label = "//:export_macro" crate_type = "proc-macro" },
 ]
}
"###.replace("@RUSTC@", &rustc).replace("@HOST@", host));
    write(
        root,
        "library/BUILD.gn",
        &r###"import("//build/templates/cargo_crate.gni")
foreach(_variant, [ "a", "b", "h" ]) {
 cargo_crate(_variant) {
  crate_name = "library"
  context = "target"
  if (_variant == "h") { context = "host" }
  sources = [ "lib.rs" ]
  features = [ _variant ]
  if (_variant == "h") {
    deps = [ ":helper(//build/toolchain:host)" ]
  }
  rustc_metadata = _variant
  version = "1.0.0"
  build_root = "build.rs"
  build_sources = [ "build.rs" ]
  build_script_features = features
  build_deps = [ ":helper(//build/toolchain:host)" ]
  build_script_aliased_deps = { build_helper = ":helper(//build/toolchain:host)" }
  build_script_rustenv = [ "CFLAGS=unexpected-explicit-flags", "CC_FORCE_DISABLE=1" ]
  if (_variant == "a") { build_script_rustenv += [ "CARGO_FEATURE_A=1" ] }
  if (_variant == "b") { build_script_rustenv += [ "CARGO_FEATURE_B=1" ] }
  if (_variant == "h") { build_script_rustenv += [ "CARGO_FEATURE_H=1" ] }
  build_script_outputs = [ "library.build_script_outputs.stamp" ]
 }
}
"###
        .replace("@RUSTC@", &rustc)
        .replace("@HOST@", host),
    );
    write(root, "library/build.rs", &r###"fn main() {
 assert_eq!(build_helper::value(), 40);
 let native_context = if std::env::var_os("CARGO_FEATURE_H").is_some() { "HOST" } else { "TARGET" };
 let target = std::env::var("TARGET").unwrap();
 for (name, executable) in [("CC", "clang"), ("CXX", "clang++"), ("AR", "llvm-ar")] {
  let expected = if name == "AR" { executable.to_owned() } else { format!("{executable} -DGN_{native_context}_NATIVE") };
  for key in [name.to_owned(), format!("TARGET_{name}"), format!("{name}_{target}"), format!("{name}_{}", target.replace(['-', '.'], "_"))] {
   assert_eq!(std::env::var(&key).unwrap(), expected, "{key}");
  }
 }
 assert!(std::env::var_os("CC_KNOWN_WRAPPER_CUSTOM").is_none());
 assert!(std::env::var_os("CC_FORCE_DISABLE").is_none());
 assert_eq!(std::env::var("CC_SHELL_ESCAPED_FLAGS").unwrap(), "1");
 for name in ["CFLAGS", "CXXFLAGS", "ARFLAGS"] {
  let flags = std::env::var(format!("{name}_{target}")).unwrap();
  let expected = if name == "ARFLAGS" { "--format=gnu".to_owned() } else { format!("-DGN_{native_context}_{name}") };
  assert_eq!(flags.matches(&expected).count(), 1);
  for key in [name.to_owned(), format!("HOST_{name}"), format!("TARGET_{name}"), format!("{name}_{}", target.replace(['-', '.'], "_"))] {
   assert!(std::env::var_os(key).is_none());
  }
 }
 let value = if std::env::var_os("CARGO_FEATURE_A").is_some() { 1 } else if std::env::var_os("CARGO_FEATURE_B").is_some() { 2 } else { 3 };
 let out = std::env::var("OUT_DIR").unwrap();
 std::fs::write(std::path::Path::new(&out).join("native_flags.txt"), std::env::var(format!("CFLAGS_{target}")).unwrap()).unwrap();
 std::fs::write(std::path::Path::new(&out).join("value.rs"), format!("pub fn value() -> u8 {{ {value} }}")).unwrap();
}
"###.replace("@RUSTC@", &rustc).replace("@HOST@", host));
    write(
        root,
        "library/lib.rs",
        &r###"include!(concat!(env!("OUT_DIR"), "/value.rs"));
#[cfg(feature = "h")]
pub fn helper_value() -> u8 { helper::value() }
"###
        .replace("@RUSTC@", &rustc)
        .replace("@HOST@", host),
    );
    write(
        root,
        "BUILD.gn",
        &r###"import("//build/templates/rust.gni")
build_rust("app") {
 crate_type = "bin"
 sources = [ "main.rs" ]
 deps = [ "//catalog:a", "//catalog:b(${default_toolchain})", "//catalog:exported" ]
 proc_macro_deps = [ "//catalog:export_macro" ]
 aliased_deps = { a = "//catalog:a" b = "//catalog:b(${default_toolchain})" }
}
build_rust("host_consumer") {
 crate_type = "bin"
 sources = [ "host.rs" ]
 build_deps = [ "//catalog:a" ]
 aliased_deps = { h = "//catalog:a" }
}
build_rust("export_macro") {
 crate_type = "proc-macro"
 sources = [ "macro.rs" ]
 deps = [ "//catalog:a" ]
 aliased_deps = { h = "//catalog:a" }
 public_deps = [ "//catalog:exported(${default_toolchain})" ]
}
_generated_include = "$root_gen_dir/fixture.rs"
action("generate_include") {
 script = "generate.py"
 outputs = [ _generated_include ]
 args = [ rebase_path(_generated_include) ]
}
build_rust("action_consumer") {
 crate_type = "bin"
 sources = [ "action.rs" ]
 build_deps = [ ":generate_include" ]
 inputs = [ _generated_include ]
 rustenv = [ "GENERATED_INCLUDE=" + rebase_path(_generated_include) ]
}
group("default") { deps = [ ":app", ":host_consumer", ":action_consumer" ] }
"###
        .replace("@RUSTC@", &rustc)
        .replace("@HOST@", host),
    );
    write(
        root,
        "main.rs",
        &r###"fn main() { assert_eq!(a::value(), 1); assert_eq!(b::value(), 2); assert_eq!(export_macro::value!(), 9); }"###
            .replace("@RUSTC@", &rustc)
            .replace("@HOST@", host),
    );
    write(
        root,
        "host.rs",
        &r###"fn main() { assert_eq!(h::value(), 3); assert_eq!(h::helper_value(), 40); }"###
            .replace("@RUSTC@", &rustc)
            .replace("@HOST@", host),
    );
    write(root, "generate.py", "import pathlib, sys\npath = pathlib.Path(sys.argv[1])\npath.parent.mkdir(parents=True, exist_ok=True)\npath.write_text('pub const VALUE: u8 = 77;')\n");
    write(
        root,
        "action.rs",
        "include!(env!(\"GENERATED_INCLUDE\")); fn main() { assert_eq!(VALUE, 77); }",
    );
    let library_build = root.join("library/BUILD.gn");
    let source = fs::read_to_string(&library_build).unwrap();
    fs::write(
        library_build,
        source
            + r#"
cargo_crate("exported") {
  sources = [ "exported.rs" ]
  context = "target"
  rustc_metadata = "exported_target"
}
cargo_crate("exported_host") {
  crate_name = "exported"
  sources = [ "exported.rs" ]
  context = "host"
  rustc_metadata = "exported_host"
}
cargo_crate("helper") {
  sources = [ "helper.rs" ]
  context = "host"
  rustc_metadata = "build_helper"
}
"#,
    )
    .unwrap();
    write(root, "library/helper.rs", "pub fn value() -> u8 { 40 }");
    write(root, "library/exported.rs", "pub fn value() -> u8 { 9 }");
    write(
        root,
        "macro.rs",
        r#"extern crate proc_macro; #[proc_macro] pub fn value(_: proc_macro::TokenStream) -> proc_macro::TokenStream { assert_eq!(h::value(), 3); "exported::value()".parse().unwrap() }"#,
    );
    let gn = std::env::var_os("GNRT_GN_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|| tool("gn"));
    let command = |arguments: &[&str]| {
        Command::new(&gn)
            .current_dir(root)
            .args(arguments)
            .output()
            .unwrap()
    };
    assert_success(&command(&["gen", "out"]));
    assert_success(
        &Command::new(tool("ninja"))
            .current_dir(root)
            .args(["-C", "out"])
            .envs([
                ("CC", "unexpected-compiler"),
                ("CXX", "unexpected-compiler"),
                ("AR", "unexpected-archiver"),
                ("HOST_CC", "unexpected-compiler"),
                ("TARGET_CXX", "unexpected-compiler"),
                ("CC_KNOWN_WRAPPER_CUSTOM", "clang"),
                ("CFLAGS", "unexpected-inherited-flags"),
                ("HOST_CXXFLAGS", "unexpected-inherited-flags"),
                ("TARGET_ARFLAGS", "unexpected-inherited-flags"),
                ("CC_FORCE_DISABLE", "1"),
            ])
            .env(format!("CC_{host}"), "unexpected-compiler")
            .env(
                format!("AR_{}", host.replace(['-', '.'], "_")),
                "unexpected-archiver",
            )
            .env(format!("CFLAGS_{host}"), "unexpected-inherited-flags")
            .env(
                format!("CXXFLAGS_{}", host.replace(['-', '.'], "_")),
                "unexpected-inherited-flags",
            )
            .output()
            .unwrap(),
    );
    for binary in ["app", "host_consumer", "action_consumer"] {
        assert_success(
            &Command::new(root.join("out/bin").join(binary))
                .output()
                .unwrap(),
        );
    }
    for (target, value) in [("a", 1), ("b", 2), ("h", 3)] {
        let output_dir = root.join(format!("out/obj/library/{target}-1.0.0_out"));
        assert!(fs::read_to_string(output_dir.join("value.rs"))
            .unwrap()
            .contains(&format!("{{ {value} }}")));
        for suffix in [
            "cargo_flags.rsp",
            "build_script_rustc_env.env",
            "library.build_script_outputs.stamp",
        ] {
            assert!(root
                .join(format!("out/obj/library/{target}.{suffix}"))
                .is_file());
        }
    }
    let aliases: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(root.join("out/gen/app.cargo_aliases.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(
        aliases["resolved_deps"][0],
        "//library:a(//build/toolchain:host)"
    );
    assert_eq!(
        aliases["resolved_deps"][1],
        "//library:b(//build/toolchain:host)"
    );
    let native_context_path = root.join("out/gen/library/a.native_context.json");
    let native_context: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&native_context_path).unwrap()).unwrap();
    assert_eq!(native_context["version"], 1);
    assert_eq!(native_context["target"]["cflags"][0], "-DGN_TARGET_CFLAGS");
    let config_path = root.join("build/BUILDCONFIG.gn");
    fs::write(
        &config_path,
        fs::read_to_string(&config_path).unwrap().replace(
            "build_config_cflags_c = [ \"-DGN_TARGET_CFLAGS\" ]",
            "build_config_cflags_c = [ \"-DGN_TARGET_CFLAGS\", \"-DGN_CHANGED\" ]",
        ),
    )
    .unwrap();
    assert_success(
        &Command::new(tool("ninja"))
            .current_dir(root)
            .args(["-C", "out"])
            .output()
            .unwrap(),
    );
    assert!(
        fs::read_to_string(root.join("out/obj/library/a-1.0.0_out/native_flags.txt"))
            .unwrap()
            .contains("-DGN_CHANGED")
    );
    fs::write(
        &config_path,
        fs::read_to_string(&config_path).unwrap().replace(
            "set_default_toolchain(\"//build/toolchain:host\")",
            "set_default_toolchain(\"//build/toolchain:target\")",
        ),
    )
    .unwrap();
    let toolchain_path = root.join("build/toolchain/BUILD.gn");
    let host_toolchain = fs::read_to_string(&toolchain_path).unwrap();
    let target_toolchain = host_toolchain.replace("toolchain(\"host\")", "toolchain(\"target\")");
    fs::write(toolchain_path, host_toolchain + &target_toolchain).unwrap();
    assert_success(&command(&["gen", "out_target"]));
    assert_success(
        &Command::new(tool("ninja"))
            .current_dir(root)
            .args(["-C", "out_target"])
            .output()
            .unwrap(),
    );
    for binary in ["app", "host_consumer", "action_consumer"] {
        assert_success(
            &Command::new(root.join("out_target/bin").join(binary))
                .output()
                .unwrap(),
        );
    }
    assert!(root.join("out_target/gen/fixture.rs").is_file());
    let path = root.join("build/config/gnrt_sync.gni");
    fs::write(
        &path,
        fs::read_to_string(&path)
            .unwrap()
            .replace("host_label = \"//library:h\"", ""),
    )
    .unwrap();
    let output = command(&["gen", "out"]);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stdout).contains("No host recipe for"));
}
