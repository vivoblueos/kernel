# GNRT Sync Configuration Reference

This reference covers the current `external/gnrt` implementation, not the
Chromium commands or a sibling checkout. Read `main.rs`, `lib/config.rs`,
`lib/collect.rs`, `lib/resolve.rs`, and `lib/generate.rs` under `external/gnrt`
if the implementation changes.

## CLI

Run from the project root containing `.gn`.

| Option | Default | Behavior |
| --- | --- | --- |
| `gnrt sync` | Full registered catalog | Collect declarations, resolve and vendor packages, apply patches, and publish GN rules and state. Reuse valid existing results. |
| `--all` | Not set | Explicit full-catalog intent; currently plain `sync` also collects the full catalog. |
| `--check` | Not set | Validate saved inputs, tools, environment, binary, and artifacts without downloading or generating dependencies. |
| `-o`, `--out OUT` | `out/gnrt-sync` | Directory for intermediate collection, resolution, and staging data, relative to the project root. |
| `--args [ARGS...]` | Empty | Pass GN argument assignments to collection. Conditions in the catalog remain symbolic. |
| `-h`, `--help` | Not set | Display the installed CLI's supported options. |

```sh
gnrt sync --all --out out/gnrt-custom \
  --args 'board="seeed_xiao_esp32c3"' 'build_type="release"'
gnrt sync --all --check
```

The current CLI hides its internal target-selection field. Do not use
`gnrt sync --target`. `--args` does not turn full sync into a board-only sync.

## Files and Path Bases

| Purpose | Current path |
| --- | --- |
| Configuration | `external/gnrt_config.toml` |
| Declaration files | `external/rust/BUILD.gn` |
| Canonical application-dependency lockfile | `external/rust/Cargo.lock` |
| GNRT's own build dependencies | `external/gnrt/Cargo.lock` |
| Versioned Cargo sources and generated GN files | `external/vendor/<package>-<version>/` |
| Declaration proxy index | `external/vendor/gnrt_crate_index.json` |
| Synchronization record | `external/vendor/gnrt_sync_state.json` |
| Synchronization lock | `external/vendor/.gnrt.lock` |
| Interrupted-publication journal | `external/vendor/.gnrt-sync-in-progress.json` |
| Intermediate data | `out/gnrt-sync/` unless `--out` changes it |

Sync uses Cargo's `--versioned-dirs` layout. Do not substitute the epoch-based
paths used by legacy helper methods. Generated compilation instances can share
one source directory while having different GN target names.

`[collect]`, `[fingerprint].files`, and `[resolve]` file paths are project-root
relative. `[gn]` template paths are relative to the configuration file. Patch
references are GN-root-relative `//` paths. Relative license and extra-input
paths in legacy fields follow their crate-oriented consumers, not the project
root; they are not active sync source-layout controls.

## `cargo_spec` Fields

The template is `build/templates/cargo.gni`; it is allowed under
`//external/rust` and its descendants. Register each declaration file in
`collect.declaration_files`.

| Field | Default or requirement | Meaning |
| --- | --- | --- |
| Target name | Required GN template argument | Stable proxy name used by consumers, independent of the package name. |
| `package` | Required | Cargo package name. |
| `version` | Required | Cargo version requirement. Use `=1.2.3` for an exact version, not `==1.2.3`. |
| `default_features` | `true` | Enable Cargo's default feature set. |
| `features` | `[]` | Feature strings and conditional scopes. Cargo unions requests; generated GN restores their conditions. |
| `rustflags` | `[]` | Ordered rustc arguments, optionally conditional. Conflicting requests for a shared instance require isolation. |
| `isolation` | `"none"` | `none` shares root and dependencies; `root` separates only the root; `closure` separates the root and its dependency closure. |
| `git` | Empty | Git source URL instead of crates.io. |
| `rev` | Empty | Git revision; prefer an immutable commit for reproducibility. |
| `branch` | Empty | Git branch selector. |
| `tag` | Empty | Git tag selector. |
| `patches` | `[]` | Ordered patch files applied to matching vendored versions. |

Supply at most one of `rev`, `branch`, and `tag`, and only with `git`. Declarations
for the same normalized package/version/Git source/ref must agree on patches.
The shared vendor layout rejects different sources for one package name/version.

Only `features` and `rustflags` accept conditional scopes:

```gn
features = [
  "build-script",
  {
    condition = "board == \"esp32c6_devkitc_1\""
    values = [ "esp32c6" ]
  },
]
```

`condition` is a GN expression. A conditional removal's `when`, documented below,
is a Cargo target selector. They are different syntaxes.

## Top-Level TOML Sections

The parser rejects unknown fields. All sections are described below.

### `[collect]`

| Field | Default | Sync behavior |
| --- | --- | --- |
| `declaration_files` | `[]` | Registered project-root-relative GN declaration files forming the full catalog. Keep the existing files when adding another. |

### `[resolve]`

| Field | Default or requirement | Sync behavior |
| --- | --- | --- |
| `root` | Required when the section is present | Legacy Cargo root package name. Accepted by the shared schema, unused by sync's synthetic workspace. Preserve the existing value. |
| `cargo_lockfile` | Schema default empty; sync requires a nonempty relative path | Canonical lockfile seeded into the synthetic workspace and published with generated artifacts. |
| `toolchain_file` | Empty | Project-root-relative GN file exporting toolchain metadata; BlueKernel uses `build/toolchain/BUILD.gn`. |
| `remove_crates` | Required when the section is present | Remove dependency edges to these packages from the generated graph. Does not remove them from Cargo resolution or turn them into external providers. Use `[]` if none. |
| `remove_crates_when` | `[]` | Conditional removals, each with `package` and `when`. Conditions are retained for GN evaluation. |

### `[fingerprint]`

| Field | Default | Sync behavior |
| --- | --- | --- |
| `files` | `[]` | Additional project-root-relative files or directory trees that affect synchronization. |
| `environment` | `[]` | Record these environment variable values, including whether each is unset. |
| `tools` | `[]` | Additional executable names whose selected paths and contents are recorded. Cargo and GN are always included; the generator and declared Rust compilers are also tracked. |

BlueKernel currently adds `rustc` and `python3` to `tools` and records
`RUSTUP_TOOLCHAIN`, `RUSTC_BOOTSTRAP`, `RUSTFLAGS`, and `CARGO_HOME`.

### `[gn]`

| Field | Default or requirement | Sync behavior |
| --- | --- | --- |
| `build_file_template` | Required when the section is present | Handlebars template for generated crate rules; currently `../build/CARGO_BUILD.gn.hbs`. |
| `host_toolchain` | `"//build/toolchain:host"` | Fallback host label; collected host toolchain metadata takes precedence. |
| `readme_file_template` | Empty | Legacy README generation field; sync does not generate those READMEs. |
| `removed_cargo_template` | Empty | Legacy placeholder Cargo manifest template; unused by sync. |
| `removed_librs_template` | Empty | Legacy placeholder Rust library template; unused by sync. |

The legacy Rust `VetConfig` type is not a top-level field of `BuildConfig`.
Do not add a `[vet]` section to this sync configuration.

## Per-Crate and Global Settings

Use `[crate.<name>]` for a package, or a quoted epoch key such as
`[crate."heapless@v0_8"]`. Epoch examples are `v1`, `v0_8`, and `v0_0_4`.
Do not combine an unversioned key and versioned keys for the same package.
Epoch matching selects a compatibility family, not one exact patch version.

`[all-crates]` accepts the same schema. Current sync combines global and per-crate
`remove_deps`, `remove_deps_when`, and `bin_targets` as additive collections.
`edition`, `remove_build_rs`, `patches`, and `group` are read per crate; do not
assume all other global fields affect sync.

All fields are optional. Collections default to empty, booleans to `false`, and
optional scalar values to unset.

| Field | Type | Current sync behavior |
| --- | --- | --- |
| `remove_deps` | Array of package names | Remove outgoing dependency edges from this crate after Cargo feature resolution. The source must already work without them. |
| `remove_deps_when` | Array of `{ package, when }` | Remove outgoing edges only under matching Cargo target selectors. |
| `remove_build_rs` | Boolean | Omit the crate's build-script rule. Confirm the crate does not require its generated files, cfgs, or link flags. |
| `bin_targets` | Array of Cargo binary names | Select binary targets to generate in addition to the library. Examples, tests, and benches are not selected by this field. |
| `edition` | String | Override the edition used by generated GN compilation, for example `"2021"`. Does not make an older Cargo parse a newer manifest. |
| `patches` | Array of GN `//` paths | Apply patches even when the crate is only transitive. Unversioned keys affect matching vendored versions; epoch keys limit the family. |
| `group` | `"test"`, `"sandbox"`, or `"safe"` | Stored in resolved package metadata; default is `safe`. The current GN template does not enforce these groups. |
| `exclude_deps_in_gn` | Array of strings | Accepted legacy GN-generation setting; not consumed by the current sync generator. |
| `ban_features` | Array of strings | Accepted legacy setting; current sync does not enforce a feature ban from it. |
| `remove_vendored_files` | Array of paths | Accepted legacy setting; current sync does not delete source files based on it. |
| `extra_input_roots` | Array of paths | Accepted legacy setting; current sync relies on rustc dep-info rather than this source-expansion option. |
| `extra_build_script_input_roots` | Array of paths | Accepted legacy setting; current sync does not expand build-script inputs from it. |
| `extra_kv` | Table of arbitrary values | Legacy template data; not exposed by the current sync `Target` render structure. |
| `allow_first_party_usage` | Boolean | Accepted legacy visibility setting; not enforced by the current sync template. |
| `build_script_outputs` | Array of paths | Accepted legacy output list. Current sync generates a build-script marker automatically rather than using this list. |
| `security_critical` | Optional boolean | Legacy audit/metadata setting; sync does not perform the corresponding audit. |
| `shipped` | Optional boolean | Legacy product metadata setting; not consumed by the current sync renderer. |
| `license` | Optional string | Legacy license metadata override; sync does not generate a license report from it. |
| `license_files` | Array of strings | Legacy license-file metadata; preserve existing entries, but sync does not validate or generate license READMEs from them. |
| `native_libs_roots` | Array of paths | Legacy `.lib` discovery option; not consumed by current sync generation. |
| `no_license_file_tracked_in_crbug_369075726` | Boolean | Legacy license exception; no current sync license-validation behavior. |

For example, a source adaptation can remove a build probe and its generated edge:

```toml
[crate.num-traits]
remove_deps = ["autocfg"]
```

Conditional removal example:

```toml
[[crate.example.remove_deps_when]]
package = "windows-sys"
when = 'cfg(not(target_os = "windows"))'
```

Multiple matching removal rules are combined with OR. These rules remove graph
edges; they do not subtract Cargo features or rewrite source code.

## Complete Baseline Configuration

This example includes the active configuration sections without changing the
project's existing crate-specific settings:

```toml
[collect]
declaration_files = ["external/rust/BUILD.gn"]

[resolve]
root = "bluekernel_crates_io"
cargo_lockfile = "external/rust/Cargo.lock"
toolchain_file = "build/toolchain/BUILD.gn"
remove_crates = []
remove_crates_when = []

[fingerprint]
files = []
environment = ["RUSTUP_TOOLCHAIN", "RUSTC_BOOTSTRAP", "RUSTFLAGS", "CARGO_HOME"]
tools = ["rustc", "python3"]

[gn]
build_file_template = "../build/CARGO_BUILD.gn.hbs"
host_toolchain = "//build/toolchain:host"
```

Merge required changes into the existing configuration; do not replace the
project's removal rules or patch registrations with this baseline example.

## Environment and Toolchain Integration

| Setting | Scope |
| --- | --- |
| `GNRT_CARGO_BIN` | Cargo executable used by sync resolution and tool validation. Does not choose the Cargo used to install GNRT. |
| `GNRT_GN_BIN` | GN executable used for declaration collection and fingerprinting. |
| `GNRT_RUSTC_BIN` | Override for the tool named `rustc` when fingerprinting; does not replace GN's declared compiler commands. |
| `GNRT_THIRD_PARTY_DIR` | Override the vendored/generated directory; default `external/vendor`. BlueKernel's GN index/state paths also need to agree. |
| `GNRT_THIRD_PARTY_CARGO_ROOT` | Legacy Cargo-root path override; default `external`. Sync's lockfile and vendoring follow their own explicit paths. |
| `GNRT_THIRD_PARTY_CONFIG_FILE` | Override the config file path; default `external/gnrt_config.toml`. |
| `GNRT_BIN` | Project/CI convention for selecting an executable. It is not a GNRT CLI option and does not replace typing the intended executable when invoking sync. |
| `RUSTUP_TOOLCHAIN`, `PATH`, Cargo/Rust flags | Select the actual tools and compilation settings; preserve configured fingerprint values across sync and builds. |
| `CARGO_HOME`, Cargo proxy/source settings | Cargo cache and download configuration. See troubleshooting for mirrors and proxies. |
| `RUST_LOG` | GNRT's env_logger filtering; use focused logging if diagnostics require it. |

`gnrt_mode = "collect"` is an internal GN collection mode. Ordinary builds use
`gnrt_mode = "build"`; leaving collect mode enabled skips normal compilation
behavior and is not a repair for missing dependencies.

`build/toolchain/BUILD.gn` exports host and target metadata through the
`gnrt_declarations` key. Its toolchain records contain `origin`, `label`, `role`,
`cc`, `cxx`, `ar`, `rustc`, `llvm_target`, and `target_triple`, plus the declaration
`type`. Keep the metadata consistent with GN's compiler context. Project-specific
Cargo cfg/triple rendering is controlled by the `gn_condition` bindings in
`build/CARGO_BUILD.gn.hbs`.

All four bindings are required nonempty GN expressions:

| Helper argument | BlueKernel binding | Meaning |
| --- | --- | --- |
| `target_triple` | `build_ctx.toolchain_target_triple` | Triple for Cargo target-context conditions. |
| `target_cfgs` | `build_ctx.toolchain_cfgs` | Compiler cfg values for Cargo target-context conditions. |
| `host_triple` | `host_build_ctx.toolchain_target_triple` | Triple for Cargo host-context conditions. |
| `host_cfgs` | `host_build_ctx.toolchain_cfgs` | Compiler cfg values for Cargo host-context conditions. |

These are template bindings, not extra TOML settings. Preserve the context when
changing compiler metadata or rendering conditions.

The current schema has no dependency-provider override, `dependency_overrides`,
or local Cargo source-replacement field for routing a package to `//libc`.
Do not turn a recorded proposal into configuration for an unmodified binary.
