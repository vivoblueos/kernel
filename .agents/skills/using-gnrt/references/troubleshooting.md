# Troubleshooting GNRT Sync

## Identify the First Failing Stage

Check the intended checkout and tools first:

```sh
git rev-parse --show-toplevel
git status --short
command -v gnrt
gnrt sync --help
rustc -vV
cargo -V
```

Use the first concrete diagnostic to choose the next step. Keep the original
failure log and use a targeted retry when it tests a specific correction.

| Symptom | Diagnosis and action |
| --- | --- |
| Current directory has no `.gn` | Run from the BlueKernel root, not `external/gnrt` or a vendor directory. |
| A `third_party/.gnrt.lock` appears | Check `GNRT_THIRD_PARTY_DIR` and the selected executable. The default is `external/vendor`; the lock follows the configured vendor directory and can remain after a failed sync. |
| Collection cannot find a generated crate target | Check catalog registration, `cargo.gni` imports, metadata-only collect behavior, and consumers using declaration proxies. |
| Missing proxy or host/target recipe | Check the declaration label, registered files, dependency role, and index entry. Re-sync after correcting inputs. |
| Unknown config field or invalid selector | Consult the local schema. GN `condition` expressions and Cargo `when` selectors are different formats. Proposed dependency overrides are not implemented. |
| Cargo cannot parse an edition | Check the selected Cargo version. A generated `edition` override cannot change manifest parsing. |
| Version requirement cannot be resolved | Inspect exact pins, registry completeness, Git source/ref, mirror configuration, and the canonical lockfile. |
| Conflicting shared rustflags or features | Trace declarations and Cargo feature propagation. Use root or closure isolation where separate compilation is intended. |
| Multiple sources collide | The current vendor layout cannot host two different sources with the same package name/version. Resolve the source identity conflict explicitly. |
| Patch neither applies nor matches | Compare against the exact pristine vendored version, normalized manifests, patch order, and partial local edits. |
| Sync input/artifact changed | Inspect the named path and compare configuration, declarations, patches, templates, lockfile, generated sources, and executable selection. Re-sync after the intended change. |
| Tool/environment changed | Use the same Cargo/GN/Rust selection and configured environment during sync and builds, or re-sync under the intended environment. |
| Unfinished publication marker | Stop consumers and run `gnrt sync --all` to recover. Do not delete the journal to bypass recovery. |
| Sync passes, compiler or linker fails | Diagnose the Rust/C compiler, build script, native library order, missing symbols, cfgs, or ABI. Sync success is not build success. |
| Clang reports no compatible RISC-V target | Check `command -v clang` and `clang --print-targets`. Select a Clang build supporting RISC-V through the build environment; a different Clang earlier on `PATH` can lack that backend. |

## Installation and Updates

Install from the checkout with:

```sh
cargo install --path external/gnrt --locked --bin gnrt
```

`--path` rebuilds and installs local sources, so routine local updates do not need
`--force`. `--force` permits overwriting installed packages or binaries; it does
not mean offline. `--locked` preserves the GNRT package's dependency lockfile;
`--offline` forbids network access and requires the necessary cached dependencies.

After a GNRT source change, rerun the installation command and sync explicitly.

## Proxy and Company Mirror Configuration

Cargo performs installation downloads. A subprocess inherits exported environment
settings unless its caller replaces them; Python proxy detection is not involved
in the direct installation command. An OS desktop proxy setting alone does not
establish the command-line tool's effective proxy.

For example, replace the port with the actual proxy port:

```sh
export CARGO_HTTP_PROXY=http://127.0.0.1:7890
cargo install --path external/gnrt --locked --bin gnrt
```

For a crates.io-compatible company mirror, merge a source replacement into the
user's Cargo configuration, using the real index address:

```toml
[source.crates-io]
replace-with = "company"

[source.company]
registry = "sparse+https://cargo.company.example/index/"
```

A mirror must provide the pinned package versions and matching contents/checksums.
`--locked` does not prevent mirror replacement. A private registry containing
different packages or modified contents is a different source-identity problem.
Do not drop lockfile validation as a generic mirror fix.

Check installation and vendoring separately. The current GNRT vendor command is
`cargo vendor --locked --no-delete --versioned-dirs`; it does not add
`--respect-source-config`. Cargo vendor normally ignores source replacement unless
that option is supplied. A mirror that works for installation therefore does not
prove that sync vendoring uses it. If that phase must respect a company mirror,
identify the missing vendoring support and implement/test it within the requested
scope rather than inventing a nonexistent sync configuration flag.

## Existing Vendor Trees and Clean Reconstruction

Old generated directories can contain patched sources, placeholder manifests, or
checksum files incompatible with the current Cargo graph. Common symptoms include
a missing aliased dependency, `package` checksums set to null, or an offline
metadata command demanding lockfile changes.

Inspect the named crate's manifest, `.cargo-checksum.json`, and source differences
against both the pinned upstream package and the previous project version. Do
not disable checksums or rewrite the canonical lockfile to hide a mismatch.

Prefer validating in an isolated project checkout with no vendor directory, then
run sync and a real consumer build there. Back up intended local adaptations
before refreshing an existing source directory. Refresh only confirmed generated
or stale content. `--out` relocates intermediate files, not the live vendor tree.
Do not use broad `git clean`, resets, or recursive deletion as an automatic fix.

## Native Build and Architecture Failures

- Inspect `build.rs` stdout, generated cargo flag files, and the final compiler or
  linker command. Verify host/target context and propagated cfgs/link flags.
- A GNU linker error such as `archive has no index` requires checking the actual
  archive, its symbol index, and whether `inline-asm` makes its linkage unnecessary.
  Do not suppress arbitrary native link directives globally.
- A portable-atomic privilege error depends on the target's advertised atomic
  capabilities, selected features, CPU privilege mode, and interrupt implementation.
  A compile-time platform exception does not prove those safety requirements.
- Check custom BlueOS target triples against a crate's upstream target validation.
  Accepting a custom triple should still preserve chip-to-target checks.
- The build-script runner implements a subset of Cargo behavior. Inspect the
  current runner before relying on `DEP_*` metadata or complete `rerun-if-*`
  behavior; do not assume those features exist because a crate works under Cargo.

## Sync State and Validation Limits

The publication journal covers generated artifacts and recorded state, but
vendoring and patch application can change live sources before publication.
Recovery does not imply that every source file is rolled back.

The Python checker emits JSON and can exit successfully while reporting
`"valid": false`. Inspect the JSON, or use normal `gn gen`, which asserts validity.
Do not leave `gnrt_mode = "collect"` enabled for a normal build.

Report precisely whether validation covered clean source reconstruction, saved
state, GN generation, crate compilation, final linking, or runtime tests. Preserve
the existing license/compliance workflow; sync does not provide a complete license
README or unsafe-code audit pipeline.
