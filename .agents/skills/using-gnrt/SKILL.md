---
name: using-gnrt
description: Manage BlueKernel Rust dependencies with GNRT sync. Use when adding or updating crates, configuring resolution and generated GN rules, maintaining source patches, or diagnosing synchronization and dependency build failures.
---

# Using GNRT

Use the GNRT implementation in `external/gnrt` and the integration in `build/`.
Treat declarations, the canonical lockfile, configuration, and source patches as
the editable inputs. Generate vendored sources and GN rules with `gnrt sync`.

## Read the Relevant Reference

| Task | Reference |
| --- | --- |
| CLI options, every configuration field, defaults, path bases, and environment | [Configuration](references/configuration.md) |
| Add or update a crate, use macros, select board features, or isolate features | [Dependency workflows](references/dependencies.md) |
| Capture local adaptations, register patches, or validate patch application | [Source patches](references/patches.md) |
| Diagnose collection, Cargo, patch, state, compiler, or linker failures | [Troubleshooting](references/troubleshooting.md) |

Read only the references needed for the task. Verify behavior against the local
source when changing configuration: some accepted fields belong to legacy
commands and do not affect `sync`.

## Establish the Checkout and Tools

Run commands from the BlueKernel root containing `.gn`. Confirm the Git root,
branch, worktree changes, `command -v gnrt`, `gnrt sync --help`, and active Rust
toolchain before editing or synchronizing. The standalone GNRT repository and
other BlueKernel checkouts can contain different implementations.

Install or update the local executable directly with Cargo:

```sh
cargo install --path external/gnrt --locked --bin gnrt
```

Use the same executable and toolchain for synchronization and validation.
`--locked` permits configured registry mirrors; it does not mean offline.
After changing GNRT sources, reinstall it explicitly.

## Synchronize and Validate

```sh
gnrt sync --all
gnrt sync --all --check
```

Both plain `sync` and `sync --all` process the full registered catalog in the
current CLI. There is no public `--target` option. Keep declarations visible
outside board-specific `if` blocks and use conditional feature values instead.

After synchronization, generate the affected board and build an actual consumer:

```sh
gn gen out/qemu_mps3_an547.release.swi \
  --args='board="qemu_mps3_an547" build_type="release" direct_syscall_handler=false'
ninja -C out/qemu_mps3_an547.release.swi bin/ftp_client_example
```

Select validation for the actual change. `--check` does not compile or link.
A `cargo_spec` label is a proxy, so building that label alone may perform no
compilation. Build a generated crate target or a product that uses it.

## Preserve Project Boundaries

- Keep generated `external/vendor` files out of commits. Do not use manual edits
  there as the durable implementation of an adaptation.
- Keep project-maintained libraries such as `//libc`, `external/rust-fatfs`, and
  `external/rust-ftp` on their existing targets unless their migration is
  explicitly requested. Update their references to migrated vendor dependencies
  when necessary.
- Keep normal dependencies in `deps` and procedural macros in `proc_macro_deps`.
  Preserve build dependencies and host/target feature separation.
- Finish synchronization before starting consumers; avoid syncing while a build
  is using the same vendor tree. Publication recovery does not roll back every
  source change performed by vendoring or patching.
- Diagnose the named failure before retrying. Preserve unrelated local edits and
  validate a patch or clean source reconstruction in an isolated directory.
- Do not bypass sync checks or delete transaction markers to make a build pass.

Report the editable files changed, checks actually run, and remaining failures.
Distinguish sync validation, compilation, linking, and runtime tests.
