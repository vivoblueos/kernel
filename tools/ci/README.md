# BlueKernel PR CI

The root `BlueKernel CI` workflow checks every pull request targeting `main`,
including drafts. Each job checks out the PR's merge result and uses the existing
`ghcr.io/vivoblueos/kernel:latest` toolchain image.

The workflow runs format and license checks, 40 board build profiles, two host
profiles, and the allocator's Miri Tree Borrows tests. Every ordinary profile
runs `gn gen`, `ninja default`, and `ninja check_all`. The final `BlueKernel CI` job
passes only when all jobs succeed and can be selected as a required PR check.

The scripts live outside the synchronized component directories. Existing
component workflows and repository synchronization remain independent.

## Run locally

From the repository root, with the CI toolchain on `PATH`:

```sh
python3 tools/ci/run_profile.py --board none --build-type debug --syscall-mode swi
python3 tools/ci/run_profile.py --board qemu_mps2_an385 --build-type release --syscall-mode dsc
python3 tools/ci/check_changes.py --base BASE_COMMIT --head MERGE_COMMIT
```

For changed-file checks, check out `MERGE_COMMIT` first. The script compares its
tree with `BASE_COMMIT`, checks existing changed GN/Python/Rust/YAML files, and
runs license-eye in each affected component using its existing configuration.
Moves and deletions also count when selecting affected license configurations.
Formatting excludes `external`; license checks cover `kernel`, `build`, `libs/librs`,
`example`, `shell`, and `tools/ci`.

To reproduce the Miri job:

```sh
gn gen out/qemu_mps2_an385.debug.miri --args='board="qemu_mps2_an385" build_type="debug" miri_path="/opt/sysroot/usr/local/bin/miri" miri_sysroot="/opt/sysroot/usr/local/lib/rustlib/x86_64-unknown-linux-gnu/miri-sysroot"'
ninja -C out/qemu_mps2_an385.debug.miri kernel/allocator:check_allocator_by_miri
```
