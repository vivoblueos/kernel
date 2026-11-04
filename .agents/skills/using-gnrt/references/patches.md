# Maintaining Source Patches

## Choose the Scope

Use a declaration's `patches` when that declaration owns the package policy.
Use a per-crate entry in `external/gnrt_config.toml` for a transitive crate or
for a package shared by several declarations.

For example, the direct `num-traits` declaration contains:

```gn
patches = [
  "//external/rust/patches/num-traits-0.2.19/001-local-no-autocfg.patch",
]
```

A transitive manifest adaptation is configured as follows:

```toml
[crate.defmt-parser]
license_files = ["LICENSE-APACHE", "LICENSE-MIT"]
patches = ["//external/rust/patches/defmt-parser-1.0.0/001-disable-thiserror-default-features.patch"]
```

Preserve existing license metadata even though sync does not generate a license
report from it. Continue the project's applicable compliance checks.

Place patches under `external/rust/patches/<package>-<version>/`, in application
order, with names such as `001-disable-thiserror-default-features.patch`. Pin the
package version or Git revision first. Multiple declarations for the same source
identity must agree on patch policy; a shared source cannot have incompatible
per-consumer patches.

## Create the Patch from Pristine Source

Use the exact registry archive or pinned Git revision. For registry manifests,
Cargo's normalized `Cargo.toml` can differ from `Cargo.toml.orig` and the upstream
repository version. Patch the file that Cargo actually vendors.

Use a disposable Git repository to obtain `a/` and `b/` paths that work with
`git apply -p1`. For example, after unpacking pristine source into `patch_workdir`:

```sh
git -C "$patch_workdir" init
git -C "$patch_workdir" add -- Cargo.toml
```

Make the intended edit in that disposable source tree, then capture it:

```sh
git -C "$patch_workdir" diff --binary -- Cargo.toml > \
  "$project_root/external/rust/patches/defmt-parser-1.0.0/001-disable-thiserror-default-features.patch"
```

Here `project_root` is the BlueKernel checkout and `patch_workdir` is the
temporary source repository. These commands do not stage the real project.

Describe the change and its reason at the top of the patch file. For example,
the manifest change adds `default-features = false` to defmt-parser's thiserror
dependency. Keep the explanation in the patch, not duplicated at every reference.
Use the established header form:

```text
# Patch: Disable thiserror's default features in defmt-parser.
# Reason: Its default std feature is unavailable on embedded BlueOS targets.
```

Its manifest change is:

```diff
--- a/Cargo.toml
+++ b/Cargo.toml
@@ -42,2 +42,3 @@
 [dependencies.thiserror]
 version = "2"
+default-features = false
```

Leave existing source notices intact. Avoid formatting churn outside the intended
change. When editing a unified diff by hand, update hunk counts and check that it
still applies; a comment-only patch edit can invalidate those counts.

## Validate Application and Behavior

Against a separate pristine copy of the pinned source, initialize a disposable
repository so Git cannot interpret paths relative to a parent project:

```sh
git -C "$clean_crate" init
git -C "$clean_crate" apply --check -p1 "$patch_file"
git -C "$clean_crate" apply -p1 "$patch_file"
git -C "$clean_crate" apply --check --reverse -p1 "$patch_file"
```

Use absolute `patch_file` paths when changing directories. Apply an ordered patch
series in order before checking the next patch. Check reverse applicability to
the corresponding state of the series.

GNRT applies declaration patches after vendoring, followed by configured
per-crate patches. A patch is accepted when it applies cleanly or its reverse
applies cleanly to the already-patched source. Otherwise sync fails; do not treat
a partially edited source tree as a valid upstream baseline.

After registration:

```sh
gnrt sync --all
gnrt sync --all --check
```

Then build a real affected target. A successful sync-state check establishes
neither clean patch application nor successful compilation/linking by itself.

## Dependency-Manifest Changes

Resolution starts before source patches are applied. Patching a manifest can
change the later offline metadata graph. Review the canonical lockfile and
dependency edges, not just whether `git apply` succeeded.

`remove_deps` only removes the generated dependency edge. It does not modify
source imports, remove a Cargo manifest requirement, or disable a transitive
feature. Use it only when the source adaptation already makes the dependency
unnecessary. Existing `num-traits` handling is an example: its patch removes the
autocfg probe, and configuration removes the unused GN edge.

## Preserve Existing Adaptations During Migration

Compare three versions: pristine upstream, the previous checked-in BlueKernel
source, and the newly patched source. A diff against upstream alone cannot reveal
a local modification that was accidentally omitted.

Classify changes explicitly when useful for review:

- Existing adaptations reproduced without functional changes.
- New fixes required by the integration or selected toolchain.
- Existing adaptations that also need additional changes.

Keep new changes narrow and explain them. A shared package name does not prove
ABI compatibility: root `libc` and vendor `libc` can contain different socket
constants and structure layouts. Do not replace one with the other merely to
remove a patch.
