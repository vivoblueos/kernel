# Josh Branch Tools

Import and export child branches for the `vivoblueos/kernel` center.
Requires Python 3, Git, `josh`, and `josh-filter`; verified with Josh
`r26.07.19`. Run each script with `--help` for parameter details.
Run Josh operations sequentially within a repository.

## Configure Remotes

From the center checkout, configure each child remote you need:

```bash
josh remote add fork-build \
    https://github.com/Natural-selection1/build.git ':prefix=build'
```

| `--repo`       | Center directory | Remote filter        |
| -------------- | ---------------- | -------------------- |
| `apps_shell`   | `shell`          | `:prefix=shell`      |
| `apps_example` | `example`        | `:prefix=example`    |
| `build`        | `build`          | `:prefix=build`      |
| `external`     | `external`       | `:prefix=external`   |
| `libc`         | `libs/libc`      | `:prefix=libs/libc`  |
| `librs`        | `libs/librs`     | `:prefix=libs/librs` |

Reuse an existing remote only if its filter matches. For an old-layout
remote, add a new name with the correct filter; `--repo` does not change it.
The usual libc baseline is `blueos-dev`, rather than `main`.
`book` is no longer synchronized; kernel history uses the projection below.

## Import a Child Branch

```bash
python3 tools/josh/merge-subtree-branches.py \
    --source-remote fork-build --source-branch miri/allocator \
    --repo build --target-base main --target-branch merge/miri/allocator
```

Commit or stash tracked changes and finish ongoing Git operations first.
The script creates the target from the baseline, or merges into an existing
target, then stays on that branch. It does not push. For another child,
run again with its remote and repo, using the current target branch as both
`--target-base` and `--target-branch`. Handle merge conflicts with Git's usual
`merge --continue` or `merge --abort` workflow.

## Export to a Child Branch

Preview the changes in `main..merge/miri/allocator`, replayed onto build's
`main`:

```bash
python3 tools/josh/push-subtree-branch.py \
    --source-base main --source-rev merge/miri/allocator \
    --target-remote fork-build --repo build \
    --target-branch miri/allocator --target-base main
```

- This is a dry run. Review the preview and add `--push` to publish.
- Add `--force` only when replacing history is intended. It permits a
  non-fast-forward update and has no `--force-with-lease` protection.
- The source baseline's subtree must match the child target baseline,
  except for `bluekernel-version` and `blueos-version`. Range export preserves
  these markers from the child baseline and flattens merges.
- Keep the same source baseline for later exports from this development
  branch; use its SHA if the baseline branch has moved.
- To export the entire reachable subtree history, including sync markers,
  omit **both** `--source-base` and `--target-base`.

Only committed content is exported. The current branch and working tree
stay in place; replay conflicts or file verification failures stop the push.

## Export Kernel History

Use this separate projection for internal kernel synchronization. It keeps
the original root and history through the fixed boundary below, then
projects `kernel/` to the root. Do not replace it with plain `:/kernel`:
that would lose the original layout before the directory move.

```bash
josh clone -b main https://github.com/vivoblueos/kernel.git \
    ':rev(<=2f94b1d75e5e44497d59617b08f07f834a990c8a:/,_:/kernel)' \
    kernel-only
cd kernel-only
# Subsequent updates use the same projection:
josh pull -r origin -R main
```

Push the projected checkout to an internal mirror through a separate,
ordinary Git remote, after checking the target branch and ancestry.
Keep Josh's `origin` pointing to the center. The commands above do not
publish to the internal mirror. The child-branch scripts do not handle
this export; do not use `:prefix=kernel` against the full center.
