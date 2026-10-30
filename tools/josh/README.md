# Josh Branch Tools

Both scripts use `source` and `target` to name their inputs. `--repo` selects
a child repository and its directory in the central repository. Parameters
that select central commits accept branch names, tags, full or unique
abbreviated SHAs, and Git expressions such as `HEAD~1`. Branch parameters,
and `--target-base` in the push script, accept branch names only.

## Import and Merge a Child Branch

`merge-subtree-branches.py` reverse-maps a configured Josh child remote
branch onto the full central history, then merges it into the target
branch. Each invocation imports one source. Run it sequentially to import
multiple child repositories.

Requires Python 3, Git, `josh`, and `josh-filter`. The verified Josh version
is `r26.07.19`. Configure the remotes you need:

```bash
cd /home/hegui/vivoblueos/bluekernel
josh remote add fork-build \
    https://github.com/Natural-selection1/build.git ':prefix=build'
josh remote add fork-kernel \
    https://github.com/Natural-selection1/kernel.git ':prefix=kernel'
```

Skip remote configuration if the remotes already exist.
Import build from `main`:

```bash
python3 tools/josh/merge-subtree-branches.py \
    --source-remote fork-build \
    --source-branch miri/allocator \
    --repo build \
    --target-base main \
    --target-branch bluekernel/miri/allocator
```

| Parameter         | Purpose                                                  |
| ----------------- | -------------------------------------------------------- |
| `--source-remote` | Configured Josh remote, such as `fork-build`.            |
| `--source-branch` | Child branch to import, such as `miri/allocator`.        |
| `--repo`          | Child repository name; determines the central directory. |
| `--target-base`   | Central mapping baseline; defaults to `main`.            |
| `--target-branch` | Central branch to create or append a merge to.           |
| `--repo-root`     | Central checkout; defaults to the script's repository.   |

`--target-base` accepts a branch name, full or abbreviated SHA, or a Git
expression such as `HEAD~1`. If the target branch does not exist, it is
created from this baseline. An existing target branch receives a merge.

`--repo` supports `apps_shell`, `apps_example`, `book`, `build`, `external`,
`kernel`, `libc`, and `librs`. `apps_example` maps to `apps/example`, and
`apps_shell` maps to `apps/shell`. All other names map to a directory of the
same name. The Josh remote's prefix must match that directory.

## Merge Multiple Child Repositories Sequentially

After importing build above, use the current target branch as the baseline
to append kernel:

```bash
python3 tools/josh/merge-subtree-branches.py \
    --source-remote fork-kernel \
    --source-branch miri/allocator \
    --repo kernel \
    --target-base bluekernel/miri/allocator \
    --target-branch bluekernel/miri/allocator
```

`--target-base` may name the target branch itself. The script resolves the
starting commit before merging, so moving the branch during this invocation
does not change that baseline. You can also choose a new target branch to
preserve the first import's branch position.

For an existing target branch, the baseline must be its ancestor or the
branch tip itself. The script preserves existing commits without resetting
the target branch. The baseline should contain the full central history,
usually `main` or the result of the previous import. A Git expression only
selects a commit; its history must still be suitable for the operation.

The source is first mapped through separate refs using
`--reverse --check-roundtrip`, then merged into the target with
`git merge --no-ff`. Mapping refs live under `refs/import/<target-branch>/`.
They are regenerated on each invocation and are not development branches.

## Working Tree and Conflicts

The script switches to the target branch and merges in the current working
tree. On success, it stays on that branch. Commit your changes or save them
with `git stash` first. The script rejects uncommitted changes to tracked
files and ongoing Git operations such as merge or rebase. Git's overwrite
protection still applies to untracked files.

Resolve conflicts using the usual Git workflow:

```bash
git status
# Edit the conflicted files.
git add <resolved-files>
git merge --continue
```

After completing the merge, that source has been integrated. You can import
the next child repository. To retry the original command, use the same
baseline and source commit. The script prints `Round starting commit: <SHA>`.
If the baseline branch has moved, set `--target-base` to that SHA. Treat a
changed source as a new import round.

Use `git merge --abort` to abandon the current conflicted merge. Earlier
completed merges remain in place.

The script imports and merges without pushing to a remote. Each run
overwrites two helper refs and retains them for inspection after success
or failure. It creates no temporary branches, worktrees, or resume files.

Run Josh operations sequentially within a repository. The scripts do not
coordinate concurrent operations.

## Push Back to a Child Branch

`push-subtree-branch.py` uses `--source-base` (an existing central baseline)
and `--source-rev` (the final branch tip) to select an export range. The range
is Git's `SOURCE_BASE..SOURCE_REV`: it excludes the baseline and its
ancestors, and includes the tip and other merged commits outside that
baseline history. Linear and merge branches use the same selection model.
Each invocation filters one child directory and uses Josh to attempt a push
to the specified child branch.

Both central parameters accept branch names, SHAs, and Git expressions such
as `HEAD~1`. They are resolved to fixed SHAs at the start of the invocation.
Only committed content is processed. The central branch and working tree
stay in place.

For example, export the build changes in `main..merge/miri/allocator`, replay
them onto build's `main`, and update its `miri/allocator` branch:

```bash
python3 tools/josh/push-subtree-branch.py \
    --source-base main \
    --source-rev merge/miri/allocator \
    --target-remote fork-build \
    --repo build \
    --target-branch miri/allocator \
    --target-base main \
    --force
```

This is still a dry run. Add `--push` to perform the push. For a linear
branch, use `--source-rev bluekernel/miri/allocator`. You can also use a SHA or a
Git expression such as `HEAD`. `--source-base` must be an ancestor of
`--source-rev` or the same commit, and may be a merge commit. Equal endpoints
select an empty range. The central baseline is not chosen or recorded
automatically.

`--target-base` explicitly selects the child branch that receives the replay,
usually the PR's target branch. The selected subtree of the central
`--source-base` must contain the same files as the child's `--target-base`,
except for the automation-managed `bluekernel-version` and legacy
`blueos-version` files at the child repository root. Range mode filters out
changes to these files before replay, including commits that only change
them, and preserves their contents or absence from the child's `--target-base`.
Child repositories using the legacy filename do not need to migrate first.
Only then does the script rebase the filtered range onto the child baseline,
verify that all other final files are unchanged, and attempt the push. The two
baselines are independent and need not share a name. The `--target-base`
branch itself is not modified.

Range mode uses an automatically cleaned detached temporary worktree. It
creates no temporary branch and flattens filtered merges. Changes outside
the selected directory are filtered out. If replaying that directory causes
conflicts or changes the final files, the script returns an error without
pushing and cleans up the temporary worktree. Prepare the source branch so
that its changes in the selected directory can be replayed, then retry.
Rebase sets the committer date to the author date to keep repeated exports
stable with the same inputs and Git identity.

After further development on the merge branch, use the same baseline and
the latest branch tip to export each child directory. Each export includes
the imported business changes and later changes that affect that directory.

To push kernel from the same final central branch, change the remote and
repository:

```bash
python3 tools/josh/push-subtree-branch.py \
    --source-base main \
    --source-rev merge/miri/allocator \
    --target-remote fork-kernel \
    --repo kernel \
    --target-branch miri/allocator \
    --target-base main \
    --force
```

To filter the selected commit's entire reachable history, supply only
`--source-rev`, omitting both `--source-base` and `--target-base`. Preview:

```bash
python3 tools/josh/push-subtree-branch.py \
    --source-rev bluekernel/miri/allocator \
    --target-remote fork-build \
    --repo build \
    --target-branch miri/allocator
```

| Parameter         | Purpose                                                  |
| ----------------- | -------------------------------------------------------- |
| `--source-base`   | Excluded central baseline; requires `--target-base`.     |
| `--source-rev`    | Required central range tip; includes this commit.        |
| `--target-base`   | Child replay baseline; requires `--source-base`.         |
| `--target-remote` | Configured target Josh remote.                           |
| `--repo`          | Child repository name; same mapping as the merge script. |
| `--target-branch` | Child branch to update or create.                        |
| `--repo-root`     | Central checkout; defaults to the script's repository.   |
| `--push`          | Push after a successful preview; omit for a dry run.     |
| `--force` / `-f`  | Pass Josh's `--force`; independent of `--push`.          |

For an actual push, use the same arguments with `--push`. For kernel, use
`--target-remote fork-kernel --repo kernel`. Configure each remote with the
corresponding `:prefix=<directory>` filter.

Add `--force` when rewritten history requires a non-fast-forward update.
`--force` alone is still a dry run; `--force --push` performs a force push.
Preview and actual push use the same Josh force option.

```bash
python3 tools/josh/push-subtree-branch.py \
    --source-rev bluekernel/miri/allocator \
    --target-remote fork-build \
    --repo build \
    --target-branch miri/allocator \
    --force --push
```

This is Josh's ordinary force push. It allows overwriting the target branch's
existing history and has no `--force-with-lease` check. Force changes whether
Git accepts a non-fast-forward update; it uses the same Josh reverse-mapped
result.

The script saves the filtered result in the reusable ref
`refs/export/<remote>/<target-branch>`. Range mode also saves the filtered
central baseline in `refs/export-bases/<remote>/<target-branch>`. These refs
are regenerated each time and retained for inspection after success or
failure. There is no push progress file or coupling to the merge script.
Run Josh operations sequentially within the same repository.

The script first previews the Josh push. Its English summary shows
`BEFORE (current remote)`, the child branch fetched before the update, and
`AFTER (proposed, not pushed)`, the candidate child branch. Each list shows
commits above `--target-base`, limited to the latest 20, oldest first. In
full-history mode, there is no `--target-base`: the lists instead show
current commits omitted by the candidate and new commits in the candidate.
New branches are explicitly marked as not yet existing. The summary also
shows added and removed commit counts by SHA, and whether the candidate's
files match the current remote. Replay can change SHAs; removing an old
commit does not mean its file changes were lost.

A successful preview suppresses Josh's raw `Pushed` output and ends with an
explicit statement that the remote was not updated. `Push completed` appears
only after a successful actual push. A failed preview retains Josh's raw
error output. Candidate SHA parsing depends on the verified Josh version
`r26.07.19` and its `Pushing <SHA> to ...` output format. If that line is
missing, the script returns an error without performing an actual push.
Without `--force`, a normal push rejects non-fast-forward updates.

The script checks whether the actual Josh candidate's files match the
selected source directory. In range mode, `bluekernel-version` and
`blueos-version` must instead match the target base, including whether each
file exists. A mismatch returns
an error without performing an actual push. This check depends on the
candidate SHA output line above.
The selected child directory must exist in the source commit.

Using only `--source-rev` preserves the entire reachable history, including
sync version files and their changes. A SHA selects a branch tip, not a
commit range. Central import merges and old sync
commits may also appear in the exported history. To exclude that old
history, explicitly supply `--source-base` and `--target-base`; force does
not identify business boundaries automatically. Range commits that do not
affect the selected directory do not appear as new child commits after
filtering.
