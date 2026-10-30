#!/usr/bin/env python3
"""Reverse-map a subtree branch and merge it into BlueKernel."""

import argparse
import shlex
import subprocess
import sys
from pathlib import Path

PATH_MAP = {
    "apps_shell": "apps/shell",
    "apps_example": "apps/example",
    "book": "book",
    "build": "build",
    "external": "external",
    "kernel": "kernel",
    "libc": "libc",
    "librs": "librs",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--source-remote",
                        required=True,
                        help="Configured Josh remote")
    parser.add_argument("--source-branch",
                        required=True,
                        help="Child repository branch")
    parser.add_argument("--repo", required=True, choices=PATH_MAP)
    parser.add_argument(
        "--target-base",
        default="main",
        help="BlueKernel mapping baseline; branch, SHA or Git expression",
    )
    parser.add_argument("--target-branch",
                        required=True,
                        help="Branch to create or merge into")
    parser.add_argument("--repo-root",
                        type=Path,
                        default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()
    git_dir = None

    def run(*command, capture=False, check=True):
        if not capture:
            print(f"$ {shlex.join(command)}", flush=True)
        return subprocess.run(command,
                              cwd=args.repo_root,
                              text=True,
                              capture_output=capture,
                              check=check)

    def git(*command):
        return run("git", *command, capture=True).stdout.strip()

    def commit(revision):
        return git("rev-parse", "--verify", "--end-of-options",
                   f"{revision}^{{commit}}")

    def require_clean():
        states = (
            "MERGE_HEAD",
            "CHERRY_PICK_HEAD",
            "REVERT_HEAD",
            "rebase-merge",
            "rebase-apply",
            "sequencer",
        )
        if any((git_dir / state).exists() for state in states):  # type: ignore
            raise ValueError(
                "Finish or abort the current Git operation before importing")
        if git("status", "--porcelain", "--untracked-files=no"):
            raise ValueError(
                "Commit or stash tracked changes before importing")

    try:
        git_dir = Path(git("rev-parse", "--absolute-git-dir"))
        require_clean()
        if any(
                name.startswith("-")
                for name in (args.source_remote, args.source_branch,
                             args.target_branch)):
            raise ValueError("Remote and branch names cannot start with '-'")
        target_ref = f"refs/heads/{args.target_branch}"
        source_ref = f"refs/remotes/{args.source_remote}/{args.source_branch}"
        git("check-ref-format", target_ref)
        git("check-ref-format", source_ref)
        base_oid = commit(args.target_base)
        exists = (run(
            "git",
            "show-ref",
            "--verify",
            "--quiet",
            target_ref,
            capture=True,
            check=False,
        ).returncode == 0)
        if exists:
            target_oid = commit(target_ref)
            ancestor = run(
                "git",
                "merge-base",
                "--is-ancestor",
                base_oid,
                target_oid,
                capture=True,
                check=False,
            )
            if ancestor.returncode:
                raise ValueError(
                    "--target-base must be an ancestor of the existing target")

        path = PATH_MAP[args.repo]
        if git("cat-file", "-t", f"{base_oid}:{path}") != "tree":
            raise ValueError(
                f"Starting revision has no subtree directory: {path}")
        print(f"Round starting commit: {base_oid}", flush=True)
        run("josh", "fetch", "--remote", args.source_remote)
        source_oid = commit(source_ref)
        if git("cat-file", "-t", f"{source_oid}:{path}") != "tree":
            raise ValueError(
                f"Josh remote does not expose prefix {path}: {source_ref}")

        snapshot_ref = f"refs/import/{args.target_branch}/source/0"
        mapped_ref = f"refs/import/{args.target_branch}/mapped/0"
        run("git", "update-ref", snapshot_ref, source_oid)
        # Reverse filtering updates its input ref; never use the target branch here.
        run("git", "update-ref", mapped_ref, base_oid)
        run(
            "josh-filter",
            f"::{path}/",
            mapped_ref,
            "--update",
            snapshot_ref,
            "--reverse",
            "--check-roundtrip",
        )
        mapped_oid = commit(mapped_ref)

        require_clean()
        if exists:
            if commit(target_ref) != target_oid:  # type: ignore
                raise ValueError(
                    "Target branch changed during preparation; rerun the command"
                )
            run("git", "switch", "--no-guess", args.target_branch)
        else:
            run("git", "switch", "-c", args.target_branch, base_oid)
        run(
            "git",
            "merge",
            "--no-ff",
            "--no-edit",
            "-m",
            f"Import {args.source_remote}/{args.source_branch} into bluekernel",
            mapped_oid,
        )
        print(f"\nUpdated branch: {args.target_branch}")
        return 0
    except (
            subprocess.CalledProcessError,
            OSError,
            ValueError,
            KeyboardInterrupt,
    ) as error:
        detail = (error.stderr if isinstance(
            error, subprocess.CalledProcessError) else None)
        print(
            f"Import stopped: {(detail or str(error)).strip() or 'interrupted'}",
            file=sys.stderr,
        )
        if git_dir and (git_dir / "MERGE_HEAD").exists():
            print(
                "Resolve conflicts, git add the files, and git merge --continue.",
                file=sys.stderr,
            )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
