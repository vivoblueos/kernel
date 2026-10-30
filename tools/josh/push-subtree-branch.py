#!/usr/bin/env python3
"""Filter a BlueKernel revision and try pushing it to a child repository branch."""

import argparse
import re
import shlex
import subprocess
import sys
import tempfile
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

# These files are maintained by the subtree sync automation, not developers.
SYNC_VERSION_FILES = ("bluekernel-version", "blueos-version")


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument(
        "--source-rev",
        required=True,
        help=
        "Source BlueKernel commit (range end included); branch, SHA or Git expression",
    )
    parser.add_argument(
        "--source-base",
        help=
        "Excluded BlueKernel baseline; branch, SHA or Git expression; requires --target-base",
    )
    parser.add_argument("--target-remote",
                        required=True,
                        help="Configured Josh remote")
    parser.add_argument("--repo", required=True, choices=PATH_MAP)
    parser.add_argument("--target-branch",
                        required=True,
                        help="Child branch to update or create")
    parser.add_argument("--repo-root",
                        type=Path,
                        default=Path(__file__).resolve().parents[2])
    parser.add_argument("--push",
                        action="store_true",
                        help="Actually push; default is dry-run")
    parser.add_argument("--force",
                        "-f",
                        action="store_true",
                        help="Pass --force to Josh push")
    parser.add_argument(
        "--target-base",
        help="Child branch to replay onto; requires --source-base")
    args = parser.parse_args()
    if (args.source_base is None) != (args.target_base is None):
        parser.error(
            "--source-base and --target-base must be supplied together")

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

    def check_files(left, right, message, prefix=""):
        paths = ["."]
        if args.source_base is not None:
            paths.extend(f":(top,exclude,literal){prefix}{name}"
                         for name in SYNC_VERSION_FILES)
        differences = git("diff", "--no-ext-diff", "--no-textconv",
                          "--name-only", left, right, "--", *paths)
        if differences:
            raise ValueError(f"{message}:\n{differences}")

    def show_commits(label, revision):
        count = git("rev-list", "--count", revision)
        limit = " (showing latest 20, oldest first)" if int(count) > 20 else ""
        print(f"  {label}: {count}{limit}", flush=True)
        entries = git("log", "--reverse", "--format=%h %s", "--max-count=20",
                      revision)
        for entry in entries.splitlines():
            print(f"    {entry}", flush=True)

    try:
        if args.target_remote.startswith("-") or args.target_branch.startswith(
                "-"):
            raise ValueError(
                "Remote and target branch names cannot start with '-'")
        destination = f"refs/heads/{args.target_branch}"
        tracking = f"refs/remotes/{args.target_remote}/{args.target_branch}"
        export_ref = f"refs/export/{args.target_remote}/{args.target_branch}"
        for reference in (destination, tracking, export_ref):
            git("check-ref-format", reference)
        source_oid = git(
            "rev-parse",
            "--verify",
            "--end-of-options",
            f"{args.source_rev}^{{commit}}",
        )
        path = PATH_MAP[args.repo]
        if git("cat-file", "-t", f"{source_oid}:{path}") != "tree":
            raise ValueError(
                f"Source revision has no subtree directory: {path}")
        print(f"Source commit: {source_oid}", flush=True)
        base_oid = None
        if args.source_base is not None:
            base_oid = git(
                "rev-parse",
                "--verify",
                "--end-of-options",
                f"{args.source_base}^{{commit}}",
            )
            if run(
                    "git",
                    "merge-base",
                    "--is-ancestor",
                    base_oid,
                    source_oid,
                    capture=True,
                    check=False,
            ).returncode:
                raise ValueError(
                    "--source-base must be an ancestor of --source-rev (or the same commit)"
                )
            if args.target_base.startswith("-"):
                raise ValueError("Target base branch cannot start with '-'")
            git("check-ref-format", f"refs/heads/{args.target_base}")
            print(
                f"Export range (base excluded): {base_oid}..{source_oid}; "
                f"child base: {args.target_base}",
                flush=True,
            )
        run("josh", "fetch", "--remote", args.target_remote)
        exists = (run(
            "git",
            "show-ref",
            "--verify",
            "--quiet",
            tracking,
            capture=True,
            check=False,
        ).returncode == 0)
        if exists and git("cat-file", "-t", f"{tracking}:{path}") != "tree":
            raise ValueError(
                f"Josh remote does not expose prefix {path}: {tracking}")
        export_filter = f"::{path}/"
        if base_oid is not None:
            # Remove marker changes before replay, including marker-only commits.
            # Rebase then carries the target base's markers through unchanged.
            markers = ",".join(f"::{path}/{name}"
                               for name in SYNC_VERSION_FILES)
            export_filter += f":exclude[{markers}]"
        run("josh-filter", export_filter, source_oid, "--update", export_ref)
        if base_oid is not None:
            base_ref = f"refs/export-bases/{args.target_remote}/{args.target_branch}"
            onto_ref = f"refs/remotes/{args.target_remote}/{args.target_base}"
            onto_oid = git("rev-parse", "--verify", f"{onto_ref}^{{commit}}")
            run("josh-filter", export_filter, base_oid, "--update", base_ref)
            filtered_base = git("rev-parse", base_ref)
            filtered_head = git("rev-parse", export_ref)
            git("merge-base", "--is-ancestor", filtered_base, filtered_head)
            check_files(filtered_base, onto_oid,
                        "Center base files differ from child target base",
                        f"{path}/")
            with tempfile.TemporaryDirectory(
                    prefix="bluekernel-josh-export-") as worktree:
                run("git", "worktree", "add", "--detach", worktree,
                    filtered_head)
                try:
                    run(
                        "git",
                        "-C",
                        worktree,
                        "rebase",
                        "--no-autosquash",
                        "--no-update-refs",
                        "--no-autostash",
                        "--no-rebase-merges",
                        "--no-fork-point",
                        "--committer-date-is-author-date",
                        "--onto",
                        onto_oid,
                        filtered_base,
                    )
                    candidate = git("-C", worktree, "rev-parse", "HEAD")
                    check_files(filtered_head, candidate,
                                "Replayed files differ from filtered source",
                                f"{path}/")
                    run("git", "update-ref", export_ref, candidate)
                finally:
                    run(
                        "git",
                        "-C",
                        worktree,
                        "rebase",
                        "--abort",
                        capture=True,
                        check=False,
                    )
                    run("git", "worktree", "remove", "--force", worktree)
        refspec = f"{export_ref}:{destination}"
        push_command = ["josh", "push", args.target_remote, refspec]
        # Keep the current raw history when the candidate extends its projection.
        # Overriding Josh's base in that case can fold existing commits into a new one.
        if base_oid is not None and (not exists or run(
                "git",
                "merge-base",
                "--is-ancestor",
                tracking,
                export_ref,
                capture=True,
                check=False,
        ).returncode):
            push_command.extend(["--base", args.target_base])
        if args.force:
            push_command.append("--force")

        # Josh's dry-run computes the raw child commit too; show that history,
        # rather than treating the prefixed center projection as the result.
        preview = run(*push_command, "--dry-run", capture=True, check=False)
        pattern = rf"^Pushing ([0-9a-f]{{40}}) to {re.escape(args.target_remote)}/{re.escape(destination)}$"
        match = re.search(pattern, preview.stderr + preview.stdout,
                          re.MULTILINE)
        # Successful Josh previews say "Pushed", even though no ref was pushed.
        # Show our explicit before/after summary; retain raw output on failure.
        if preview.returncode or not match:
            print(preview.stdout, end="", flush=True)
            print(preview.stderr, end="", file=sys.stderr, flush=True)
        if preview.returncode == 0 and not match:
            raise ValueError(
                "Josh dry-run did not report a candidate commit; cannot verify files"
            )
        if match:
            candidate = match.group(1)
            candidate_tree = git("rev-parse", f"{candidate}^{{tree}}")
            check_files(
                f"{source_oid}:{path}", candidate_tree,
                "Josh result files differ from the selected source subtree")
            if base_oid is not None:
                # Verify Josh's reverse mapping also preserves the target markers.
                git("diff", "--no-ext-diff", "--no-textconv", "--exit-code",
                    f"{onto_oid}:{path}", candidate_tree, "--",
                    *(f":(top,literal){name}" for name in SYNC_VERSION_FILES))
            raw_ref = f"refs/josh/remotes/{args.target_remote}/{args.target_branch}"
            current = git("rev-parse", raw_ref) if exists else None
            title = "PUSH PREVIEW" if args.push else "DRY RUN"
            print(f"\n[{title}] Proposed update (not pushed yet)", flush=True)
            print(f"Target branch: {args.target_remote}/{args.target_branch}",
                  flush=True)
            child_base = None
            if base_oid is not None:
                child_base = git(
                    "rev-parse",
                    f"refs/josh/remotes/{args.target_remote}/{args.target_base}",
                )
                print(
                    f"Base branch: {args.target_remote}/{args.target_base} ({child_base})",
                    flush=True,
                )
            print(
                f"\nBEFORE (current remote): {current or 'branch does not exist; a new branch will be created'}",
                flush=True,
            )
            if current:
                show_commits(
                    f"Commits above {args.target_base}" if child_base else
                    "Current commits absent from the proposed result",
                    f"{child_base or candidate}..{current}",
                )
            print(f"\nAFTER (proposed, not pushed): {candidate}", flush=True)
            show_commits(
                f"Commits above {args.target_base}" if child_base else
                "New commits compared with the current remote",
                f"{child_base or current}..{candidate}"
                if child_base or current else candidate,
            )
            added = git(
                "rev-list",
                "--count",
                f"{current}..{candidate}" if current else candidate,
            )
            removed = (git("rev-list", "--count", f"{candidate}..{current}")
                       if current else "0")
            print(
                f"\nHistory changes (compared by SHA): {added} added, {removed} removed.",
                flush=True,
            )
            if current and added != "0" and removed != "0":
                print(
                    "Replay can replace a commit with an equivalent new SHA; these counts do not measure file changes.",
                    flush=True,
                )
            files = f"Files: match source subtree '{path}'"
            if base_oid is not None:
                files += (" except sync version files "
                          "(preserved from target base)")
            if current:
                same = git("rev-parse",
                           f"{current}^{{tree}}") == candidate_tree
                files += ("; identical to the current remote"
                          if same else "; different from the current remote")
            print(f"{files}.", flush=True)
        if preview.returncode:
            raise ValueError("Josh push dry-run failed; nothing was pushed")
        if args.push:
            run(*push_command)
            print(
                f"\nPush completed: {args.target_remote}/{args.target_branch} -> {candidate}"  # type: ignore
            )
        else:
            print(
                "\nDry run completed. Remote branch was not updated. Add --push to apply this result."
            )
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
            f"Push stopped: {(detail or str(error)).strip() or 'interrupted'}",
            file=sys.stderr,
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
