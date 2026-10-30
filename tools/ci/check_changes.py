#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""Check formatting and license headers for files changed by a pull request."""

import argparse
import os
import platform
import shlex
import subprocess
import sys
from collections import defaultdict
from pathlib import Path, PurePosixPath
from typing import Iterable, Sequence

REPO_ROOT = Path(__file__).resolve().parents[2]
LICENSE_ROOTS = (
    PurePosixPath("kernel"),
    PurePosixPath("build"),
    PurePosixPath("librs"),
    PurePosixPath("apps/example"),
    PurePosixPath("apps/shell"),
    PurePosixPath("tools/ci"),
)


class CheckFailure(Exception):
    """Raised when a changed-file check cannot be completed or fails."""


def _git(command: Sequence[str], repo_root: Path = REPO_ROOT) -> bytes:
    try:
        result = subprocess.run(
            ("git", *command),
            cwd=repo_root,
            check=False,
            capture_output=True,
        )
    except OSError as error:
        raise CheckFailure(f"unable to run git: {error}") from error
    if result.returncode != 0:
        diagnostic = result.stderr.decode(errors="replace").strip()
        raise CheckFailure(diagnostic or f"git {' '.join(command)} failed")
    return result.stdout


def get_changed_files(base: str,
                      head: str,
                      repo_root: Path = REPO_ROOT) -> list[str]:
    """Return changed paths, including both sides of moves between components."""
    _git(("cat-file", "-e", f"{base}^{{commit}}"), repo_root)
    _git(("cat-file", "-e", f"{head}^{{commit}}"), repo_root)
    output = _git((
        "diff",
        "--name-only",
        "--no-renames",
        "-z",
        base,
        head,
        "--",
    ), repo_root)
    return [os.fsdecode(path) for path in output.split(b"\0") if path]


def format_groups(files: Iterable[str]) -> dict[str, list[str]]:
    """Group changed paths by formatter, preserving the legacy exclusions."""
    groups: dict[str, list[str]] = defaultdict(list)
    for file_name in files:
        path = PurePosixPath(file_name)
        if path.parts and path.parts[0] == "external":
            continue
        suffix = path.suffix.lower()
        if suffix == ".rs":
            groups["rust"].append(file_name)
        elif suffix == ".py":
            groups["python"].append(file_name)
        elif suffix in (".gn", ".gni"):
            groups["gn"].append(file_name)
        elif suffix in (".yml", ".yaml"):
            groups["yaml"].append(file_name)
    return dict(groups)


def affected_license_roots(files: Iterable[str]) -> list[PurePosixPath]:
    """Return license configuration roots touched by the changed paths."""
    changed = [PurePosixPath(file_name) for file_name in files]
    return [
        root for root in LICENSE_ROOTS
        if any(path == root or root in path.parents for path in changed)
    ]


def _run(command: Sequence[str],
         cwd: Path = REPO_ROOT) -> subprocess.CompletedProcess:
    print(f"+ {shlex.join(command)}", flush=True)
    try:
        return subprocess.run(command,
                              cwd=cwd,
                              check=False,
                              capture_output=True,
                              text=True)
    except OSError as error:
        raise CheckFailure(f"unable to run {command[0]}: {error}") from error


def _diagnostic(result: subprocess.CompletedProcess) -> str:
    return "\n".join(part.strip() for part in (result.stdout, result.stderr)
                     if part.strip())


def check_format(files: Iterable[str],
                 repo_root: Path = REPO_ROOT) -> list[str]:
    """Run formatters in check-only mode and return diagnostics."""
    existing_files = [
        file_name for file_name in files if (repo_root / file_name).is_file()
    ]
    groups = format_groups(existing_files)
    failures: list[str] = []

    # A separate invocation lets rustfmt discover each file's component config.
    for file_name in groups.get("rust", []):
        result = _run((
            "rustfmt",
            "--edition=2021",
            "--check",
            "--unstable-features",
            "--skip-children",
            file_name,
        ), repo_root)
        if result.returncode != 0:
            failures.append(f"Rust formatting failed:\n{_diagnostic(result)}")

    for file_name in groups.get("gn", []):
        result = _run(("gn", "format", "--dry-run", file_name), repo_root)
        if result.returncode != 0:
            failures.append(
                f"GN formatting failed for {file_name}:\n{_diagnostic(result)}"
            )

    yapf = "yapf" if platform.system() == "Darwin" else "yapf3"
    for file_name in groups.get("python", []):
        result = _run((yapf, "-d", file_name), repo_root)
        if result.returncode != 0 or result.stdout.strip():
            failures.append(
                f"Python formatting failed for {file_name}:\n{_diagnostic(result)}"
            )

    for file_name in groups.get("yaml", []):
        command = ["yamlfmt", "-lint"]
        directory = (repo_root / file_name).parent
        while directory != repo_root:
            if (directory / ".yamlfmt").is_file():
                command.extend(("-conf", str(directory / ".yamlfmt")))
                break
            directory = directory.parent
        result = _run((*command, file_name), repo_root)
        if result.returncode != 0:
            failures.append(
                f"YAML formatting failed for {file_name}:\n{_diagnostic(result)}"
            )

    return failures


def check_licenses(files: Iterable[str],
                   repo_root: Path = REPO_ROOT) -> list[str]:
    """Run license-eye once for every affected configured subtree."""
    failures: list[str] = []
    for root in affected_license_roots(files):
        config = repo_root / root / ".licenserc.yaml"
        if not config.is_file():
            failures.append(f"License configuration is missing: {config}")
            continue
        result = _run(("license-eye", "header", "check"), repo_root / root)
        if result.returncode != 0:
            failures.append(
                f"License check failed for {root}:\n{_diagnostic(result)}")
    return failures


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base",
                        required=True,
                        help="Pull request base commit")
    parser.add_argument("--head",
                        required=True,
                        help="Checked-out merge commit")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        changed_files = get_changed_files(args.base, args.head)
        print(f"Checking {len(changed_files)} changed file(s).", flush=True)
        failures = check_format(changed_files)
        failures.extend(check_licenses(changed_files))
    except CheckFailure as error:
        print(f"Unable to complete checks: {error}", file=sys.stderr)
        return 1

    if failures:
        print("\n\n".join(failures), file=sys.stderr)
        return 1
    print("All changed-file checks passed.", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
