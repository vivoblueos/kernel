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
"""Find component repositories affected by a monorepo update."""

import argparse
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Iterable, Sequence

import tomllib

REPO_ROOT = Path(__file__).resolve().parents[2]


class TargetFailure(Exception):
    """Raised when affected subrepos cannot be determined safely."""


@dataclass(frozen=True)
class Subrepo:
    owner: str
    repository: str
    path: PurePosixPath


def _git(command: Sequence[str], repo_root: Path = REPO_ROOT) -> bytes:
    try:
        result = subprocess.run(("git", *command),
                                cwd=repo_root,
                                check=False,
                                capture_output=True)
    except OSError as error:
        raise TargetFailure(f"unable to run git: {error}") from error
    if result.returncode != 0:
        diagnostic = result.stderr.decode(errors="replace").strip()
        raise TargetFailure(diagnostic or f"git {' '.join(command)} failed")
    return result.stdout


def get_changed_files(base: str,
                      head: str,
                      repo_root: Path = REPO_ROOT) -> list[str]:
    """Return all paths whose contents differ between two commits."""
    _git(("cat-file", "-e", f"{base}^{{commit}}"), repo_root)
    _git(("cat-file", "-e", f"{head}^{{commit}}"), repo_root)
    output = _git(("diff", "--name-only", "--no-renames", "-z", base, head),
                  repo_root)
    return [os.fsdecode(path) for path in output.split(b"\0") if path]


def _config_paths(repo_root: Path) -> Iterable[Path]:
    for path in repo_root.rglob("josh-sync.toml"):
        relative = path.relative_to(repo_root)
        if relative.parts[0] == "out" or any(
                part.startswith(".") for part in relative.parts):
            continue
        yield path


def load_subrepos(repo_root: Path = REPO_ROOT) -> list[Subrepo]:
    """Load subrepo boundaries from their checked-in josh-sync configs."""
    subrepos: list[Subrepo] = []
    seen_paths: set[PurePosixPath] = set()
    seen_repositories: set[tuple[str, str]] = set()
    for config_path in sorted(_config_paths(repo_root)):
        try:
            with config_path.open("rb") as config_file:
                config = tomllib.load(config_file)
            owner = config["org"]
            repository = config["repo"]
            component_path = PurePosixPath(config["path"])
        except (OSError, KeyError, TypeError,
                tomllib.TOMLDecodeError) as error:
            raise TargetFailure(f"invalid {config_path}: {error}") from error

        relative_parent = PurePosixPath(
            config_path.parent.relative_to(repo_root).as_posix())
        if component_path != relative_parent:
            raise TargetFailure(
                f"{config_path} declares path {component_path}, expected "
                f"{relative_parent}")
        if not owner or not repository:
            raise TargetFailure(f"{config_path} has an empty org or repo")
        if component_path in seen_paths:
            raise TargetFailure(f"duplicate subrepo path: {component_path}")
        repository_key = (owner, repository)
        if repository_key in seen_repositories:
            raise TargetFailure(f"duplicate subrepo: {owner}/{repository}")

        seen_paths.add(component_path)
        seen_repositories.add(repository_key)
        subrepos.append(Subrepo(owner, repository, component_path))
    return subrepos


def affected_subrepos(files: Iterable[str],
                      subrepos: Iterable[Subrepo]) -> list[Subrepo]:
    """Return subrepos containing at least one changed path."""
    changed_paths = [PurePosixPath(file_name) for file_name in files]
    return [
        subrepo for subrepo in subrepos
        if any(path == subrepo.path or subrepo.path in path.parents
               for path in changed_paths)
    ]


def write_github_output(path: Path, targets: Sequence[Subrepo]) -> None:
    """Write the owner and repository list consumed by GitHub Actions."""
    owners = {target.owner for target in targets}
    if len(owners) > 1:
        raise TargetFailure("affected subrepos span multiple organizations")
    owner = next(iter(owners), "")
    repositories = ",".join(target.repository for target in targets)
    with path.open("a", encoding="utf-8") as output:
        output.write(f"has-targets={'true' if targets else 'false'}\n")
        output.write(f"owner={owner}\n")
        output.write(f"repositories={repositories}\n")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, help="Commit before the push")
    parser.add_argument("--head", required=True, help="Commit after the push")
    parser.add_argument(
        "--github-output",
        type=Path,
        required=True,
        help="Path from the GITHUB_OUTPUT environment variable")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        changed_files = get_changed_files(args.base, args.head)
        targets = affected_subrepos(changed_files, load_subrepos())
        write_github_output(args.github_output, targets)
    except TargetFailure as error:
        print(f"Unable to determine affected subrepos: {error}",
              file=sys.stderr)
        return 1

    print(f"Changed files: {len(changed_files)}", flush=True)
    if targets:
        for target in targets:
            print(f"Affected subrepo: {target.owner}/{target.repository}")
    else:
        print("No component repository is affected.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
