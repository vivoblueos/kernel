#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

import argparse
import subprocess
import sys
import shutil
from pathlib import Path
from typing import List, Tuple
import platform
import xml.etree.ElementTree as ET


def get_default_branch(repo: str) -> str:
    """Get default branch from manifest.xml, checking project revision then default revision"""
    manifest_path = Path(repo).parent / ".repo" / "manifests" / "manifest.xml"
    if manifest_path.exists():
        tree = ET.parse(manifest_path)
        root = tree.getroot()

        # Get project name from repo path
        repo_name = Path(repo).name

        # Check project-specific revision first
        for project in root.findall("project"):
            if project.get("name") == repo_name:
                revision = project.get("revision")
                if revision:
                    return revision

        # Fall back to default revision
        default = root.find("default")
        if default is not None:
            return default.get("revision", "main")

    return "main"


def get_changed_files(repo: str) -> List[str]:
    """Get list of modified files in the merge request"""
    try:
        default_branch = get_default_branch(repo)
        subprocess.run(["git", "fetch", "origin", default_branch],
                       check=True,
                       stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL,
                       cwd=repo)

        result = subprocess.run([
            "git", "diff", "--name-only", "--diff-filter=ACMR",
            f"origin/{default_branch}"
        ],
                                check=True,
                                capture_output=True,
                                text=True,
                                cwd=repo)
        return [f.strip() for f in result.stdout.splitlines() if f.strip()]
    except subprocess.CalledProcessError as e:
        print(f"❌ Failed to get changed files: {e.stderr}")
        raise Exception("Get changed files failed!!!")


def check_files_format(repo: str, files: List[str]) -> List[Tuple[str, str]]:
    """Check formatting for different file types"""
    errors = []

    # Categorize files
    rust_files = []
    python_files = []
    if 'external' not in repo:
        rust_files = [f for f in files if f.endswith(".rs")]
        python_files = [f for f in files if f.endswith(".py")]
    gn_files = [f for f in files if f.endswith((".gn", ".gni"))]

    # Check Rust formatting
    if rust_files:
        try:
            subprocess.run([
                "rustfmt",
                "--edition=2021",
                "--check",
                "--unstable-features",
                "--skip-children",
            ] + rust_files,
                           check=True,
                           capture_output=True,
                           text=True,
                           cwd=repo)
        except subprocess.CalledProcessError as e:
            errors.append(("Rust", e.stdout + e.stderr))

    # Check GN formatting
    for gn_file in gn_files:
        try:
            subprocess.run(["gn", "format", "--dry-run", gn_file],
                           check=True,
                           capture_output=True,
                           text=True,
                           cwd=repo)
        except subprocess.CalledProcessError as e:
            errors.append(("GN", f"{gn_file}: {e.stderr}"))

    # Check Python formatting with yapf3
    for py_file in python_files:
        try:
            yapf = "yapf3"
            if platform.system() == "Darwin":
                yapf = "yapf"
            subprocess.run([yapf, "-d", py_file],
                           check=True,
                           capture_output=True,
                           text=True,
                           cwd=repo)
        except subprocess.CalledProcessError as e:
            errors.append(("Python", f"{py_file}: {e.stderr}"))

    return errors


def check_format(repo_to_check):
    print(f"🔍 Checking format of {repo_to_check} ...")
    format_errors = []
    for repo in repo_to_check:
        try:
            changed_files = get_changed_files(repo.strip())
        except Exception as e:
            raise
        format_errors.extend(check_files_format(repo.strip(), changed_files))
    if format_errors:
        print("\n❌ Formatting issues found:")
        for lang, msg in format_errors:
            print(f"\n===== {lang} Issues =====")
            print(msg.strip())
        print("\n🛠️  Fix suggestions:")
        print("Rust  : Run 'rustfmt [file]'")
        print("GN    : Run 'gn format [file]'")
        print("Python: Run 'yapf3 -i [file]'")
        sys.stdout.flush()
        raise Exception("Format check failed!!!")
    print("✅ All files are properly formatted!")
    sys.stdout.flush()


def main():
    # The script lives at <kernel_root>/build/ci/run_check_fmt.py
    kernel_root = str(Path(__file__).resolve().parent.parent.parent)

    parser = argparse.ArgumentParser(
        description='Check code formatting for BlueOS kernel repos')
    parser.add_argument(
        'repo_paths',
        nargs='*',
        default=[kernel_root],
        help=
        'Repository paths to check (default: kernel repo root derived from script location)'
    )
    args = parser.parse_args()
    try:
        check_format(args.repo_paths)
    except Exception as e:
        sys.exit(1)


if __name__ == '__main__':
    main()
