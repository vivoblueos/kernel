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
import shutil
import sys
from pathlib import Path
from typing import List, Tuple


def check_repo_license(repo) -> List[Tuple[str, str]]:
    """
    Check if the license header is present in the specified repo.
    Use repo .license-eye.yaml configuration file
    """
    errors = []
    if shutil.which("license-eye"):
        # for file in files:
        try:
            # every repo should first has license-eye configured
            # so just run use the default configuration
            result = subprocess.run(["license-eye", "header", "check"],
                                    capture_output=True,
                                    text=True,
                                    cwd=repo)
            if "don't have a valid license header" in result.stdout or result.returncode != 0:
                errors.append(
                    ("License Header:", f"{result.stdout + result.stderr}"))
        except subprocess.CalledProcessError as e:
            errors.append(("License Header", f": {e.stdout + e.stderr}"))
    else:
        print("❌ license-eye tool not found. Please install it first.")
        print(
            "Install with: go install github.com/apache/skywalking-eyes/cmd/license-eye@latest"
        )
        raise Exception("license-eye tool not found!!!")
    return errors


def check_license(repo_to_check):
    print(f"🔍 Checking license of {repo_to_check} ...")
    check_errors = []
    for repo in repo_to_check:
        if "libc" in repo or "book" in repo or "external" in repo:
            print(
                f"Skipping {repo} as it is not a valid repository for license check."
            )
            continue
        check_errors.extend(check_repo_license(repo.strip()))
    if check_errors:
        print("\n❌ Licenses issues found:")
        for _, msg in check_errors:
            print(f"\n===== License Issues =====")
            print(msg.strip())
        print("License Header: Run 'cd repo && license-eye header fix'")
        sys.stdout.flush()
        raise Exception("License check failed!!!")
    print("✅ All repos licenses are checked!")
    sys.stdout.flush()


def main():
    kernel_root = str(Path(__file__).resolve().parent.parent.parent)

    parser = argparse.ArgumentParser(
        description='Check license headers for BlueKernel repos')
    parser.add_argument(
        'repo_paths',
        nargs='*',
        default=[kernel_root],
        help=
        'Repository paths to check (default: kernel repo root derived from script location)'
    )
    args = parser.parse_args()
    try:
        check_license(args.repo_paths)
    except Exception as e:
        sys.exit(1)


if __name__ == '__main__':
    main()
