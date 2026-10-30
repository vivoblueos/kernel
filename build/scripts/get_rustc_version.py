#!/usr/bin/env python3
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
"""Prints the minor version of the active rustc (e.g. 96 for 1.96.0-dev).

Toolchains in build/toolchain/BUILD.gn invoke rustc by its bare name, so the
rustup/PATH default is the source of truth — this script queries the very
same `rustc` the build will run.
"""

import re
import subprocess
import sys

_RELEASE_RE = re.compile(r"^release: (\d+)\.(\d+)")


def main():
    try:
        out = subprocess.run(["rustc", "-vV"],
                             stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE,
                             text=True,
                             check=True)
    except (OSError, subprocess.CalledProcessError) as e:
        print("error: failed to run `rustc -vV`: %s" % e, file=sys.stderr)
        return 1

    for line in out.stdout.splitlines():
        m = _RELEASE_RE.match(line.strip())
        if m:
            # Pre-release suffixes (-dev/-nightly) are compared as the base
            # version: 1.96.0-dev counts as 1.96.
            print(m.group(2))
            return 0

    print("error: no `release:` line in `rustc -vV` output", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
