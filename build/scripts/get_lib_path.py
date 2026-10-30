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

import subprocess
import sys
import os


def main():
    if len(sys.argv) < 3:
        print("Usage: get_lib_path.py <compiler> <lib_name> [extra_flags...]",
              file=sys.stderr)
        sys.exit(1)

    compiler = sys.argv[1]
    lib_name = sys.argv[2]
    extra_flags = sys.argv[3:]

    cmd = [compiler] + extra_flags + ["-print-file-name=" + lib_name]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"Error: {result.stderr}", file=sys.stderr)
        sys.exit(1)
    print(os.path.abspath(result.stdout.strip()), end='')


if __name__ == "__main__":
    main()
