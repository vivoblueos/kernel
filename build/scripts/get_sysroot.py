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

import subprocess
import sys
import argparse
import re
import os


def main():
    parser = argparse.ArgumentParser(
        description="Get sysroot path for a compiler")
    parser.add_argument("compiler",
                        help="Compiler command (e.g., arm-none-eabi-gcc)")
    args = parser.parse_args()

    try:
        result = subprocess.run([args.compiler, "--print-sysroot"],
                                capture_output=True,
                                text=True,
                                check=True)
        if result.returncode != 0:
            print(
                f"Error: Could not find sysroot via `{args.compiler} --print-sysroot'",
                file=sys.stderr)
            sys.exit(1)
        print(os.path.abspath(result.stdout).strip(), end='')
    except subprocess.CalledProcessError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    except FileNotFoundError:
        print(f"Error: Compiler `{args.compiler}' not found", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
