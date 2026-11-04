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

# Prints rustc configuration for GN's exec_script. `--target` prints
# `rustc --print cfg` lines, `--host-triple` prints the host triple without a
# trailing newline.

import argparse
import shlex
import subprocess
import sys


def strip_target(args):
    # Drop any `--target`/`--target=` so the caller's triple wins.
    result = []
    index = 0
    while index < len(args):
        if args[index] == "--target":
            index += 2
            continue
        if args[index].startswith("--target="):
            index += 1
            continue
        result.append(args[index])
        index += 1
    return result


def run_rustc_empty_ok(command, args):
    try:
        return subprocess.run(command + args,
                              capture_output=True,
                              text=True,
                              check=True)
    except FileNotFoundError:
        print(f"Error: rustc command `{command}' not found", file=sys.stderr)
        sys.exit(1)
    except subprocess.CalledProcessError as e:
        print(f"Error: `{' '.join(command + args)}' failed:\n{e.stderr}",
              file=sys.stderr)
        sys.exit(1)


def host_triple(command):
    for line in run_rustc_empty_ok(command, ["-vV"]).stdout.splitlines():
        if line.startswith("host:"):
            return line.split(":", 1)[1].strip()
    print("Error: rustc -vV has no host: line", file=sys.stderr)
    sys.exit(1)


def print_cfg(command, target):
    output = run_rustc_empty_ok(command,
                                ["--target", target, "--print", "cfg"])
    for line in output.stdout.splitlines():
        line = line.strip()
        if line:
            print(line)


def main():
    parser = argparse.ArgumentParser(
        description="Emit rustc configuration for GN")
    parser.add_argument("--rustc-cmd",
                        required=True,
                        help="rustc command of the toolchain")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--target",
                      help="emit `rustc --print cfg --target <triple>` lines")
    mode.add_argument("--host-triple",
                      action="store_true",
                      help="emit the host target triple")
    args = parser.parse_args()

    command = shlex.split(args.rustc_cmd)
    if not command:
        print("Error: rustc command is empty", file=sys.stderr)
        sys.exit(1)
    command = strip_target(command)

    if args.host_triple:
        print(host_triple(command), end="")
    else:
        print_cfg(command, args.target)


if __name__ == "__main__":
    main()
