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
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys


def parse_args():
    parser = argparse.ArgumentParser(
        description="Compile a Miri dependency or interpret a Miri test")
    parser.add_argument("--mode", choices=("compile", "test"), required=True)
    parser.add_argument("--miri", required=True)
    parser.add_argument("--sysroot", required=True)
    parser.add_argument("--stamp")
    parser.add_argument("--aux-output", action="append", default=[])
    parser.add_argument("rustc_args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.rustc_args and args.rustc_args[0] == "--":
        args.rustc_args.pop(0)
    return args


def fail(message):
    print(f"Miri GN error: {message}", file=sys.stderr)
    return 1


def main():
    args = parse_args()
    if not args.sysroot:
        return fail(
            "miri_sysroot is empty; set MIRI_SYSROOT before gn gen or pass "
            "miri_sysroot=\"...\" in GN args")
    if not Path(args.sysroot).is_dir():
        return fail(f"Miri sysroot does not exist: {args.sysroot}")
    if shutil.which(args.miri) is None:
        return fail(f"Miri executable was not found: {args.miri}")
    if args.mode == "test" and not args.stamp:
        return fail("--stamp is required in test mode")

    command = [args.miri, "--sysroot", args.sysroot, *args.rustc_args]
    if args.mode == "test":
        command.extend(("--", "--nocapture"))

    env = os.environ.copy()
    if args.mode == "compile":
        env["MIRI_BE_RUSTC"] = "target"
    else:
        env.pop("MIRI_BE_RUSTC", None)

    print(f"Executing command: {shlex.join(command)}", flush=True)
    try:
        result = subprocess.run(command, env=env, check=False)
    except OSError as error:
        return fail(str(error))
    if result.returncode != 0:
        return result.returncode

    if args.mode == "test":
        stamp = Path(args.stamp)
        stamp.parent.mkdir(parents=True, exist_ok=True)
        temporary_stamp = stamp.with_suffix(stamp.suffix + ".tmp")
        temporary_stamp.write_text("Miri test passed\n", encoding="utf-8")
        temporary_stamp.replace(stamp)
    for output_name in args.aux_output:
        output = Path(output_name)
        output.parent.mkdir(parents=True, exist_ok=True)
        output.touch()
    return 0


if __name__ == '__main__':
    sys.exit(main())
