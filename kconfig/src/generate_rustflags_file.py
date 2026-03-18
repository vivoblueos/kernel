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
"""
Generate rustflags file from kconfig
"""

import sys
import re
import os
import argparse

_UNSET_RE = re.compile(r"^# (CONFIG_[A-Za-z0-9_]+) is not set$")


def write_rustflags_from_config(config_path, output_dir):
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)

    rustflags_file = os.path.join(output_dir, f"rustflags.txt")
    with open(config_path, "r",
              encoding="utf-8") as src, open(rustflags_file,
                                             "w",
                                             encoding="utf-8") as out:
        for raw_line in src:
            line = raw_line.strip()
            if not line:
                continue
            if _UNSET_RE.match(line):
                continue
            if not line.startswith("CONFIG_") or "=" not in line:
                continue
            key, value = line.split("=", 1)
            if value == "y":
                out.write(f"--cfg\n")
                key_lower = key[len("CONFIG_"):].lower()
                out.write(f"{key_lower}\n")
            elif value == "n":
                continue
            elif value == "":
                continue
            elif value.startswith('"') and value.endswith('"'):
                out.write(f'--cfg\n')
                key_lower = key[len("CONFIG_"):].lower()
                out.write(f'{key_lower}={value.lower()}\n')
            else:
                continue


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", help="config file")
    parser.add_argument("--output_dir", help="rustflags output dir path")
    args = parser.parse_args()
    try:
        write_rustflags_from_config(args.config, args.output_dir)
    except Exception as e:
        print(f"\n[ERROR] Parse failed: {e}", file=sys.stderr)
        sys.exit(1)
