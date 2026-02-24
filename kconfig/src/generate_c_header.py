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
"""
Generate C header file from .config
"""

import sys
import re
import os
import argparse

_UNSET_RE = re.compile(r"^# (CONFIG_[A-Za-z0-9_]+) is not set$")

def write_autoconf_from_config(config_path, output_headers):
    output_dir = os.path.dirname(output_headers)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
    
    with open(config_path, "r", encoding="utf-8") as src, open(
        output_headers, "w", encoding="utf-8"
    ) as out:
        out.write("/* Automatically generated file; DO NOT EDIT. */\n")
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
                out.write(f"#define {key}\n")
            elif value == "n":
                continue
            elif value == "":
                out.write(f"#define {key} \"\"\n")
            else:
                out.write(f"#define {key} {value}\n")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", help="config file")
    parser.add_argument("--output_headers", help="C header file output path")
    args = parser.parse_args()
    try:
        write_autoconf_from_config(args.config, args.output_headers)
    except Exception as e:
        print(f"\n[ERROR] Parse failed: {e}", file=sys.stderr)
        sys.exit(1)
