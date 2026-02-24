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
Parse the int configuration item in Kconfig
Use the value of .config first, if not, use the default value
Generate config for rust build
"""

import sys
from kconfiglib import Kconfig, BOOL, STRING
import os
import argparse
import re

_UNSET_RE = re.compile(r"^# (CONFIG_[A-Za-z0-9_]+) is not set$")


def _normalize_key(key: str) -> str:
    if key.startswith("CONFIG_"):
        key = key[len("CONFIG_") :]
    return key.lower()


def parse_rustflags_from_config(config_path):
    rustflags = []
    with open(config_path, "r", encoding="utf-8") as src:
        for raw_line in src:
            line = raw_line.strip()
            if not line:
                continue
            if _UNSET_RE.match(line):
                continue
            if not line.startswith("CONFIG_") or "=" not in line:
                continue
            key, value = line.split("=", 1)
            key = _normalize_key(key)
            if value == "y":
                rustflags.append(key)
            elif value == "n":
                continue
            elif value == "":
                rustflags.append(f'{key}=""')
            else:
                if value.startswith('"') and value.endswith('"'):
                    rustflags.append(f'{key}="{value[1:-1].lower()}"')
    return rustflags


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", help=".config file path")
    args = parser.parse_args()
    try:
        rustflags = parse_rustflags_from_config(args.config)
        if rustflags:
            for flag in rustflags:
                print(flag)
    except Exception as e:
        print(f"\n[ERROR] Parse failed: {e}", file=sys.stderr)
        sys.exit(1)
