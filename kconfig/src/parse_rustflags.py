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


def parse_rustflags(kconfig_path, board, build_type):
    rustflags = []
    kconf = Kconfig(kconfig_path)
    dotconfig = os.path.join(os.path.dirname(kconfig_path), board, build_type,
                             'defconfig')
    if os.path.exists(dotconfig):
        kconf.load_config(dotconfig)
    for sym in kconf.defined_syms:
        if sym.type == BOOL and sym.tri_value == 2:
            rustflags.append(sym.name.lower())
        elif sym.type == STRING and sym.str_value:
            rustflags.append(f'{sym.name.lower()}="{sym.str_value.lower()}"')
    return rustflags


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--kconfig", help="Kconfig dir")
    parser.add_argument("--board", help="target board")
    parser.add_argument("--build_type", help="target build_type")
    args = parser.parse_args()
    os.environ['BOARD'] = args.board
    os.environ['KCONFIG_DIR'] = os.path.dirname(args.kconfig)
    try:
        rustflags = parse_rustflags(args.kconfig, args.board, args.build_type)
        if rustflags:
            for flag in rustflags:
                print(flag)
    except Exception as e:
        print(f"\n[ERROR] Parse failed: {e}", file=sys.stderr)
        sys.exit(1)
