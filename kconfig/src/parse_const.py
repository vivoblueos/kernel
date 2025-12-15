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
Generate const value to rust
"""

import sys
from kconfiglib import Kconfig, INT
import os
import argparse


def parse_int_configs(kconfig_path, board, build_type):
    kconf = Kconfig(kconfig_path)
    dotconfig = os.path.join(os.path.dirname(kconfig_path), board, build_type,
                             'defconfig')
    if os.path.exists(dotconfig):
        kconf.load_config(dotconfig)

    configs = {}

    for sym in kconf.defined_syms:
        if sym.orig_type != INT or not sym.visibility:
            continue

        # check depends on
        if sym.direct_dep is not None:
            # Handle both single dependency and tuple of dependencies
            if isinstance(sym.direct_dep, tuple):
                # If it's a tuple, check if any dependency is false
                if any(dep.tri_value == 0 for dep in sym.direct_dep
                       if hasattr(dep, 'tri_value')):
                    continue
            else:
                # If it's a single dependency
                if hasattr(sym.direct_dep,
                           'tri_value') and sym.direct_dep.tri_value == 0:
                    continue

        value = None
        try:
            # 1. The value set in .config is used first
            if sym.str_value:
                value = int(sym.str_value)
            # 2. Try to get a default value (check the default ... if ... condition)
            elif sym.defaults:
                for default, cond in sym.defaults:
                    if cond is None or cond.eval():
                        value = int(default.str_value)
                        break

            if value is not None:
                configs[sym.name.upper()] = value

        except (ValueError, TypeError) as e:
            print(f"[WARN] items {sym.name} value conversion failed: {e}",
                  file=sys.stderr)

    return configs


def generate_rust_const(configs, output):
    rust_code = """
// Automatically generated configuration constants
#![no_std]
#![allow(unused)]
"""
    for name, value in sorted(configs.items()):
        rust_code += f"pub const {name}: usize = {value};\n"
    output_dir = os.path.dirname(output)
    os.makedirs(output_dir, exist_ok=True)
    with open(output, "w") as f:
        f.write(rust_code)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--kconfig", help="Kconfig dir")
    parser.add_argument("--board", help="target board")
    parser.add_argument("--build_type", help="target build_type")
    parser.add_argument("--output", help="Rust file output directory")
    args = parser.parse_args()
    os.environ['BOARD'] = args.board
    os.environ['KCONFIG_DIR'] = os.path.dirname(args.kconfig)
    # Set KERNEL_SRC_DIR to point to kernel/kernel/src directory
    kconfig_dir = os.path.dirname(args.kconfig)
    kernel_src_dir = os.path.join(
        os.path.dirname(os.path.dirname(kconfig_dir)), 'kernel', 'src')
    os.environ['KERNEL_SRC_DIR'] = os.path.abspath(kernel_src_dir)
    try:
        results = parse_int_configs(args.kconfig, args.board, args.build_type)
        if results:
            generate_rust_const(results, args.output)
    except Exception as e:
        print(f"\n[ERROR] Parse failed: {e}", file=sys.stderr)
        sys.exit(1)
