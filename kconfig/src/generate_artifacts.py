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
Generate C header file and rustflags file from kconfig
"""

import argparse
import os
import sys
from kconfiglib import Kconfig, BOOL, STRING


def generate_configs(kconfig_path, output_dir, defconfig_files):
    kconf = Kconfig(kconfig_path)
    kconf.disable_override_warnings()
    kconf.disable_redun_warnings()
    if defconfig_files:
        for path in defconfig_files:
            kconf.load_config(path, replace=False)

    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
    kconf.write_config(os.path.join(output_dir, f".config"))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--kconfig", help="Kconfig path")
    parser.add_argument("--board", help="target board")
    parser.add_argument("--build_type", help="target build_type")
    parser.add_argument("--output_dir", help="output dir path")
    parser.add_argument("--defconfig_files", help="defconfig files")
    args = parser.parse_args()
    os.environ["BOARD"] = args.board
    os.environ["KCONFIG_DIR"] = os.path.dirname(args.kconfig)
    # Set KERNEL_SRC_DIR to point to kernel/kernel/src directory
    kconfig_dir = os.path.dirname(args.kconfig)
    kernel_src_dir = os.path.join(
        os.path.dirname(os.path.dirname(kconfig_dir)), "kernel", "src")
    os.environ["KERNEL_SRC_DIR"] = os.path.abspath(kernel_src_dir)
    defconfigs = args.defconfig_files.split(",")
    try:
        generate_configs(args.kconfig, args.output_dir, defconfigs)
    except Exception as e:
        print(f"\n[ERROR] Parse failed: {e}", file=sys.stderr)
        sys.exit(1)
