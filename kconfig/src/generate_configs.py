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
Parse the configuration item in Kconfig
And generate .config file
"""

import argparse
import os
import sys

from kconfiglib import Kconfig


def generate_configs(kconfig_path, board, build_type, output):
    kconf = Kconfig(kconfig_path)
    defconfig = os.path.join(os.path.dirname(kconfig_path), board, build_type,
                             "defconfig")
    if os.path.exists(defconfig):
        kconf.load_config(defconfig)

    output_dir = os.path.dirname(output)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
    kconf.write_config(output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--kconfig", help="Kconfig dir")
    parser.add_argument("--board", help="target board")
    parser.add_argument("--build_type", help="target build_type")
    parser.add_argument("--output", help=".config output path")
    args = parser.parse_args()
    os.environ["BOARD"] = args.board
    os.environ["KCONFIG_DIR"] = os.path.dirname(args.kconfig)
    # Set KERNEL_SRC_DIR to point to kernel/kernel/src directory
    kconfig_dir = os.path.dirname(args.kconfig)
    kernel_src_dir = os.path.join(
        os.path.dirname(os.path.dirname(kconfig_dir)), "kernel", "src")
    os.environ["KERNEL_SRC_DIR"] = os.path.abspath(kernel_src_dir)

    try:
        generate_configs(args.kconfig, args.board, args.build_type,
                         args.output)
    except Exception as e:
        print(f"\n[ERROR] Parse failed: {e}", file=sys.stderr)
        sys.exit(1)
