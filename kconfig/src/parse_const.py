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
import argparse
import os


def generate_rust_const(configs, output) -> None:
    rust_code = """
// Automatically generated configuration constants
#![no_std]
#![allow(unused)]
"""
    output_dir = os.path.dirname(output)
    os.makedirs(output_dir, exist_ok=True)
    with open(output, "w") as f, open(configs, "r") as conf_file:
        f.write(rust_code)
        f.write("\r\n")
        f.write(conf_file.read())

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--src", help="Rust src file")
    parser.add_argument("--output", help="Rust file output directory")
    args = parser.parse_args()
    try:
        generate_rust_const(args.src, args.output)
    except Exception as e:
        print(f"\n[ERROR] Parse failed: {e}", file=sys.stderr)
        sys.exit(1) 

