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
This script is used to run menuconfig for kernel configuration.
"""

import argparse
import os
import subprocess
import sys


def get_kernel_src_dir(kconfig_path):
    kconfig_dir = os.path.dirname(kconfig_path)
    return os.path.abspath(
        os.path.join(os.path.dirname(os.path.dirname(kconfig_dir)), "kernel",
                     "src"))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--kconfig", required=True)
    parser.add_argument("--board", required=True)
    parser.add_argument("--build_type", required=True)
    parser.add_argument("--config", required=True)
    args = parser.parse_args()

    kconfig_path = os.path.abspath(args.kconfig)
    config_path = os.path.abspath(args.config)

    env = os.environ.copy()
    env["BOARD"] = args.board
    env["KCONFIG_DIR"] = os.path.dirname(kconfig_path)
    env["KERNEL_SRC_DIR"] = get_kernel_src_dir(kconfig_path)
    # menuconfig reads/writes config from this path.
    env["KCONFIG_CONFIG"] = config_path

    os.makedirs(os.path.dirname(config_path), exist_ok=True)

    try:
        subprocess.run([sys.executable, "-m", "menuconfig", kconfig_path],
                       env=env,
                       check=True)
    except subprocess.CalledProcessError as e:
        sys.exit(e.returncode)
