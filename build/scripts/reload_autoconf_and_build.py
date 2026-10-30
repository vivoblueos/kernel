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
This file will build a new gn project from the parent project.
"""

import os
import argparse
from kconfiglib import Kconfig
import subprocess


def reload_kconfig(kconfig_path, autoconf_path, app_conf_path):
    kconf = Kconfig(kconfig_path)
    kconf.load_config(autoconf_path)
    kconf.disable_override_warnings()
    kconf.disable_redun_warnings()
    kconf.load_config(app_conf_path, replace=False)
    kconf.write_config(autoconf_path)


def gen_ninja_workspace(ninja_dir, board, build_type, defconfig_files):
    gn_cmd = ['gn', 'gen', ninja_dir]
    gn_cmd += [
        f'--args=board=\"{board}\" defconfig_files=\"{defconfig_files}\" build_type=\"{build_type}\"'
    ]
    subprocess.run(gn_cmd, check=True)


def build_with_ninja(ninja_dir, target_name):
    ninja_cmd = ['ninja', '-C', ninja_dir, target_name]
    subprocess.run(ninja_cmd, check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--defconfig_files", help="defconfig files")
    parser.add_argument("--board", help="target board")
    parser.add_argument("--build_type", help="build type")
    parser.add_argument("--ninja_dir", help="ninja build directory")
    parser.add_argument("--output_dir", help="output dir path")
    parser.add_argument("target_name", help="ninja target name")
    args = parser.parse_args()

    try:
        gen_ninja_workspace(args.ninja_dir, args.board, args.build_type,
                            args.defconfig_files)
        build_with_ninja(args.ninja_dir, args.target_name)
        target_name = args.target_name[:-len("_pass")]
        bin_file = args.ninja_dir + '/bin/' + args.target_name + '.bin'
        cped_bin_file = args.output_dir + '/' + target_name + '.bin'
        elf_file = args.ninja_dir + '/bin/' + args.target_name
        cped_elf_file = args.output_dir + '/' + target_name
        cp_cmd = ['cp', bin_file, cped_bin_file]
        subprocess.run(cp_cmd, check=True)
        cp_cmd = ['cp', elf_file, cped_elf_file]
        subprocess.run(cp_cmd, check=True)

    except Exception as e:
        print(f"Error reload autoconf and build: {e}")
        exit(1)
