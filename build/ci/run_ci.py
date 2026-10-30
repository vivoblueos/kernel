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
'''
The CI runner should know as less as possible about the internal BlueOS kernel GN.
Only minimal knowledge of the toplevel targets("default", "check", ...)
should be acquired in this CI runner.
Remaining work, like running tests, should be driven by GN rather than this CI runner.
'''

import os
import sys
import re
import subprocess
import shlex
import shutil
import tempfile
import logging
import itertools
import asyncio
import platform
from run_check_fmt import check_format
from run_check_license import check_license
import argparse

# Use these lists to create CI matrix. Done by using itertools.product.
BOARDS = [
    'none',
    'qemu_mps2_an385',
    # 'newlib_mps3_an547',
    'qemu_mps3_an547',
    'qemu_riscv32',
    'qemu_riscv64',
    'qemu_virt64_aarch64',
    'gd32vw553_eval',
    'rk3568',
    'gd32e507_eval',
    'seeed_xiao_esp32c3',
    'esp32c6_devkitc_1',
    'raspberry_pico2_cortexm',
]
BUILD_TYPES = ['release', 'debug']
DIRECT_SYSCALL_HANDLER_FLAGS = [True, False]

LOGGER = logging.getLogger(__name__)
LOGGER.setLevel(logging.INFO)


class Config(object):

    def __init__(self):
        self.build_type = 'release'
        self.board = 'qemu_mps3_an547'
        self.direct_syscall_handler = False

    def set_build_type(self, ty):
        self.build_type = ty
        return self

    def set_board(self, board):
        self.board = board
        return self

    def set_direct_syscall_handler(self, flag):
        self.direct_syscall_handler = flag
        return self


class Runner(object):

    def __init__(self, config):
        self.config = config

    def run(self):
        LOGGER.info(
            f'Building {self.config.build_type} kernel for {self.config.board} with `direct_syscall_handler`[{self.config.direct_syscall_handler}]'
        )
        return self.run_gn_gen_and_ninja()

    def outdir_name(self):
        basename = f'{self.config.board}.{self.config.build_type}'
        if self.config.direct_syscall_handler:
            basename += '.dsc'
        else:
            basename += '.swi'
        return os.path.join('out', basename)

    def make_gn_args_str(self):
        return ' '.join([
            f'board="{self.config.board}"',
            f'build_type="{self.config.build_type}"',
            f"direct_syscall_handler={'true' if self.config.direct_syscall_handler else 'false'}",
        ])

    def run_gn_gen(self):
        args = self.make_gn_args_str()
        cmd = [
            'gn',
            'gen',
            self.outdir_name(),
            f"--args={args}",
        ]
        return subprocess.call(cmd)

    def ninja_default(self):
        cmd = [
            'ninja',
            '-C',
            self.outdir_name(),
            'default',
        ]
        return subprocess.call(cmd)

    def ninja_check(self):
        cmd = [
            'ninja',
            '-C',
            self.outdir_name(),
            'check_all',
        ]
        return subprocess.call(cmd)

    def ninja_test(self):
        cmd = [
            'ninja',
            '-C',
            self.outdir_name(),
            'test',
        ]
        return subprocess.call(cmd)

    def ninja_check_coverage(self):
        cmd = [
            'ninja',
            '-C',
            self.outdir_name(),
            'check_coverage',
        ]
        return subprocess.call(cmd)

    def run_gn_gen_and_ninja(self):
        rc = self.run_gn_gen()
        if rc != 0:
            return rc
        if self.config.build_type == 'coverage':
            return self.ninja_check_coverage()
        rc = self.ninja_default()
        if rc != 0:
            return rc
        return self.ninja_check()


# After running qemu, tty's echo becomes unfunctional. Let's recover it.
def recover_tty_echo():
    subprocess.call(['stty', 'echo'])


def main():
    parser = argparse.ArgumentParser(
        description='Run CI tests for BlueOS kernel')
    parser.add_argument(
        '--build_type',
        choices=['debug', 'release', 'coverage', 'profile'],
        help=
        'Specify build type to test. If not provided, will test all types in BUILD_TYPES'
    )
    parser.add_argument(
        '--board',
        choices=BOARDS,
        help=
        'Specify board to test. If not provided, will test all types in BOARDS'
    )
    parser.add_argument('--setup_only',
                        action='store_true',
                        default=False,
                        help='Setup output directories of boards only')
    parser.add_argument('repo_paths',
                        nargs='*',
                        help='Repository paths to check')

    args = parser.parse_args()
    repo_to_check = args.repo_paths

    try:
        check_format(repo_to_check)
        # stage 2: check license
        check_license(repo_to_check)
    except Exception as e:
        LOGGER.error(f"Formatting check failed: {e}")
        return -1
    try:
        build_types_to_test = [args.build_type
                               ] if args.build_type else BUILD_TYPES
        boards_to_test = [args.board] if args.board else BOARDS
        for profile in itertools.product(build_types_to_test, boards_to_test,
                                         DIRECT_SYSCALL_HANDLER_FLAGS):
            config = Config().set_build_type(profile[0]).set_board(
                profile[1]).set_direct_syscall_handler(profile[2])
            if args.setup_only:
                rc = Runner(config).run_gn_gen()
                if rc != 0:
                    LOGGER.error(f'Failed to setup with {profile}')
                    return rc
                continue
            rc = Runner(config).run()
            if rc != 0:
                LOGGER.error(f'Failed to run with {profile}')
                return rc
        return 0
    finally:
        recover_tty_echo()


if __name__ == '__main__':
    sys.exit(main())
