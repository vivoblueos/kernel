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

import argparse
import os
import sys

TEST = r"""
exec {qemu} {semihosting} -M {machine} {qemu_args} {block_args} {net_args} -nographic -serial \
       file:{logfile} -d int,cpu_reset,guest_errors,unimp -D {syslog}
"""

DBG = r"""
exec {qemu} {semihosting} -M {machine} {qemu_args} {block_args} {net_args} -nographic -s -S
"""

DEFAULT = r"""
exec {qemu} {semihosting} -M {machine} {qemu_args} {block_args} {net_args} -nographic
"""


def do_gen(config, template, suffix='', need_log=False):
    out_file = os.path.join(config.out_dir, f'{config.name}-qemu{suffix}.sh')
    logfile = None
    if need_log:
        logfile = os.path.abspath(
            os.path.join(config.out_dir, f'{config.name}-qemu{suffix}.log'))
        syslog = os.path.abspath(
            os.path.join(config.out_dir, f'{config.name}-qemu{suffix}.syslog'))
    machine = config.machine
    with open(out_file, 'w') as f:
        f.write(r"#!/bin/bash")

        # ESP32 image is loaded as flash device instead of "-kernel".
        block_args = f'-drive file={config.image},if=mtd,format=raw'
        if config.block_args:
            block_args += ' ' + config.block_args

        if not need_log:
            f.write(
                template.format(
                    qemu=config.qemu,
                    semihosting='' if not config.semihosting else
                    '-accel tcg -semihosting-config enable=on',
                    machine=machine,
                    qemu_args=''
                    if not config.qemu_args != "" else config.qemu_args,
                    block_args=block_args,
                    net_args='' if not config.net_args else config.net_args))
        else:
            f.write(
                template.format(
                    qemu=config.qemu,
                    machine=machine,
                    semihosting='' if not config.semihosting else
                    '-accel tcg -semihosting-config enable=on',
                    qemu_args=''
                    if config.qemu_args != "" else config.qemu_args,
                    block_args=block_args,
                    net_args='' if not config.net_args else config.net_args,
                    logfile=logfile,
                    syslog=syslog))
    os.chmod(out_file, 0o755)
    print(f'Generated {out_file}')


def gen(config):
    do_gen(config, TEST, suffix='-test', need_log=True)
    do_gen(config, DBG, suffix='-dbg')
    do_gen(config, DEFAULT)


def main():
    parser = argparse.ArgumentParser(
        description='Generate QEMU runner script for BlueOS ESP32 image')
    parser.add_argument("--qemu",
                        help="Executable of QEMU emulator",
                        required=True)
    parser.add_argument("--machine",
                        help="Select emulated machine",
                        required=True)
    parser.add_argument("--name",
                        help="The id of the output script",
                        required=True)
    parser.add_argument("--out_dir", help="Output directory", required=True)
    parser.add_argument("--qemu_args", help="Extra qmeu args", default="")
    parser.add_argument("--block_args",
                        help="Args for block device",
                        default="")
    parser.add_argument("--net_args", help="Network args", default="")
    parser.add_argument("--semihosting",
                        help="Enable semihosting",
                        action='store_true',
                        default=False)
    parser.add_argument("image", help="Image file path")
    config = parser.parse_args()
    return gen(config)


if __name__ == '__main__':
    sys.exit(main())
