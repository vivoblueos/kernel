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

import os
import sys
import argparse

TEST = r"""#!/bin/bash
exec {qemu} -cpu {cpu} -d in_asm,exec,strace -D {logfile} {image}
"""

DBG = r"""#!/bin/bash
exec {qemu} -cpu {cpu} -d in_asm,exec,strace -g 1234 {image}
"""

DEFAULT = r"""#!/bin/bash
exec {qemu} -cpu {cpu} {image}
"""


def do_gen(config, template, suffix='', need_log=False):
    out_file = os.path.join(config.out_dir, f'{config.name}-qemu{suffix}.sh')
    logfile = None
    if need_log:
        logfile = os.path.abspath(
            os.path.join(config.out_dir, f'{config.name}-qemu{suffix}.log'))
    cpu = config.cpu
    with open(out_file, 'w') as f:
        if not need_log:
            f.write(
                template.format(qemu=config.qemu,
                                cpu=cpu,
                                image=os.path.abspath(config.image)))
        else:
            f.write(
                template.format(qemu=config.qemu,
                                cpu=cpu,
                                logfile=logfile,
                                image=os.path.abspath(config.image)))
    os.chmod(out_file, 0o755)
    print(f'Generated {out_file}')


def gen(config):
    do_gen(config, TEST, suffix='-test', need_log=True)
    do_gen(config, DBG, suffix='-dbg')
    do_gen(config, DEFAULT)


def main():
    parser = argparse.ArgumentParser(
        description='Generate QEMU runner script for librs')
    parser.add_argument("--qemu",
                        help="Executable of QEMU emulator",
                        required=True)
    parser.add_argument("--cpu", help="Target cpu type", required=True)
    parser.add_argument("--name", help="Id of output scripts", required=True)
    parser.add_argument("--out_dir", help="Output directory", required=True)
    parser.add_argument("image", help="Image file path")
    config = parser.parse_args()
    return gen(config)


if __name__ == '__main__':
    sys.exit(main())
