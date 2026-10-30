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

import sys
import os
import argparse

DEFAULT = r"""
exec probe-rs run --chip {chip} {image} --disable-progressbars
"""


def do_gen(config, template, need_log=False):
    out_file = os.path.join(config.out_dir, f'{config.name}-probe.sh')
    logfile = None
    if need_log:
        logfile = os.path.abspath(
            os.path.join(config.out_dir, f'{config.name}-probe.log'))
    chip = config.chip
    with open(out_file, 'w') as f:
        f.write(r"#!/bin/bash")

        if not need_log:
            f.write(template.format(
                chip=chip,
                image=os.path.abspath(config.image)))
        else:
            script = template.format(
                chip=chip,
                image=os.path.abspath(config.image)) + f" --target-output-file {logfile}"
            f.write(script)
    os.chmod(out_file, 0o755)
    print(f'Generated {out_file}')
    

def gen(config):
    do_gen(config, DEFAULT)


def main():
    parser = argparse.ArgumentParser(
        description='Generate probe runner script for BlueOS kernel image')
    parser.add_argument("--chip",
                        help="Specify the chip series",
                        required=True)
    parser.add_argument("--name",
                        help="The id of the output script",
                        required=True)
    parser.add_argument("--out-dir", help="Output directory", required=True)
    parser.add_argument("image", help="Image file path")
    config = parser.parse_args()
    return gen(config)


if __name__ == '__main__':
    sys.exit(main())
