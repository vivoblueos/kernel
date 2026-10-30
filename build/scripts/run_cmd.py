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
import subprocess
import os
import shutil
import logging
import argparse

LOGGER = logging.getLogger(__name__)
LOGGER.setLevel(logging.INFO)


def main():
    parser = argparse.ArgumentParser(
        description='Run command with optional coverage check')
    parser.add_argument('-b', '--bin', help='Test binary path', required=True)
    parser.add_argument('-t',
                        '--test-dir',
                        help='Test directory path',
                        required=False,
                        default=None)

    args = parser.parse_args()

    # Run the command
    if args.test_dir:
        test_dir = os.path.abspath(args.test_dir)
        os.makedirs(test_dir, exist_ok=True)
        return subprocess.call(args.bin, cwd=test_dir, shell=True)
    else:
        return subprocess.call(args.bin, shell=True)


if __name__ == '__main__':
    sys.exit(main())
