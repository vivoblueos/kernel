#!/usr/bin/env python3

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
"""Resolve the actual rustc executable for GN."""

import argparse
import os
import shutil
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('rustc', help='compiler executable name or path')
    args = parser.parse_args()
    executable = shutil.which(args.rustc)
    if executable is None:
        parser.error(f'compiler not found: {args.rustc}')
    executable = os.path.realpath(executable)
    # Bypass rustup so crate-local toolchain files cannot change the compiler.
    if os.path.basename(executable) == 'rustup':
        try:
            executable = subprocess.check_output(
                [executable, 'which', 'rustc'], text=True).strip()
        except subprocess.CalledProcessError as error:
            sys.exit(error.returncode)
        except OSError as error:
            parser.error(str(error))
    print(os.path.realpath(executable), end='')


if __name__ == '__main__':
    main()
