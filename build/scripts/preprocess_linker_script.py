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
Preprocess a linker script using the C preprocessor.
"""

import sys
import argparse
import os


def preprocess_linker_script(preprocessor, input_file, include_dir,
                             output_file):
    import subprocess
    cmd = [
        preprocessor, '-E', '-x', 'c', '-P', '-I', include_dir, input_file,
        '-o', output_file
    ]
    result = subprocess.run(cmd, check=True)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--preprocessor", help="C preprocessor")
    parser.add_argument("--input", help="Input linker script")
    parser.add_argument("--include_dir",
                        help="Include directory for preprocessing")
    parser.add_argument("--output", help="Output preprocessed linker script")
    args = parser.parse_args()
    try:
        # `autoconf.h` isn't produced until later in the build process,
        # so create an temporary file here to satisfy the `gn gen` phase.
        autoconf_c_header = os.path.join(args.include_dir, "autoconf.h")
        if not os.path.exists(autoconf_c_header):
            with open(autoconf_c_header, 'a'):
                pass
        result = preprocess_linker_script(args.preprocessor, args.input,
                                          args.include_dir, args.output)
        if result.returncode != 0:
            print("Error: Preprocessing failed", file=sys.stderr)
            sys.exit(1)
        print(os.path.abspath(args.output).strip(), end='')
    except Exception as e:
        print(f"Error during preprocessing: {e}")
        sys.exit(1)
