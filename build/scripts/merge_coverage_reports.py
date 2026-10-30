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
import logging
import argparse
import subprocess
import glob
from pathlib import Path

LOGGER = logging.getLogger(__name__)
LOGGER.setLevel(logging.INFO)
handler = logging.StreamHandler()
formatter = logging.Formatter(
    '%(asctime)s - %(name)s - %(levelname)s - %(message)s')
handler.setFormatter(formatter)
LOGGER.addHandler(handler)


def merge_coverage_report(binary_path, cov_data_dir, output_dir):
    """
    Merge coverage data and generate a report using grcov
    
    Args:
        binary_path: Path to the binary being tested
        cov_data_dir: Directory containing coverage data files
        output_dir: Directory to output the merged coverage report
    
    Returns:
        0 if successful, -1 if failed
    """

    # Find llvm-cov path
    llvm_path = None
    try:
        llvm_cov_path = subprocess.check_output(["which",
                                                 "llvm-cov"]).decode().strip()
        if llvm_cov_path:
            llvm_path = os.path.dirname(llvm_cov_path)
            LOGGER.info(f"Found llvm-cov: {llvm_path}")
    except Exception as e:
        LOGGER.error(f"Error while searching for llvm-cov: {e}")
        return -1

    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)

    # Run grcov command to generate merged coverage report
    try:
        grcov_cmd = [
            "grcov", "--llvm-path", llvm_path,
            os.path.abspath(cov_data_dir), "-b",
            os.path.abspath(binary_path), "-s",
            os.path.abspath("../.."), "-t", "html", "-o", output_dir
        ]

        LOGGER.debug(f"Command: {' '.join(grcov_cmd)}")

        subprocess.run(grcov_cmd, check=True)
        LOGGER.info(f"Merged coverage report generated at {output_dir}")
        return 0
    except subprocess.CalledProcessError as e:
        LOGGER.error(f"Failed to generate merged coverage report: {e}")
        return -1
    except FileNotFoundError:
        LOGGER.error(
            "grcov command not found. Make sure it's installed and in your PATH."
        )
        return -1


def main():
    parser = argparse.ArgumentParser(
        description='Merge coverage data and generate report')
    parser.add_argument('-b',
                        '--binary',
                        help='Path to the binary being tested',
                        required=True)
    parser.add_argument('-d',
                        '--cov-data',
                        help='Directory containing coverage data files',
                        required=True)
    parser.add_argument('-o',
                        '--output-dir',
                        help='Directory to output the merged coverage report',
                        default='cov_report')

    args = parser.parse_args()

    return merge_coverage_report(os.path.abspath(args.binary),
                                 os.path.abspath(args.cov_data),
                                 os.path.abspath(args.output_dir))


if __name__ == '__main__':
    sys.exit(main())
