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
import shutil
import logging
import argparse
import subprocess

LOGGER = logging.getLogger(__name__)
LOGGER.setLevel(logging.INFO)


def find_latest_profraw(test_dir):
    """
    Find the latest .profraw file in test directory
    
    Args:
        test_dir: Directory to search for .profraw files
    
    Returns:
        Path to the latest .profraw file, or None if not found
    """
    profraw_files = [f for f in os.listdir(test_dir) if f.endswith('.profraw')]
    if not profraw_files:
        return None

    latest_profraw = max(
        profraw_files,
        key=lambda f: os.path.getmtime(os.path.join(test_dir, f)))
    return os.path.join(test_dir, latest_profraw)


def generate_coverage_report(test_dir, binary_path):
    """
    Generate coverage report using grcov
    
    Args:
        test_dir: Directory containing test files and where to output the report
        binary_path: Path to the binary being tested
    
    Returns:
        0 if successful, -1 if failed
    """
    # Find the latest .profraw file
    profraw_path = find_latest_profraw(test_dir)
    if not profraw_path:
        LOGGER.error(f"No coverage data files found in {test_dir}")
        return -1

    LOGGER.info(
        f"Found latest coverage data file: {os.path.basename(profraw_path)}")

    # Copy the profraw file to a standard location with .profraw extension
    standard_profraw_path = test_dir.rstrip('/') + ".profraw"
    try:
        shutil.copy2(profraw_path, standard_profraw_path)
        LOGGER.info(f"Copied profraw file to {standard_profraw_path}")
    except Exception as e:
        LOGGER.error(f"Failed to copy profraw file: {e}")
        return -1

    # Find llvm-cov path
    llvm_path = None
    try:
        llvm_cov_path = shutil.which("llvm-cov")
        if llvm_cov_path:
            llvm_path = os.path.dirname(llvm_cov_path)
            LOGGER.info(f"Found llvm-cov in PATH: {llvm_path}")
    except Exception as e:
        LOGGER.error(f"Error while searching for llvm-cov in PATH: {e}")
        return -1

    # Run grcov command to generate coverage report
    try:
        grcov_cmd = [
            "grcov", "--llvm-path", llvm_path, profraw_path, "-b",
            os.path.abspath(binary_path), "-s",
            os.path.abspath("../.."), "-t", "html", "-o",
            os.path.join(test_dir, "cov_report")
        ]
        LOGGER.info(
            f"Generating coverage report with command: {' '.join(grcov_cmd)}")
        subprocess.run(grcov_cmd, check=True)
        LOGGER.info("Coverage report generated")
        return 0
    except subprocess.CalledProcessError as e:
        LOGGER.error(f"Failed to generate coverage report: {e}")
        return -1
    except FileNotFoundError:
        LOGGER.error(
            "grcov command not found. Make sure it's installed and in your PATH."
        )
        return -1


def main():
    parser = argparse.ArgumentParser(description='Generate coverage report')
    parser.add_argument('-t',
                        '--test-dir',
                        help='Test directory path',
                        required=True)
    parser.add_argument('-b', '--binary', help='Binary path', required=True)

    args = parser.parse_args()

    return generate_coverage_report(os.path.abspath(args.test_dir),
                                    args.binary)


if __name__ == '__main__':
    sys.exit(main())
