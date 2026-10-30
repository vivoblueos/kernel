#!/usr/bin/env python3

import argparse
import subprocess
import sys
import os
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(
        description='Run gnrt vendor and gen commands')
    parser.add_argument('-exe', '--executable', required=True)
    parser.add_argument('-w', '--work-path')
    parser.add_argument('-c', '--cargo-home')

    args = parser.parse_args()

    gnrt_exe = args.executable
    work_dir = args.work_path
    cargo_home = args.cargo_home

    env = os.environ.copy()
    env['CARGO_HOME'] = cargo_home
    if not os.path.exists(gnrt_exe):
        print(f"Error: Executable not found: {gnrt_exe}", file=sys.stderr)
        return 1

    if os.name != 'nt':
        os.chmod(gnrt_exe, 0o755)

    print("\n=== Running 'gnrt vendor' ===")
    try:
        subprocess.run([gnrt_exe, 'vendor'], cwd=work_dir, env=env, check=True)
    except subprocess.CalledProcessError as e:
        print(f"Error: gnrt vendor failed with code {e.returncode}",
              file=sys.stderr)
        return 1

    print("\n=== Running 'gnrt gen' ===")
    try:
        subprocess.run([gnrt_exe, 'gen'], cwd=work_dir, env=env, check=True)
    except subprocess.CalledProcessError as e:
        print(f"Error: gnrt gen failed with code {e.returncode}",
              file=sys.stderr)
        return 1

    print("\n=== Completed successfully ===")
    return 0


if __name__ == '__main__':
    sys.exit(main())
