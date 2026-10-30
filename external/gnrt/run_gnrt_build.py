import sys
import os
import argparse
import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description='Build gnrt by Cargo')
    parser.add_argument('-p', '--path', required=True, help='Manifest path')
    parser.add_argument('-o',
                        '--output',
                        required=True,
                        help='Output directory for generated files')
    args = parser.parse_args()
    cargo_toml = Path(args.path) / 'Cargo.toml'
    output = Path(args.output)
    command = [
        "cargo", "build", "--manifest-path", cargo_toml, "--artifact-dir",
        output, "-Z", "unstable-options"
    ]
    try:
        result = subprocess.run(command,
                                check=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
    except subprocess.CalledProcessError as e:
        print(f"Command failed with error {e.returncode}:")
        print(e.stderr.decode())
        sys.exit(1)

    if result.stderr:
        print(result.stderr.decode())


if __name__ == '__main__':
    sys.exit(main())
