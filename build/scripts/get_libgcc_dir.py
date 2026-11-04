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

"""Locate the libgcc.a that matches a GCC's target multilib variant.

`gcc -print-libgcc-file-name` returns the generic library, which is the wrong
one when the target is a multilib build: RISC-V toolchains ship one libgcc per
variant (rv64i/lp64, rv32imac/ilp32, ...) and the linker picks the variant
from -march/-mabi, not from the library directory. When the C compiler is
clang - which knows nothing about the multilib layout - the library path has
to be spelled out, or `-lgcc` resolves to nothing.

The script takes the compiler, the -march and the -mabi, and returns the
directory holding the matching libgcc.a.

Usage:
    python3 build/scripts/get_libgcc_dir.py riscv-none-elf-gcc rv64i lp64
"""

import argparse
import os
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("compiler", help="GCC that owns the libgcc")
    parser.add_argument("march", help="target -march, e.g. rv64i")
    parser.add_argument("mabi", help="target -mabi, e.g. lp64")
    args = parser.parse_args()

    try:
        result = subprocess.run([args.compiler, "-print-libgcc-file-name"],
                                capture_output=True,
                                text=True,
                                check=True)
    except FileNotFoundError:
        print(f"Error: compiler '{args.compiler}' not found", file=sys.stderr)
        sys.exit(1)
    except subprocess.CalledProcessError as error:
        print(f"Error: {error}", file=sys.stderr)
        sys.exit(1)

    generic = os.path.abspath(result.stdout.strip())
    # .../lib/gcc/<triple>/<version>/libgcc.a -> .../lib/gcc/<triple>/<version>
    base = os.path.dirname(generic)

    # The multilib variant directory is a sibling of the generic one. An empty
    # march/mabi means the toolchain has no multilib layout, and the generic
    # directory is the answer.
    if args.march and args.mabi:
        variant = os.path.join(base, args.march, args.mabi)
        if os.path.isfile(os.path.join(variant, "libgcc.a")):
            print(variant, end="")
            return 0

    # No multilib layout: the generic library is the only one there is.
    if os.path.isfile(generic):
        print(base, end="")
        return 0

    print(
        f"Error: no libgcc.a for {args.march}/{args.mabi} under {base}",
        file=sys.stderr)
    sys.exit(1)


if __name__ == "__main__":
    sys.exit(main())
