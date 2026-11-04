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
"""Gate: the kernel is written in Rust. C and assembly are not allowed.

The kernel used to carry one C translation unit, LLVM's compiler-rt
`libatomic` fallback, because 32-bit targets have no native 64-bit CAS. That
file is now `kernel/kernel/src/sync/libatomic.rs`, so the kernel tree has no C
left.

This gate keeps it that way. It is a hard rule, not a preference: every new
`.c` / `.cc` / `.S` file under `kernel/` fails the build until it is either
deleted or added to the allowlist below with a written reason.

What is allowed, and why:

  * `kernel/adapter/cmsis/cmsis_header/**.h`
    ARM's CMSIS-RTOS API headers. They describe the ABI of an external
    standard, and bindgen turns them into Rust bindings; they are not kernel
    logic.

  * `kernel/**/link.x`
    Linker scripts. The GNU ld script syntax has no Rust equivalent.

Nothing else. In particular there is no `.S` file: the boot entry point, the
exception vectors and the context switch are all `global_asm!` inside Rust
(`kernel/kernel/src/arch/**`).

Usage:
    python3 tools/kernel_lang_gate.py
    python3 tools/kernel_lang_gate.py --json report/kernel_lang.json
    python3 tools/kernel_lang_gate.py --check report/kernel_lang_baseline.json
"""

import argparse
import json
import os
import re
import sys

# C, C++ and assembly sources are all rejected.
FORBIDDEN_SUFFIXES = (".c", ".cc", ".cpp", ".cxx", ".s", ".S", ".sx")

# Files that describe an external ABI or a linker script rather than kernel
# logic. Each entry needs a reason: an allowlist without a reason is just a
# hole in the rule.
ALLOWLIST = {
    "kernel/adapter/cmsis/cmsis_header/RTOS1/cmsis_os.h":
        "ARM CMSIS-RTOS v1 API header; ABI description consumed by bindgen.",
    "kernel/adapter/cmsis/cmsis_header/RTOS2/cmsis_os2.h":
        "ARM CMSIS-RTOS v2 API header; ABI description consumed by bindgen.",
    "kernel/adapter/cmsis/cmsis_header/RTOS2/os_tick.h":
        "ARM CMSIS-RTOS tick type header; ABI description consumed by bindgen.",
    "kernel/adapter/cmsis/cmsis_header/RTOS2/wrapper.h":
        "CMSIS-RTOS v2 header that includes cmsis_os2.h; ABI description only.",
}

# Linker scripts are data, not code.
LINKER_SCRIPT_RE = re.compile(r"(^|/)link\.x$")


def repo_root() -> str:
    return os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def is_allowed(rel_path: str) -> bool:
    if rel_path in ALLOWLIST:
        return True
    return bool(LINKER_SCRIPT_RE.search(rel_path))


def scan(root: str) -> list:
    """Return the forbidden files under kernel/, sorted by path."""
    kernel_dir = os.path.join(root, "kernel")
    found = []
    if not os.path.isdir(kernel_dir):
        return found
    for dirpath, dirnames, filenames in os.walk(kernel_dir):
        dirnames[:] = sorted(d for d in dirnames if d not in (".git", "build", "legacy"))
        for name in sorted(filenames):
            if not name.endswith(FORBIDDEN_SUFFIXES):
                continue
            abs_path = os.path.join(dirpath, name)
            rel_path = os.path.relpath(abs_path, root).replace(os.sep, "/")
            if is_allowed(rel_path):
                continue
            found.append(rel_path)
    return sorted(found)


def count_rust(root: str) -> int:
    """Count the Rust source files under kernel/."""
    kernel_dir = os.path.join(root, "kernel")
    total = 0
    for dirpath, dirnames, filenames in os.walk(kernel_dir):
        dirnames[:] = sorted(d for d in dirnames if d not in (".git", "build", "legacy"))
        total += sum(1 for f in filenames if f.endswith(".rs"))
    return total


def build_report(root: str) -> dict:
    violations = scan(root)
    return {
        "violations": violations,
        "violation_count": len(violations),
        "rust_file_count": count_rust(root),
        "allowlist": dict(sorted(ALLOWLIST.items())),
    }


def render(report: dict) -> str:
    lines = []
    lines.append("kernel language gate")
    lines.append("=" * 60)
    lines.append(f"Rust source files under kernel/: {report['rust_file_count']}")
    lines.append(f"Forbidden C/assembly files:     {report['violation_count']}")
    if report["violations"]:
        lines.append("")
        lines.append("The kernel is written in Rust. These files must be ported")
        lines.append("or added to ALLOWLIST in tools/kernel_lang_gate.py with a")
        lines.append("written reason:")
        for path in report["violations"]:
            lines.append(f"  - {path}")
    else:
        lines.append("")
        lines.append("OK: no C or assembly sources under kernel/.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", metavar="PATH", help="write the report as JSON")
    parser.add_argument("--check", metavar="PATH",
                        help="compare against a baseline; fail on new violations")
    parser.add_argument("--root", default=repo_root(),
                        help="repository root (default: the parent of tools/)")
    args = parser.parse_args()

    root = os.path.abspath(args.root)
    report = build_report(root)

    if args.json:
        os.makedirs(os.path.dirname(os.path.abspath(args.json)), exist_ok=True)
        with open(args.json, "w", encoding="utf-8") as handle:
            json.dump(report, handle, indent=2, sort_keys=True, ensure_ascii=False)
            handle.write("\n")

    if args.check:
        with open(args.check, encoding="utf-8") as handle:
            baseline = json.load(handle)
        known = set(baseline.get("violations", []))
        current = set(report["violations"])
        new = sorted(current - known)
        if new:
            print(render(report))
            print()
            print(f"FAIL: {len(new)} new C/assembly file(s) under kernel/:")
            for path in new:
                print(f"  - {path}")
            return 1
        print(f"OK: no new C/assembly files under kernel/ "
              f"(baseline {len(known)}, current {len(current)}).")
        return 0

    print(render(report))
    return 1 if report["violations"] else 0


if __name__ == "__main__":
    sys.exit(main())
