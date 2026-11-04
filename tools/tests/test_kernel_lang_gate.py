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
"""Tests for tools/kernel_lang_gate.py.

Most cases run against a synthetic tree so the expected verdict is known by
construction. The last case audits the real tree, so the gate cannot drift away
from the kernel it is supposed to protect.
"""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "tools"))

import kernel_lang_gate  # noqa: E402


def make_tree(files):
    """Create a temporary repository with the given relative paths."""
    root = Path(tempfile.mkdtemp())
    for rel in files:
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("/* synthetic */\n", encoding="utf-8")
    return root


class AllowlistTests(unittest.TestCase):

    def test_cmsis_header_is_allowed(self):
        rel = "kernel/adapter/cmsis/cmsis_header/RTOS2/cmsis_os2.h"
        self.assertTrue(kernel_lang_gate.is_allowed(rel))

    def test_linker_script_is_allowed(self):
        self.assertTrue(
            kernel_lang_gate.is_allowed("kernel/kernel/src/boards/qemu_riscv64/link.x"))

    def test_ordinary_c_file_is_not_allowed(self):
        self.assertFalse(
            kernel_lang_gate.is_allowed("kernel/kernel/src/sync/libatomic/atomic.c"))

    def test_every_allowlist_entry_has_a_reason(self):
        for path, reason in kernel_lang_gate.ALLOWLIST.items():
            self.assertTrue(reason.strip(), f"{path} has no reason in the allowlist")


class ScanTests(unittest.TestCase):

    def test_clean_tree_passes(self):
        root = make_tree([
            "kernel/kernel/src/lib.rs",
            "kernel/kernel/src/arch/aarch64/mod.rs",
            "kernel/adapter/cmsis/cmsis_header/RTOS2/cmsis_os2.h",
            "kernel/kernel/src/boards/qemu_riscv64/link.x",
        ])
        report = kernel_lang_gate.build_report(str(root))
        self.assertEqual(report["violations"], [])
        self.assertEqual(report["violation_count"], 0)
        self.assertEqual(report["rust_file_count"], 2)

    def test_c_file_is_reported(self):
        root = make_tree([
            "kernel/kernel/src/lib.rs",
            "kernel/kernel/src/sync/atomic.c",
        ])
        report = kernel_lang_gate.build_report(str(root))
        self.assertEqual(report["violations"],
                         ["kernel/kernel/src/sync/atomic.c"])

    def test_assembly_is_reported(self):
        root = make_tree([
            "kernel/kernel/src/arch/start.S",
        ])
        report = kernel_lang_gate.build_report(str(root))
        self.assertEqual(report["violations"],
                         ["kernel/kernel/src/arch/start.S"])

    def test_build_and_legacy_directories_are_ignored(self):
        root = make_tree([
            "kernel/kernel/src/lib.rs",
            "kernel/build/generated.c",
            "kernel/legacy/old_board/legacy.c",
        ])
        report = kernel_lang_gate.build_report(str(root))
        self.assertEqual(report["violations"], [])

    def test_violations_are_sorted(self):
        root = make_tree([
            "kernel/z.c",
            "kernel/a.c",
            "kernel/m.c",
        ])
        report = kernel_lang_gate.build_report(str(root))
        self.assertEqual(report["violations"], [
            "kernel/a.c", "kernel/m.c", "kernel/z.c",
        ])


class CommandLineTests(unittest.TestCase):

    def run_gate(self, args, cwd=None):
        return subprocess.run(
            [sys.executable, str(REPO_ROOT / "tools" / "kernel_lang_gate.py")] + args,
            capture_output=True, text=True, cwd=cwd or str(REPO_ROOT))

    def test_exit_code_is_zero_on_the_real_tree(self):
        result = self.run_gate([])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("no C or assembly sources", result.stdout)

    def test_json_report_is_written(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "nested" / "kernel_lang.json"
            result = self.run_gate(["--json", str(out)])
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            data = json.loads(out.read_text(encoding="utf-8"))
            self.assertIn("violations", data)
            self.assertIn("rust_file_count", data)

    def test_check_mode_detects_new_violation(self):
        with tempfile.TemporaryDirectory() as tmp:
            baseline = Path(tmp) / "baseline.json"
            baseline.write_text(json.dumps({"violations": []}), encoding="utf-8")

            root = make_tree([
                "kernel/kernel/src/lib.rs",
                "kernel/kernel/src/sync/atomic.c",
            ])
            report = Path(tmp) / "current.json"
            # Build the current report against the synthetic tree.
            data = kernel_lang_gate.build_report(str(root))
            report.write_text(json.dumps(data), encoding="utf-8")

            # The check compares a baseline against the tree it runs in, so run
            # the tool with --root pointing at the synthetic tree.
            result = subprocess.run(
                [sys.executable, str(REPO_ROOT / "tools" / "kernel_lang_gate.py"),
                 "--root", str(root), "--check", str(baseline)],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("new C/assembly file", result.stdout)


class RealTreeTests(unittest.TestCase):

    def test_real_kernel_has_no_c_or_assembly(self):
        report = kernel_lang_gate.build_report(str(REPO_ROOT))
        self.assertEqual(report["violations"], [],
                         "kernel/ must not contain C or assembly sources")
        self.assertGreater(report["rust_file_count"], 300)


if __name__ == "__main__":
    unittest.main()
