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
"""Tests for tools/bk.sh.

The suite is deliberately toolchain-free: every case either exercises argument
handling or runs a command in dry-run mode. Cross-checking against
run_profile.Profile keeps the two entry points from drifting apart.
"""

import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BK = REPO_ROOT / "tools" / "bk.sh"
sys.path.insert(0, str(REPO_ROOT / "tools" / "ci"))

from run_profile import Profile  # noqa: E402


def run_bk(*args: str,
           env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
    merged = os.environ.copy()
    merged.setdefault("NO_COLOR", "1")
    if env:
        merged.update(env)
    return subprocess.run(
        [str(BK), *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        env=merged,
        check=False,
    )


class HelpTest(unittest.TestCase):

    def test_help_lists_every_command(self) -> None:
        result = run_bk("--help")
        self.assertEqual(result.returncode, 0, result.stderr)
        for command in ("env", "build", "test", "run", "audit", "clean"):
            self.assertIn(command, result.stdout)

    def test_no_command_prints_usage_and_fails(self) -> None:
        result = run_bk()
        self.assertEqual(result.returncode, 2)
        self.assertIn("用法", result.stdout)


class ValidationTest(unittest.TestCase):

    def test_unknown_board_is_rejected(self) -> None:
        result = run_bk("--board", "not_a_board", "env")
        self.assertEqual(result.returncode, 2)
        self.assertIn("profile 非法", result.stderr)

    def test_duplicate_command_is_rejected(self) -> None:
        result = run_bk("build", "test")
        self.assertEqual(result.returncode, 2)
        self.assertIn("只能指定一个命令", result.stderr)


class ProfileConsistencyTest(unittest.TestCase):
    """bk.sh must not invent its own out dir or GN arguments."""

    def test_dry_run_build_forwards_the_profile_unchanged(self) -> None:
        cases = (
            ("qemu_virt64_aarch64", "debug"),
            ("rk3568", "release"),
            ("none", "debug"),
        )
        for board, build_type in cases:
            with self.subTest(board=board, build_type=build_type):
                profile = Profile(board, build_type)
                result = run_bk(
                    "--board",
                    board,
                    "--build-type",
                    build_type,
                    "--container",
                    "never",
                    "--dry-run",
                    "build",
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                commands = [
                    line[2:] for line in result.stdout.splitlines()
                    if line.startswith("+ ")
                ]
                # The language gate runs first: the kernel is written in Rust,
                # so a stray C file must fail before the build starts.
                self.assertEqual(len(commands), 3, commands)
                self.assertIn("tools/kernel_lang_gate.py", commands[0])
                for command, stage in zip(commands[1:], ("gen", "build")):
                    self.assertIn("tools/ci/run_profile.py", command)
                    self.assertIn(f"--board {board}", command)
                    self.assertIn(f"--build-type {build_type}", command)
                    self.assertIn(f"--only {stage}", command)
                # The out dir layout is part of the P0-01 acceptance criteria.
                self.assertEqual(profile.out_dir, f"out/{board}.{build_type}")

    def test_gn_args_are_owned_by_run_profile(self) -> None:
        result = subprocess.run(
            [
                sys.executable,
                "tools/ci/run_profile.py",
                "--board",
                "qemu_virt64_aarch64",
                "--build-type",
                "debug",
                "--only",
                "gen",
                "--print-commands",
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertEqual(
            shlex.split(result.stdout),
            [
                "gn",
                "gen",
                "out/qemu_virt64_aarch64.debug",
                '--args=board="qemu_virt64_aarch64" build_type="debug"',
            ],
        )

    def test_dry_run_test_builds_before_check_all(self) -> None:
        result = run_bk("--container", "never", "--dry-run", "test")
        self.assertEqual(result.returncode, 0, result.stderr)
        stages = [
            line.rsplit("--only ", 1)[-1]
            for line in result.stdout.splitlines()
            if line.startswith("+ ") and "--only " in line
        ]
        self.assertEqual(stages, ["gen", "build", "test"])

    def test_dry_run_needs_no_toolchain(self) -> None:
        # An empty PATH would also hide python3, which the profile parser needs,
        # so only the container decision is exercised here.
        result = run_bk("--container", "never", "--dry-run", "build")
        self.assertEqual(result.returncode, 0, result.stderr)


class ContainerTest(unittest.TestCase):

    def test_never_uses_bare_commands(self) -> None:
        result = run_bk("--container", "never", "--dry-run", "build")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("docker run", result.stdout)

    @unittest.skipUnless(
        shutil.which("docker") or shutil.which("podman"),
        "no container engine available",
    )
    def test_always_prefixes_engine_and_mounts_repo(self) -> None:
        result = run_bk(
            "--container",
            "always",
            "--image",
            "example.invalid/bluekernel:test",
            "--dry-run",
            "build",
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("run --rm --init", result.stdout)
        self.assertIn(f"-v {REPO_ROOT}:/work", result.stdout)
        self.assertIn("example.invalid/bluekernel:test", result.stdout)


class EnvReportTest(unittest.TestCase):

    def test_aarch64_profile_requires_cross_toolchain(self) -> None:
        result = run_bk("--board", "qemu_virt64_aarch64", "env")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("aarch64-none-elf-gcc", result.stdout)

    def test_host_profile_does_not_require_cross_toolchain(self) -> None:
        result = run_bk("--board", "none", "env")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("gn", result.stdout)
        self.assertNotIn("aarch64-none-elf-gcc", result.stdout)

    def test_env_always_returns_a_hint_or_a_verdict(self) -> None:
        # Force the local mode; in auto mode a running container engine makes
        # the hint section unnecessary and it is skipped by design.
        result = run_bk("--container", "never", "env")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(
            "逐条安装指引" in result.stdout or "工具链完整" in result.stdout,
            result.stdout,
        )


class CleanTest(unittest.TestCase):

    def test_clean_dry_run_reports_without_deleting(self) -> None:
        target = REPO_ROOT / "out" / "none.release"
        if target.exists():
            self.skipTest("refusing to touch a pre-existing build directory")
        target.mkdir(parents=True)
        marker = target / "keep"
        marker.write_text("x", encoding="utf-8")
        try:
            result = run_bk("--board", "none", "--build-type", "release",
                            "--dry-run", "clean")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("rm -rf", result.stdout)
            self.assertTrue(marker.exists())
        finally:
            shutil.rmtree(target, ignore_errors=True)

    def test_clean_removes_only_the_selected_profile(self) -> None:
        target = REPO_ROOT / "out" / "none.release"
        sibling = REPO_ROOT / "out" / "none.debug"
        if target.exists():
            self.skipTest("refusing to touch a pre-existing build directory")
        created_sibling = not sibling.exists()
        try:
            target.mkdir(parents=True)
            (target / "marker").write_text("x", encoding="utf-8")
            if created_sibling:
                sibling.mkdir(parents=True, exist_ok=True)
            result = run_bk("--board", "none", "--build-type", "release",
                            "clean")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse(target.exists())
            self.assertTrue(sibling.exists())
        finally:
            shutil.rmtree(target, ignore_errors=True)
            if created_sibling:
                shutil.rmtree(sibling, ignore_errors=True)


class AuditTest(unittest.TestCase):

    def test_audit_runs_in_place(self) -> None:
        result = run_bk("audit", "--quiet")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_audit_forwards_arguments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "coverage.json"
            result = run_bk("audit", "--quiet", "--json", str(output))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(output.exists())


if __name__ == "__main__":
    unittest.main()
