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
"""Tests for tools/posix_audit.py.

Most cases run against a synthetic repository so the expected status of every
record is known by construction. One case additionally audits the real tree to
catch parser drift.
"""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "tools"))

import posix_audit  # noqa: E402

NR_SOURCE = """\
pub enum NR {
    Real,
    Stubby,
    Noopy,
    Unwired,
    LastNR,
}
"""

TABLE_SOURCE = """\
syscall_table! {
    (Real, real),
    (Stubby, stubby),
    (Noopy, noopy),
}

define_syscall_handler!(
real(x: c_long) -> c_long {
    if x < 0 {
        return -(EINVAL as c_long);
    }
    x
});

define_syscall_handler!(
stubby() -> c_long {
    0
});

define_syscall_handler!(
noopy() -> c_long {
    42
});
"""

BACKEND_SOURCE = """\
impl Syscall for Sys {
    unsafe fn real(_x: c_long) -> Result<c_long> {
        to_result(bk_syscall!(Real, _x))
    }

    unsafe fn noopy() -> Result<()> {
        Ok(())
    }
}
"""


def build_fixture(root: Path) -> None:
    files = {
        "kernel/header/src/lib.rs":
        NR_SOURCE,
        "kernel/kernel/src/syscall_handlers/mod.rs":
        TABLE_SOURCE,
        "librs/src/syscall/blueos/mod.rs":
        BACKEND_SOURCE,
        "librs/tests/integration_test/scal.rs":
        "fn t() { bk_syscall!(Real, 1); }\n",
        # Two case files, three registrations: the inventory counts both, and
        # the mismatch between them is what catches a case that was commented
        # out rather than deleted.
        "librs/tests/posix/cases/one.c":
        'POSIX_CASE("one", one);\n',
        "librs/tests/posix/cases/two.c":
        'POSIX_CASE("two", two);\nPOSIX_CASE("three", three);\n',
    }
    for relative, content in files.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")


class FixtureAuditTest(unittest.TestCase):

    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        build_fixture(self.root)
        self.report = posix_audit.audit(str(self.root))

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def record(self, name: str) -> dict:
        for item in self.report["syscalls"]:
            if item["nr"] == name:
                return item
        self.fail(f"{name} missing from report")

    def test_every_declared_nr_is_reported_once(self) -> None:
        names = [item["nr"] for item in self.report["syscalls"]]
        self.assertEqual(names, ["Real", "Stubby", "Noopy", "Unwired"])

    def test_status_classification(self) -> None:
        self.assertEqual(self.record("Real")["status"], "real")
        self.assertEqual(self.record("Stubby")["status"], "stub")
        self.assertEqual(self.record("Noopy")["status"], "noop")
        self.assertEqual(self.record("Unwired")["status"], "missing")

    def test_errno_is_detected_from_the_handler_body(self) -> None:
        self.assertTrue(self.record("Real")["errno_ok"])
        self.assertFalse(self.record("Stubby")["errno_ok"])

    def test_tests_are_attributed_to_the_nr(self) -> None:
        self.assertEqual(
            self.record("Real")["test"],
            ["librs/tests/integration_test/scal.rs"],
        )
        self.assertEqual(self.record("Stubby")["test"], [])

    def test_summary_adds_up(self) -> None:
        summary = self.report["summary"]
        self.assertEqual(summary["declared"], 4)
        self.assertEqual(
            summary["real"] + summary["stub"] + summary["noop"] +
            summary["missing"],
            summary["declared"],
        )

    def test_case_inventory_counts_files_and_registrations(self) -> None:
        cases = self.report["cases"]
        self.assertEqual(cases["files"], 2)
        self.assertEqual(cases["registered"], 3)
        self.assertEqual(cases["names"], ["one.c", "two.c"])

    def test_output_is_deterministic(self) -> None:
        first = json.dumps(posix_audit.audit(str(self.root)), sort_keys=True)
        second = json.dumps(posix_audit.audit(str(self.root)), sort_keys=True)
        self.assertEqual(first, second)


class BaselineTest(unittest.TestCase):

    def test_regression_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build_fixture(root)
            report = posix_audit.audit(str(root))
            baseline = root / "baseline.json"
            baseline.write_text(
                json.dumps({"summary": {
                    "real": 2,
                    "tested": 1
                }}),
                encoding="utf-8",
            )
            self.assertEqual(posix_audit.check_baseline(report, str(baseline)),
                             1)

    def test_equal_or_better_passes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build_fixture(root)
            report = posix_audit.audit(str(root))
            baseline = root / "baseline.json"
            baseline.write_text(
                json.dumps({"summary": {
                    "real": 1,
                    "tested": 1
                }}),
                encoding="utf-8",
            )
            self.assertEqual(posix_audit.check_baseline(report, str(baseline)),
                             0)


    def test_deleted_case_file_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build_fixture(root)
            report = posix_audit.audit(str(root))
            baseline = root / "baseline.json"
            baseline.write_text(
                json.dumps({
                    "summary": {
                        "real": 0,
                        "tested": 0
                    },
                    "cases": {
                        "files": 2,
                        "registered": 3
                    },
                }),
                encoding="utf-8",
            )
            self.assertEqual(posix_audit.check_baseline(report, str(baseline)),
                             0)

            # One case file disappears; the remaining one still classifies
            # exactly as before, so only the inventory can notice.
            (root / "librs/tests/posix/cases/one.c").unlink()
            shrunk = posix_audit.audit(str(root))
            self.assertEqual(posix_audit.check_baseline(shrunk, str(baseline)),
                             1)

    def test_issue8_drop_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build_fixture(root)
            report = posix_audit.audit(str(root))
            report["issue8"] = {
                "summary": {
                    "required_exported": 1,
                    "required_covered": 1
                }
            }
            baseline = root / "baseline.json"
            baseline.write_text(
                json.dumps({
                    "summary": {
                        "real": 0,
                        "tested": 0
                    },
                    "issue8": {
                        "summary": {
                            "required_exported": 2,
                            "required_covered": 2
                        }
                    },
                }),
                encoding="utf-8",
            )
            self.assertEqual(posix_audit.check_baseline(report, str(baseline)),
                             1)


class RealTreeTest(unittest.TestCase):

    def test_repository_parses(self) -> None:
        report = posix_audit.audit(str(REPO_ROOT))
        summary = report["summary"]
        self.assertGreater(summary["declared"], 0)
        self.assertEqual(summary["declared"], len(report["syscalls"]))
        self.assertEqual(
            summary["real"] + summary["stub"] + summary["noop"] +
            summary["missing"],
            summary["declared"],
        )
        # The audit must never crash on files it cannot classify.
        for item in report["syscalls"]:
            self.assertIn(item["status"], ("real", "stub", "noop", "missing"))

    def test_cli_writes_json(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "coverage.json"
            subprocess.run(
                [
                    sys.executable,
                    str(REPO_ROOT / "tools" / "posix_audit.py"),
                    "--quiet",
                    "--json",
                    str(output),
                ],
                check=True,
            )
            data = json.loads(output.read_text(encoding="utf-8"))
            # Schema 2 added the Issue 8 dimension on top of the POSIX.1-2017
            # four-layer audit.
            self.assertEqual(data["schema"], 2)
            self.assertIn("summary", data)


NR_INLINE_SOURCE = """\
pub enum NR {
    Handmade,
    LastNR,
}
"""

TABLE_INLINE_SOURCE = """\
syscall_table! {
    (Handmade, handmade),
}

/// `Handwritten`, not generated: the trap frame is not one of the argument
/// registers.
pub mod handmade {
    use super::*;

    pub fn handle_context(ctx: &Context) -> usize {
        0
    }
}
"""

BACKEND_INLINE_SOURCE = """\
impl Syscall for Sys {
}
"""


class InlineHandlerTest(unittest.TestCase):
    """Hand-written handlers must not be reported as a missing kernel feature.

    `fork` and `execve` need the trap frame itself, so they are `pub mod <name>`
    blocks rather than `define_syscall_handler!` invocations. The auditor used
    to read the absence of the macro as "the kernel does not implement this" -
    which points a reader at writing a second handler instead of at the missing
    librs wrapper.
    """

    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        files = {
            "kernel/header/src/lib.rs": NR_INLINE_SOURCE,
            "kernel/kernel/src/syscall_handlers/mod.rs": TABLE_INLINE_SOURCE,
            "librs/src/syscall/blueos/mod.rs": BACKEND_INLINE_SOURCE,
        }
        for relative, content in files.items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
        self.report = posix_audit.audit(str(self.root))

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def test_handwritten_handler_counts_as_a_kernel_implementation(self) -> None:
        record = self.report["syscalls"][0]
        self.assertEqual(record["nr"], "Handmade")
        self.assertEqual(record["detail"]["kernel_impl"], "real")

    def test_status_still_reports_the_missing_librs_wrapper(self) -> None:
        # The kernel side being real is not the same as the call being usable:
        # without a librs method the end-to-end answer is still "missing".
        self.assertEqual(self.report["syscalls"][0]["status"], "missing")


if __name__ == "__main__":
    unittest.main()