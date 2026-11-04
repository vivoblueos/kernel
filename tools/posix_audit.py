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
"""Audit POSIX coverage across the kernel, the dispatch table, and librs.

Four layers decide whether a syscall is actually usable:

  L1 declared    the NR enum in kernel/header/src/lib.rs
  L2 dispatched  the syscall_table! entry in syscall_handlers/mod.rs
  L3 implemented the handler body is real logic, not `0` / TODO
  L4 wired       librs really issues the call, instead of returning Ok(())

A record is `real` only when every layer holds. The output is deterministic:
no timestamps, no absolute paths, and every list is sorted, so two consecutive
runs can be diffed byte for byte.

Usage:
    python3 tools/posix_audit.py
    python3 tools/posix_audit.py --json report/posix_coverage.json
    python3 tools/posix_audit.py --check report/posix_baseline.json
"""

import argparse
import json
import os
import re
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

NR_FILE = "kernel/header/src/lib.rs"
TABLE_FILE = "kernel/kernel/src/syscall_handlers/mod.rs"
LIBRS_BACKEND = "librs/src/syscall/blueos/mod.rs"
LIBRS_DIR = "librs/src"
TEST_ROOTS = (
    "kernel/kernel/tests",
    "librs/tests",
    "apps/shell/tests",
)

# NR names whose librs method is not the plain snake_case form.
ALIAS = {
    "FStat": ["fstat"],
    "FStatfs": ["fstatvfs", "fstatfs"],
    "Statfs": ["statfs", "statvfs"],
    "MqTimedSend": ["mq_timedsend"],
    "MqTimedReceive": ["mq_timedreceive"],
    "MqGetSetAttr": ["mq_getsetattr"],
    "RtSigAction": ["sigaction"],
    "SigAltStack": ["sigaltstack"],
    "RtSigPending": ["sigpending"],
    "RtSigProcmask": ["sigprocmask"],
    "RtSigSuspend": ["sigsuspend"],
    "RtSigTimedWait": ["sigtimedwait"],
    "RtSigQueueInfo": ["sigqueue"],
    "GetDents": ["getdents"],
    "Sendto": ["sendto"],
}

# A handler that reports failures must do so through a negative errno, either
# `-(EINVAL as c_long)` or `Err(Errno(...))`. A handler without any error path
# (get_tid, nop) is recorded as errno_ok=false: the field means "has a
# machine-checkable error path", not "is incorrect".
ERRNO_RE = re.compile(r"-\s*\(?\s*(?:libc::)?E[A-Z0-9_]+\s+as\s+c_long"
                      r"|Err\(\s*Errno"
                      r"|-\s*Errno\("
                      r"|-\s*(?:libc::)?E[A-Z0-9_]+\s+as\s+c_long")

# A test "verifies" a syscall only when it actually asserts on the result, not
# merely mentioning the symbol. C cases assert through POSIX_ASSERT /
# POSIX_ASSERT_EQ; Rust tests through assert! / assert_eq!. Compile-time
# `_Static_assert` is excluded on purpose: it checks layout, not behaviour.
ASSERT_RE = re.compile(
    r"POSIX_ASSERT\b|POSIX_ASSERT_EQ\b|assert!\s*\(|assert_eq!\s*\(")

# A `stub` whose constant/zero result *is* the correct POSIX behaviour, not an
# unfinished handler. `Nop` is the only member: it is a no-op syscall that must
# return 0, so `stub` (rather than `real`) is the intended status here.
EXPECTED_STUB = frozenset({"Nop"})

STATUS_RULE = {
    "real": "handler has real logic and librs issues the call",
    "stub": "handler returns a constant, TODO, or -1 without doing work "
            "(Nop's stub is intended: a no-op syscall returns 0)",
    "noop":
    "handler is real but the librs method returns Ok(()) without calling",
    "missing": "not dispatched, no handler, or librs does not expose the call",
}


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def snake(name):
    return re.sub(r"(?<!^)(?=[A-Z])", "_", name).lower()


# ---------------------------------------------------------------- L1/L2
def parse_nr(src):
    m = re.search(r"pub enum NR\s*\{(.*?)\n\s*\}", src, re.S)
    if not m:
        return []
    out = []
    for line in m.group(1).splitlines():
        line = line.split("//")[0].strip().rstrip(",")
        if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", line):
            out.append(line)
    return [name for name in out if name != "LastNR"]


def parse_table(src):
    """Return {NR name: handler module}; the table is the dispatch authority."""
    m = re.search(r"syscall_table!\s*\{(.*?)\n\}", src, re.S)
    if not m:
        return {}
    return {
        nr: mod
        for nr, mod in re.findall(r"\(\s*(\w+)\s*,\s*(\w+)\s*\)", m.group(1))
    }


# ---------------------------------------------------------------- L3
def _match_brace(src, index):
    """Brace matching from src[index] == '{'; returns the closing offset."""
    depth = 0
    while index < len(src):
        char = src[index]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return index
        index += 1
    return -1


def parse_handlers(src):
    """Return {module: {"kind": real|stub, "body": compact, "errno": bool}}."""
    out = {}
    for match in re.finditer(r"define_syscall_handler!\(\s*(\w+)\s*\(", src):
        module = match.group(1)
        brace = src.find("{", match.end())
        if brace < 0:
            continue
        end = _match_brace(src, brace)
        if end < 0:
            continue
        body_raw = src[brace + 1:end]
        body = re.sub(r"//[^\n]*", "", body_raw)
        compact = re.sub(r"\s+", " ", body).strip()
        is_stub = ("TODO" in body_raw or compact in ("0", "-1", "")
                   or re.fullmatch(r"-\s*\d+", compact) is not None)
        out[module] = {
            "kind": "stub" if is_stub else "real",
            "body": compact,
            "errno": bool(ERRNO_RE.search(body)),
        }
    return out


def parse_inline_handlers(src):
    """Return module names of hand-written handlers in the dispatch table.

    Two calls need the trap frame itself rather than the decoded argument
    registers - `fork` (the child resumes with the parent's registers) and
    `execve` (three pointers that must be translated before the kernel looks at
    them) - so they are written as `pub mod <name> { ... fn handle_context ... }`
    instead of going through `define_syscall_handler!`.

    Without this pass they were reported as "kernel: missing": the auditor said
    the kernel had no `fork`, when the kernel side was complete and only the
    librs wrapper was absent. That is the worst kind of wrong answer here,
    because it points the next reader at writing a second handler.
    """
    found = set()
    for match in re.finditer(r"\npub mod (\w+)\s*\{", src):
        brace = src.find("{", match.end() - 1)
        if brace < 0:
            continue
        end = _match_brace(src, brace)
        if end < 0:
            continue
        if "fn handle_context" in src[brace:end]:
            found.add(match.group(1))
    return found


# ---------------------------------------------------------------- L4
def parse_backend(src):
    """Return {librs method: real|noop|stub|panic|other}."""
    out = {}
    starts = [
        match.start()
        for match in re.finditer(r"\n\s*(?:pub )?(?:unsafe )?fn \w+", src)
    ]
    for index, start in enumerate(starts):
        end = starts[index + 1] if index + 1 < len(starts) else len(src)
        segment = src[start:end]
        name_match = re.search(r"fn (\w+)", segment)
        if not name_match:
            continue
        brace = segment.find("{")
        if brace < 0:
            continue
        body = re.sub(r"//[^\n]*", "", segment[brace + 1:])
        compact = re.sub(r"\s+", " ", body).strip()
        if "todo!()" in compact or "unimplemented!()" in compact:
            kind = "panic"
        elif compact.startswith("Ok(())"):
            kind = "noop"
        elif compact.startswith("Err(Errno(-1))"):
            kind = "stub"
        elif "bk_syscall!" in compact or "to_result(" in compact:
            kind = "real"
        else:
            kind = "other"
        out[name_match.group(1)] = kind
    return out


def scan_bk_syscall(root):
    """Return the NR names issued through bk_syscall! anywhere in librs."""
    used = set()
    for dirpath, _, files in os.walk(root):
        for filename in sorted(files):
            if not filename.endswith(".rs"):
                continue
            src = read(os.path.join(dirpath, filename))
            used.update(re.findall(r"bk_syscall!\s*\(\s*(?:NR::)?(\w+)", src))
    return used


def scan_tests(repo):
    """Return {NR name: {"files": [...], "verified": bool}}.

    `files` lists the test translation units that exercise the NR; `verified`
    is true only when at least one of them actually asserts on the result
    (POSIX_ASSERT for C cases, assert!/assert_eq! for Rust tests). A file that
    merely mentions the symbol without checking behaviour keeps `verified`
    false, so the audit can tell "touched" apart from "checked".
    """
    covered = {}
    for relative_root in TEST_ROOTS:
        root = os.path.join(repo, relative_root)
        if not os.path.isdir(root):
            continue
        for dirpath, dirnames, files in os.walk(root):
            dirnames.sort()
            for filename in sorted(files):
                if not filename.endswith(".rs"):
                    continue
                path = os.path.join(dirpath, filename)
                relative = os.path.relpath(path, repo).replace(os.sep, "/")
                src = read(path)
                has_assert = bool(ASSERT_RE.search(src))
                for name in re.findall(r"bk_syscall!\s*\(\s*(?:NR::)?(\w+)",
                                       src):
                    entry = covered.setdefault(
                        name, {"files": set(), "verified": False})
                    entry["files"].add(relative)
                    if has_assert:
                        entry["verified"] = True
    return {name: {"files": sorted(d["files"]), "verified": d["verified"]}
            for name, d in covered.items()}


# ------------------------------------------------------------- inventory
CASE_DIR = "librs/tests/posix/cases"


def count_cases(repo):
    """Inventory of the C conformance cases.

    `files` counts the case translation units and `registered` the
    `POSIX_CASE` entries inside them. Both are compared against the baseline,
    because a deleted case is invisible to the four-layer audit: the cases
    that remain keep their status, so `real` and `tested` do not move while
    the suite shrinks.
    """
    root = os.path.join(repo, CASE_DIR)
    names = []
    if os.path.isdir(root):
        names = sorted(name for name in os.listdir(root)
                       if name.endswith(".c"))
    registered = 0
    for name in names:
        # `POSIX_CASE_XFAIL(...)` registers a case too. Matching only the
        # plain macro silently under-counted the inventory by one (the socket
        # case), so a deliberate deletion of an XFAIL case went unnoticed.
        registered += len(
            re.findall(r"\bPOSIX_CASE(_XFAIL)?\s*\(",
                       read(os.path.join(root, name))))
    return {"files": len(names), "registered": registered, "names": names}


# --------------------------------------------------------------- issue 8
ISSUE8_FILE = "tools/posix_issue8.txt"

# A C symbol reaches the user through one of these shapes in librs. The
# `#[no_mangle] pub extern "C" fn` form is what the C ABI actually needs.
EXPORT_PATTERNS = (
    re.compile(r"#\[no_mangle\][^\n]*\n(?:#\[[^\n]*\]\s*\n)*\s*pub\s+(?:unsafe\s+)?"
               r"extern\s+\"C\"\s+fn\s+(\w+)"),
    re.compile(r"#\[no_mangle\][^\n]*\n(?:#\[[^\n]*\]\s*\n)*\s*pub\s+"
               r"(?:unsafe\s+)?extern\s+\"C\"\s+fn\s+(\w+)"),
)


def parse_issue8(path):
    """Read the Issue 8 delta list: [(header, symbol, tier), ...]."""
    entries = []
    if not os.path.exists(path):
        return entries
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) != 3:
                continue
            entries.append((parts[0], parts[1], parts[2]))
    return entries


def scan_exported_symbols(root):
    """Return the set of C symbols librs exports with #[no_mangle]."""
    exported = set()
    for dirpath, dirnames, files in os.walk(root):
        dirnames.sort()
        for filename in sorted(files):
            if not filename.endswith(".rs"):
                continue
            src = read(os.path.join(dirpath, filename))
            for pattern in EXPORT_PATTERNS:
                exported.update(pattern.findall(src))
    return exported


def audit_issue8(repo):
    """Report Issue 8 coverage: is the symbol exported, is it covered."""
    entries = parse_issue8(os.path.join(repo, ISSUE8_FILE))
    if not entries:
        return None

    exported = scan_exported_symbols(os.path.join(repo, LIBRS_DIR))
    cases = scan_issue8_cases(os.path.join(repo, "librs/tests/posix"))

    records = []
    for header, symbol, tier in entries:
        case_entry = cases.get(symbol, {})
        records.append({
            "header": header,
            "symbol": symbol,
            "tier": tier,
            "exported": symbol in exported,
            "case": case_entry.get("files", []),
            "verified": case_entry.get("verified", False),
        })

    summary = {"total": len(records)}
    for tier in ("required", "optional", "deferred"):
        subset = [r for r in records if r["tier"] == tier]
        summary[tier] = len(subset)
        summary[f"{tier}_exported"] = sum(1 for r in subset if r["exported"])
        summary[f"{tier}_covered"] = sum(
            1 for r in subset if r["exported"] and r["case"])
    summary["required_ratio"] = (
        round(summary["required_exported"] / summary["required"], 4)
        if summary["required"] else 0.0)
    return {"summary": summary, "interfaces": records}


def scan_issue8_cases(root):
    """Return {symbol: {"files": [...], "verified": bool}} for C cases.

    `verified` is true only when the symbol's case file contains a real
    behaviour assertion (POSIX_ASSERT / POSIX_ASSERT_EQ), not just a mention.
    """
    covered = {}
    if not os.path.isdir(root):
        return covered
    for dirpath, dirnames, files in os.walk(root):
        dirnames.sort()
        for filename in sorted(files):
            if not (filename.endswith(".c") or filename.endswith(".h")):
                continue
            path = os.path.join(dirpath, filename)
            src = read(path)
            has_assert = bool(ASSERT_RE.search(src))
            for symbol in re.findall(r"\b([a-z_][a-z0-9_]*)\s*\(", src):
                entry = covered.setdefault(
                    symbol, {"files": set(), "verified": False})
                entry["files"].add(
                    os.path.relpath(path, root).replace(os.sep, "/"))
                if has_assert:
                    entry["verified"] = True
    return {symbol: {"files": sorted(d["files"]), "verified": d["verified"]}
            for symbol, d in covered.items()}


# ---------------------------------------------------------------- summary
def audit(repo):
    nr_names = parse_nr(read(os.path.join(repo, NR_FILE)))
    table_src = read(os.path.join(repo, TABLE_FILE))
    table = parse_table(table_src)
    handlers = parse_handlers(table_src)
    inline = parse_inline_handlers(table_src)

    # A few handlers live in their own file instead of the mod.rs above.
    handler_dir = os.path.dirname(os.path.join(repo, TABLE_FILE))
    for extra in ("echo.rs", ):
        path = os.path.join(handler_dir, extra)
        if os.path.exists(path):
            handlers.update(parse_handlers(read(path)))

    backend = parse_backend(read(os.path.join(repo, LIBRS_BACKEND)))
    wired = scan_bk_syscall(os.path.join(repo, LIBRS_DIR))
    tests = scan_tests(repo)

    normalized = {}
    for name in sorted(backend):
        normalized.setdefault(name.replace("_", "").lower(), name)

    records = []
    for name in nr_names:
        module = table.get(name)
        handler = handlers.get(module) if module else None

        if module is None:
            kernel_impl = "missing"
        elif handler is not None:
            kernel_impl = handler["kind"]
        elif module in inline or os.path.exists(
                os.path.join(handler_dir, module + ".rs")):
            # Hand-written (needs the trap frame) or in its own file.
            kernel_impl = "real"
        else:
            kernel_impl = "missing"

        candidates = ALIAS.get(name, []) + [snake(name)]
        backend_name = next((c for c in candidates if c in backend), None)
        if backend_name is None:
            backend_name = normalized.get(name.lower(), "")
        backend_kind = backend.get(backend_name, "") if backend_name else ""

        if backend_kind in ("noop", "panic", "stub"):
            librs_kind = backend_kind
        elif backend_kind == "real" or name in wired:
            librs_kind = "real"
        else:
            librs_kind = "missing"

        # `status` collapses the four layers into the single contract value.
        if kernel_impl == "missing":
            status = "missing"
        elif kernel_impl == "stub":
            status = "stub"
        elif librs_kind == "real":
            status = "real"
        elif librs_kind in ("noop", "panic"):
            status = "noop"
        else:
            status = "missing"

        test_entry = tests.get(name, {})
        records.append({
            "nr": name,
            "declared": True,
            "dispatched": name in table,
            "backend": backend_name,
            "status": status,
            "errno_ok": bool(handler and handler["errno"]),
            "test": test_entry.get("files", []),
            "verified": test_entry.get("verified", False),
            "detail": {
                "kernel_impl": kernel_impl,
                "librs_kind": librs_kind,
                "handler": module or "",
                "expected_stub": name in EXPECTED_STUB,
            },
        })

    counted = {
        status: sum(1 for record in records if record["status"] == status)
        for status in ("real", "stub", "noop", "missing")
    }
    summary = {
        "declared": len(records),
        "dispatched": sum(1 for record in records if record["dispatched"]),
        **counted,
        "errno_ok": sum(1 for record in records if record["errno_ok"]),
        "tested": sum(1 for record in records if record["test"]),
        "verified": sum(1 for record in records if record["verified"]),
    }
    summary["real_ratio"] = (round(summary["real"] /
                                   summary["declared"], 4) if records else 0.0)
    report = {
        "schema": 2,
        "status_rule": STATUS_RULE,
        "summary": summary,
        "syscalls": records,
    }
    report["cases"] = count_cases(repo)

    issue8 = audit_issue8(repo)
    if issue8 is not None:
        report["issue8"] = issue8
    return report


LABEL = {
    "real": " REAL",
    "stub": " STUB",
    "noop": " NOOP",
    "missing": "MISS ",
}


def print_report(report):
    summary = report["summary"]
    print("BlueKernel POSIX 覆盖度（端到端口径）")
    print(f"  声明 syscall : {summary['declared']}")
    print(f"  已分发       : {summary['dispatched']}")
    print(f"  real         : {summary['real']}")
    print(f"  stub         : {summary['stub']}")
    print(f"  noop         : {summary['noop']}")
    print(f"  missing      : {summary['missing']}")
    print(f"  errno 显式   : {summary['errno_ok']}")
    print(f"  有用例覆盖   : {summary['tested']}")
    print(f"  已验证行为   : {summary['verified']}  "
          f"(覆盖中真正断言了行为的 NR)")
    print(f"  real 占比    : {summary['real_ratio'] * 100:.1f}%")
    print()
    for record in report["syscalls"]:
        stub_mark = " [预期stub]" if record["detail"].get("expected_stub") else ""
        print(f"{LABEL[record['status']]}  {record['nr']:20} "
              f"kernel={record['detail']['kernel_impl']:8} "
              f"librs={record['detail']['librs_kind']:7} "
              f"errno={'y' if record['errno_ok'] else 'n'} "
              f"tests={len(record['test'])} "
              f"verified={'y' if record['verified'] else 'n'}{stub_mark}")

    cases = report.get("cases")
    if cases:
        print()
        print("C 一致性用例清单")
        print(f"  文件数       : {cases['files']}")
        print(f"  注册用例数   : {cases['registered']}")

    issue8 = report.get("issue8")
    if issue8:
        summary = issue8["summary"]
        print()
        print("POSIX.1-2024 (Issue 8) 接口增量")
        print(f"  增量接口总数 : {summary['total']}")
        for tier in ("required", "optional", "deferred"):
            print(f"  {tier:9}   : {summary[tier_exported(tier)]}/{summary[tier]} "
                  f"已导出，有用例 {summary[tier + '_covered']}")
        print(f"  required 占比 : {summary['required_ratio'] * 100:.1f}%")
        print()
        for record in issue8["interfaces"]:
            if record["tier"] != "required":
                continue
            mark = "OK   " if record["exported"] else "MISS "
            print(f"{mark}  {record['symbol']:32} {record['header']:12} "
                  f"case={len(record['case'])} "
                  f"verified={'y' if record['verified'] else 'n'}")


def tier_exported(tier):
    """Summary key holding the exported count for a tier."""
    return f"{tier}_exported"


def check_baseline(report, path):
    """Fail when any frozen number drops below the baseline.

    Three groups are compared, and all are monotonic:

      * syscall coverage - `real` and `tested`;
      * the C case inventory - `cases.files` and `cases.registered`, because
        deleting a case file leaves the coverage numbers untouched;
      * Issue 8 - how many of the required interfaces are exported and how
        many have a case.
    """
    with open(path, encoding="utf-8") as f:
        baseline = json.load(f)
    failures = []
    for field in ("real", "tested"):
        expected = baseline.get("summary", {}).get(field)
        actual = report["summary"][field]
        if expected is not None and actual < expected:
            failures.append(f"summary.{field}: {actual} < baseline {expected}")

    for field in ("files", "registered"):
        expected = baseline.get("cases", {}).get(field)
        actual = report.get("cases", {}).get(field)
        if expected is not None and actual is not None and actual < expected:
            failures.append(f"cases.{field}: {actual} < baseline {expected}")

    for field in ("required_exported", "required_covered"):
        expected = baseline.get("issue8", {}).get("summary", {}).get(field)
        actual = report.get("issue8", {}).get("summary", {}).get(field)
        if expected is not None and actual is not None and actual < expected:
            failures.append(f"issue8.{field}: {actual} < baseline {expected}")

    if failures:
        print("基线回归:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        print(
            "只允许单调上升；确需下调请说明理由并更新基线文件。",
            file=sys.stderr,
        )
        return 1
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        default=REPO_ROOT,
        help="仓库根目录，默认取脚本所在仓库",
    )
    parser.add_argument("--json", help="把结果写入该路径")
    parser.add_argument("--quiet", action="store_true", help="不打印逐条结果")
    parser.add_argument(
        "--check",
        metavar="BASELINE",
        help="与基线 JSON 比较，real/tested 下降时以非零码退出",
    )
    args = parser.parse_args()

    report = audit(args.repo)
    if not args.quiet:
        print_report(report)

    if args.json:
        path = os.path.abspath(args.json)
        directory = os.path.dirname(path)
        if directory:
            os.makedirs(directory, exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(report, f, ensure_ascii=False, indent=2, sort_keys=False)
            f.write("\n")
        if not args.quiet:
            print(f"\n写入 {path}")

    if args.check:
        return check_baseline(report, args.check)
    return 0


if __name__ == "__main__":
    sys.exit(main())
