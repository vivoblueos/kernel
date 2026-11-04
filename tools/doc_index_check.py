#!/usr/bin/env python3
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
"""Consistency checks for the two root Markdown docs.

Why this exists: the same fact used to live in five documents and they drifted
(aarch64 was described three different ways). The root now holds exactly two
documents -- `README.md` for status and structure, `DEFECTS.md` for defects and
roadmap -- and a convention nobody checks is a convention that decays.

Five mechanical checks:

1. Both documents exist and declare their own responsibility on a
   `> **本文件职责**` line, so a future edit has to think about the split.
2. Every `DF-nn` referenced in either document is defined in `DEFECTS.md`,
   either as an open `### DF-nn` heading or as an archive-table row
   (`| DF-nn | ... |`).
3. Ids are unique. Gaps are allowed on purpose: a closed defect collapses to a
   one-line archive row and its number is never reused.
4. The severity summary table in `DEFECTS.md` agrees with its own headings.
5. No reference to a retired root document survives (the three merged away),
   because a dangling link is worse than no link.

Exit code 0 when clean, 1 otherwise, so it can gate a commit.
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DOCS = ("README.md", "DEFECTS.md")
REGISTRY = "DEFECTS.md"
RETIRED = ("PROJECT_INVENTORY.md", "S_MODE_MIGRATION.md", "UPSTREAM_COMPARISON.md")

DEF_RE = re.compile(r"\bDF-(\d{2})\b")
HEADING_RE = re.compile(r"^### (DF-\d{2})\s", re.M)
ARCHIVE_RE = re.compile(r"^\| (DF-\d{2})", re.M)
SEVERITY_HEADING_RE = re.compile(r"^## (P\d) · ")
RESPONSIBILITY_RE = re.compile(r"^> \*\*本文件职责\*\*", re.M)


def read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def defined_defects(text: str) -> list[str]:
    """Open defects (headings) plus closed ones (archive table rows)."""
    return HEADING_RE.findall(text) + ARCHIVE_RE.findall(text)


def severity_counts(text: str) -> dict[str, int]:
    """Count `### DF-nn` headings per `## Pn · ...` section."""
    counts: dict[str, int] = {}
    current = None
    for line in text.splitlines():
        h = SEVERITY_HEADING_RE.match(line)
        if h:
            current = h.group(1)
            counts.setdefault(current, 0)
            continue
        if HEADING_RE.match(line) and current:
            counts[current] += 1
    return counts


def check_summary_table(registry: str, counts: dict[str, int], errors: list[str]) -> None:
    table = re.search(r"^\| 级别 \|.*?条数.*?\|$(?P<body>.*?)^\S", registry, re.S | re.M)
    if not table:
        errors.append(f"{REGISTRY}: severity summary table not found")
        return
    for line in table.group("body").splitlines():
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 3:
            continue
        m = re.match(r"\*\*(P\d)", cells[0])
        if not m or not cells[2].isdigit():
            continue
        level, declared = m.group(1), int(cells[2])
        actual = counts.get(level, 0)
        if declared != actual:
            errors.append(
                f"{REGISTRY}: summary says {level} has {declared} entries, body has {actual}"
            )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=ROOT)
    args = ap.parse_args()

    errors: list[str] = []
    texts: dict[str, str] = {}

    for name in DOCS:
        path = args.root / name
        if not path.is_file():
            errors.append(f"{name}: missing")
            continue
        texts[name] = read(path)
        if not RESPONSIBILITY_RE.search(texts[name]):
            errors.append(f"{name}: no '> **本文件职责**' declaration")

    if REGISTRY not in texts or "README.md" not in texts:
        for e in errors:
            print(f"FAIL {e}")
        return 1

    registry = texts[REGISTRY]
    defined = defined_defects(registry)

    for name in DOCS:
        for ref in sorted(set(DEF_RE.findall(texts[name]))):
            if f"DF-{ref}" not in defined:
                errors.append(f"{name}: references DF-{ref}, undefined in {REGISTRY}")

    if len(set(defined)) != len(defined):
        errors.append(f"{REGISTRY}: duplicate defect id")

    check_summary_table(registry, severity_counts(registry), errors)

    for name in DOCS:
        for dead in RETIRED:
            if dead in texts[name]:
                errors.append(f"{name}: references retired document {dead}")

    if errors:
        for e in errors:
            print(f"FAIL {e}")
        print(f"\n{len(errors)} problem(s); {len(defined)} defects registered.")
        return 1

    print(
        f"OK   {len(defined)} defect ids, references resolve, summary table "
        f"matches body, {len(DOCS)} root docs."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
