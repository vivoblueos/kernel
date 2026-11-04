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
"""Collect and freeze the kernel baseline described by P0-07.

Runs the `bench` workload inside the guest, keeps the median of the requested
number of samples, merges the static POSIX inventory from tools/posix_audit.py,
and writes report/baseline.json.

Only the swi profile is built. P0-08 removed the direct-call switch, so the
dsc numbers in an existing baseline are historical: they stay in the file as
`dsc` plus `dsc_historical`, but no run can reproduce them.

Must run inside the toolchain image: it needs gn, ninja and qemu-system-aarch64.
"""

import argparse
import json
import os
import statistics
import subprocess
import sys
import time

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPORT_DIR = os.path.join(REPO_ROOT, "report")
BASELINE_PATH = os.path.join(REPORT_DIR, "baseline.json")
AUDIT_SCRIPT = os.path.join(REPO_ROOT, "tools", "posix_audit.py")

# Per-metric keys printed by apps/bench/src/main.rs as `BENCH <key>=<value>`.
NUMERIC_METRICS = ("syscall_roundtrip_ns", "ctx_switch_ns")
RUN_TIMEOUT_SECONDS = 30

# Modes whose samples are preserved from an older baseline but never rebuilt.
HISTORICAL_MODES = ("dsc", )


def tool_version(command):
    try:
        out = subprocess.run(
            command,
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"
    return out.splitlines()[0] if out else "unknown"


def out_dir_for(board, build_type):
    return os.path.join(REPO_ROOT, "out", f"{board}.{build_type}")


def gn_args(board, build_type):
    return f'board="{board}" build_type="{build_type}"'


def build_bench(out_dir, board, build_type):
    args = gn_args(board, build_type)
    subprocess.run(["gn", "gen", out_dir, f"--args={args}"],
                   cwd=REPO_ROOT,
                   check=True)
    subprocess.run(["ninja", "-C", out_dir, "apps/bench:bench_runner"],
                   cwd=REPO_ROOT,
                   check=True)


def parse_bench_log(text):
    """Return (values, unavailable) parsed from `BENCH key=value` lines."""
    values = {}
    unavailable = {}
    for line in text.splitlines():
        if not line.startswith("BENCH "):
            continue
        body = line[len("BENCH "):].strip()
        if "=" not in body:
            continue
        key, raw = body.split("=", 1)
        parts = raw.split()
        if not parts:
            continue
        if parts[0] == "unavailable":
            marker = "reason="
            index = body.find(marker)
            reason = body[index + len(marker):].strip() if index >= 0 else ""
            unavailable[key] = reason or "unspecified"
            continue
        try:
            value = float(parts[0])
        except ValueError:
            continue
        # Integer metrics keep integer medians; throughput keeps decimals.
        values[key] = value if key == "tcp_loopback_mbps" else int(value)
    return values, unavailable


def run_once(out_dir):
    """Run the default runner and return its serial output.

    The `-test` runner script combines `-nographic` with `-serial file:`, which
    makes QEMU refuse the second chardev, so the plain runner (serial on stdio)
    is the one that actually produces output.
    """
    bin_dir = os.path.join(out_dir, "bin")
    script = os.path.join(bin_dir, "bench_runner-qemu.sh")
    if not os.path.exists(script):
        raise SystemExit(f"missing runner script: {script}")

    try:
        result = subprocess.run(
            [script],
            cwd=bin_dir,
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=RUN_TIMEOUT_SECONDS,
        )
        return result.stdout
    except subprocess.TimeoutExpired as expired:
        # The workload prints BENCH-END but the guest keeps running until QEMU
        # is killed, so a timeout is the normal exit path.
        output = expired.stdout or ""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        return output


def median_or_none(samples):
    if not samples:
        return None
    if isinstance(samples[0], float):
        return round(statistics.median(samples), 3)
    return int(statistics.median(samples))


def collect_swi(board, build_type, runs):
    out_dir = out_dir_for(board, build_type)
    print(f"[baseline] building swi in {os.path.relpath(out_dir, REPO_ROOT)}",
          flush=True)
    build_bench(out_dir, board, build_type)

    samples = {key: [] for key in NUMERIC_METRICS}
    unavailable = {}
    for index in range(runs):
        text = run_once(out_dir)
        values, missing = parse_bench_log(text)
        if not values and not missing:
            raise SystemExit(f"swi run {index + 1}: no BENCH lines; the guest "
                             "did not reach the workload")
        for key, value in values.items():
            samples.setdefault(key, []).append(value)
        unavailable.update(missing)
        print(f"[baseline] swi run {index + 1}/{runs}: {values or missing}",
              flush=True)

    return {
        "samples": samples,
        "unavailable": unavailable,
        "out_dir": os.path.relpath(out_dir, REPO_ROOT),
    }


def collect_posix():
    output = os.path.join(REPO_ROOT, "report", "posix_coverage.json")
    subprocess.run([sys.executable, AUDIT_SCRIPT, "--quiet", "--json", output],
                   cwd=REPO_ROOT,
                   check=True)
    with open(output, "r", encoding="utf-8") as handle:
        return json.load(handle)["summary"]


def load_historical(path):
    """Return the per-mode fields that must survive from an earlier baseline.

    The shape mirrors the parts of a measurement entry this script rewrites:
    `{"<metric>": {"dsc": <median>, "samples": {"dsc": [...]}, ...}}`.
    """
    if not os.path.exists(path):
        return {}
    try:
        with open(path, encoding="utf-8") as handle:
            old = json.load(handle)
    except (OSError, json.JSONDecodeError):
        return {}

    historical = {}
    for key, entry in old.get("measurements", {}).items():
        kept = {}
        for mode in HISTORICAL_MODES:
            if mode in entry:
                kept[mode] = entry[mode]
        for field in ("samples", "min", "max"):
            section = entry.get(field, {})
            for mode in HISTORICAL_MODES:
                if mode in section:
                    kept.setdefault(field, {})[mode] = section[mode]
        if kept:
            historical[key] = kept
    return historical


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--board", default="qemu_virt64_aarch64")
    parser.add_argument("--build-type", default="debug")
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--output", default=BASELINE_PATH)
    args = parser.parse_args()

    if args.runs < 1:
        raise SystemExit("--runs must be at least 1")

    historical = load_historical(args.output)
    result = collect_swi(args.board, args.build_type, args.runs)

    measurements = {}
    for key in NUMERIC_METRICS:
        samples = result["samples"].get(key, [])
        entry = {
            "swi": median_or_none(samples),
            "samples": {
                "swi": samples
            },
            "min": {
                "swi": min(samples) if samples else None
            },
            "max": {
                "swi": max(samples) if samples else None
            },
        }
        old = historical.get(key, {})
        dsc = old.get("dsc")
        if dsc is not None:
            entry["dsc"] = dsc
            entry["dsc_historical"] = True
            for field in ("samples", "min", "max"):
                if field in old:
                    entry[field]["dsc"] = old[field]["dsc"]
            if dsc:
                entry["ratio"] = round(entry["swi"] / dsc, 2)
        # QEMU runs on TCG with 8 vCPUs, so a sample can land on a preempted
        # slice. min is the closest estimate of the cost itself, median is what
        # a caller usually sees; both are frozen so a later run can be compared
        # without arguing about which statistic was meant.
        measurements[key] = entry

    tcp = {
        "swi": median_or_none(result["samples"].get("tcp_loopback_mbps", []))
    }
    old_tcp = historical.get("tcp_loopback_mbps", {})
    if old_tcp.get("dsc") is not None:
        tcp["dsc"] = old_tcp["dsc"]
        tcp["dsc_historical"] = True
    if not any(value for value in tcp.values()):
        tcp["status"] = "unavailable"
        tcp["reason"] = result["unavailable"].get("tcp_loopback_mbps",
                                                  "unspecified")
    measurements["tcp_loopback_mbps"] = tcp

    baseline = {
        "schema": 1,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "board": args.board,
        "build_type": args.build_type,
        "modes": ["swi"],
        "runs_per_mode": args.runs,
        "toolchain": {
            "image": os.environ.get("BK_IMAGE",
                                    "ghcr.io/vivoblueos/kernel:latest"),
            "rustc": tool_version(["rustc", "--version"]),
            "qemu": tool_version(["qemu-system-aarch64", "--version"]),
        },
        "measurements": measurements,
        "posix": collect_posix(),
        "notes": {
            "clock_ids":
            ("The toolchain numbers CLOCK_MONOTONIC as 4 while the kernel "
             "accepts 0..=3, so std::time::Instant panics with EINVAL. The "
             "workload times itself through the raw ClockGetTime syscall "
             "instead."),
            "tcp_loopback":
            ("socket bind returns EPROTONOSUPPORT (109) on 127.0.0.1, so "
             "loopback throughput cannot be measured on this build. Recorded "
             "as unavailable rather than dropped; it is one of the v1 gaps "
             "the v2 plan has to close."),
            "context_switch":
            ("Measured as a Mutex/Condvar ping-pong between two threads; one "
             "iteration is two switches (wake the peer, block again)."),
            "dsc_historical":
            ("P0-08 removed the direct-call syscall switch. The dsc numbers were "
             "measured before that change and are kept for the record; they "
             "cannot be reproduced on this tree."),
        },
    }

    os.makedirs(os.path.dirname(args.output), exist_ok=True)
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(baseline, handle, indent=2, ensure_ascii=False)
        handle.write("\n")
    print(f"[baseline] wrote {os.path.relpath(args.output, REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
