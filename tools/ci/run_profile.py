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
"""Run one central-repository CI build profile."""

import argparse
import shlex
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Sequence

REPO_ROOT = Path(__file__).resolve().parents[2]
BOARDS = (
    "none",
    "qemu_mps2_an385",
    "qemu_mps3_an547",
    "qemu_riscv64",
    "qemu_virt64_aarch64",
    "qemu_riscv32",
    "gd32e507_eval",
    "rk3568",
    "gd32vw553_eval",
    "seeed_xiao_esp32c3",
    "raspberry_pico2_cortexm",
)
BUILD_TYPES = ("debug", "release")

# A profile is made of three ordered stages. `--only` lets callers such as
# tools/bk.sh run a single stage without restating the GN argument rules, so
# there is exactly one place that decides how a profile maps to commands.
STAGES = ("gen", "build", "test")


@dataclass(frozen=True)
class Profile:
    board: str
    build_type: str

    def validate(self) -> None:
        if self.board not in BOARDS:
            raise ValueError(f"unsupported board: {self.board}")
        if self.build_type not in BUILD_TYPES:
            raise ValueError(f"unsupported build type: {self.build_type}")

    @property
    def out_dir(self) -> str:
        return f"out/{self.board}.{self.build_type}"

    @property
    def gn_args(self) -> str:
        args = [
            f'board="{self.board}"',
            f'build_type="{self.build_type}"',
        ]
        return " ".join(args)


def commands_for(profile: Profile,
                 stage: str = "all") -> tuple[tuple[str, ...], ...]:
    """Return the commands that make up a profile run.

    `stage` selects one entry of STAGES; "all" keeps the historical behaviour
    of running gen, build, and test in order.
    """
    profile.validate()
    if stage != "all" and stage not in STAGES:
        raise ValueError(f"unsupported stage: {stage}")
    commands = (
        ("gn", "gen", profile.out_dir, f"--args={profile.gn_args}"),
        ("ninja", "-C", profile.out_dir, "default"),
        ("ninja", "-C", profile.out_dir, "check_all"),
    )
    if stage == "all":
        return commands
    return (commands[STAGES.index(stage)], )


CommandRunner = Callable[..., subprocess.CompletedProcess]


def run_profile(profile: Profile,
                command_runner: CommandRunner = subprocess.run,
                stage: str = "all") -> int:
    """Run a profile and return the first failing command's status."""
    for command in commands_for(profile, stage):
        print(f"+ {shlex.join(command)}", flush=True)
        try:
            result = command_runner(command, cwd=REPO_ROOT, check=False)
        except OSError as error:
            print(f"Unable to run {command[0]}: {error}", file=sys.stderr)
            return 127
        if result.returncode != 0:
            return result.returncode
    return 0


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--board", required=True, choices=BOARDS)
    parser.add_argument("--build-type", required=True, choices=BUILD_TYPES)
    parser.add_argument(
        "--only",
        choices=STAGES,
        default=None,
        help="run a single stage instead of gen + build + test",
    )
    parser.add_argument(
        "--print-commands",
        action="store_true",
        help="print the commands for the selected stage without running them",
    )
    args = parser.parse_args(argv)
    return args


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    profile = Profile(args.board, args.build_type)
    stage = args.only or "all"
    if args.print_commands:
        for command in commands_for(profile, stage):
            print(shlex.join(command))
        return 0
    return run_profile(profile, stage=stage)


if __name__ == "__main__":
    sys.exit(main())
