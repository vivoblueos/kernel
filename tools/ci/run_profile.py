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
SYSCALL_MODES = ("swi", "dsc")


@dataclass(frozen=True)
class Profile:
    board: str
    build_type: str
    syscall_mode: str

    def validate(self) -> None:
        if self.board not in BOARDS:
            raise ValueError(f"unsupported board: {self.board}")
        if self.build_type not in BUILD_TYPES:
            raise ValueError(f"unsupported build type: {self.build_type}")
        if self.syscall_mode not in SYSCALL_MODES:
            raise ValueError(f"unsupported syscall mode: {self.syscall_mode}")
        if self.board == "none" and self.syscall_mode != "swi":
            raise ValueError("the host profile only supports swi mode")

    @property
    def out_dir(self) -> str:
        return f"out/{self.board}.{self.build_type}.{self.syscall_mode}"

    @property
    def gn_args(self) -> str:
        args = [
            f'board="{self.board}"',
            f'build_type="{self.build_type}"',
        ]
        if self.board != "none":
            direct = "true" if self.syscall_mode == "dsc" else "false"
            args.append(f"direct_syscall_handler={direct}")
        return " ".join(args)


def commands_for(profile: Profile) -> tuple[tuple[str, ...], ...]:
    """Return the commands that make up a profile run."""
    profile.validate()
    return (
        ("gn", "gen", profile.out_dir, f"--args={profile.gn_args}"),
        ("ninja", "-C", profile.out_dir, "default"),
        ("ninja", "-C", profile.out_dir, "check_all"),
    )


CommandRunner = Callable[..., subprocess.CompletedProcess]


def run_profile(profile: Profile,
                command_runner: CommandRunner = subprocess.run) -> int:
    """Run a profile and return the first failing command's status."""
    for command in commands_for(profile):
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
    parser.add_argument("--syscall-mode", required=True, choices=SYSCALL_MODES)
    args = parser.parse_args(argv)
    if args.board == "none" and args.syscall_mode != "swi":
        parser.error("the host profile only supports --syscall-mode=swi")
    return args


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    profile = Profile(args.board, args.build_type, args.syscall_mode)
    return run_profile(profile)


if __name__ == "__main__":
    sys.exit(main())
