#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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
"""Generate standalone Linux syscall enums for AArch64 and RISC-V 64.

Reference: https://github.com/jasonwhite/syscalls/tree/main/syscalls-gen
No third-party Python packages or Linux build tools are required.

Examples:
  python3 build/scripts/gen_linux_syscalls.py --output-dir /tmp/linux-syscalls
  python3 build/scripts/gen_linux_syscalls.py --arch aarch64 \\
      --linux-dir /path/to/linux --output-dir /tmp/linux-syscalls
"""

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import re
import shlex
import shutil
import ssl
import subprocess
import sys
import tempfile
from urllib.error import URLError
from urllib.parse import quote
from urllib.request import urlopen

LINUX_REPO = "https://raw.githubusercontent.com/torvalds/linux"
LINUX_VERSION = "v7.0"

# Match the native 64-bit ABI selections in Linux's architecture Makefiles.
# In v7.0, arch/arm64/tools/syscall_64.tbl is a symlink to scripts/syscall.tbl.
# Use its target directly: raw GitHub downloads return a symlink's path text.
SOURCES = {
    "aarch64": ("scripts/syscall.tbl", ("common", "64", "renameat", "rlimit",
                                        "memfd_secret")),
    "riscv64": ("scripts/syscall.tbl", ("common", "64", "riscv", "rlimit",
                                        "memfd_secret")),
}


@dataclass(frozen=True)
class Syscall:
    number: int
    name: str

    @property
    def variant(self):
        """Return the syscall name as an UpperCamelCase Rust enum variant."""
        return "".join(part[0].upper() + part[1:]
                       for part in self.name.split("_"))


def parse_table(contents, abis, source):
    """Read public syscall names, including reserved/unimplemented entries.

    Optional entry-point and compat columns do not affect syscall numbering.
    Duplicate detection applies after ABI selection: a table can legitimately
    reuse a number for mutually exclusive 32-bit and 64-bit entries.
    """
    numbers = set()
    names = set()
    entries = []
    for line_number, line in enumerate(contents.splitlines(), 1):
        fields = line.split("#", 1)[0].split()
        if not fields:
            continue
        location = f"{source}:{line_number}"
        if len(fields) < 3 or not re.fullmatch(r"[0-9]+", fields[0]):
            raise ValueError(
                f"{location}: expected NUMBER ABI NAME [ENTRY ...]")
        number, abi, name = int(fields[0]), fields[1], fields[2]
        if abi not in abis:
            continue
        if (not re.fullmatch(r"[a-z_][a-z0-9_]*", name)
                or name in {"_", "self", "super", "crate"}):
            raise ValueError(f"{location}: invalid Rust syscall name {name!r}")
        if number > 0xffffffff:
            raise ValueError(f"{location}: syscall number exceeds u32")
        if number in numbers:
            raise ValueError(f"{location}: duplicate syscall number {number}")
        if name in names:
            raise ValueError(f"{location}: duplicate syscall name {name!r}")
        numbers.add(number)
        names.add(name)
        entries.append(Syscall(number, name))
    if not entries:
        raise ValueError(
            f"{source}: no syscalls matched ABIs {', '.join(abis)}")
    return sorted(entries, key=lambda entry: entry.number)


def read_source(path, version, linux_dir):
    if linux_dir is not None:
        return (linux_dir / path).read_text(encoding="utf-8")
    url = f"{LINUX_REPO}/{quote(version, safe='')}/{path}"
    curl = shutil.which("curl")
    if curl is not None:
        response = subprocess.run(
            [
                curl, "--fail", "--silent", "--show-error", "--location",
                "--max-time", "30", "--retry", "5", "--retry-all-errors",
                "--retry-delay", "1", "--retry-max-time", "60", url
            ],
            check=False,
            capture_output=True,
        )
        if response.returncode != 0:
            raise URLError(
                response.stderr.decode("utf-8", errors="replace").strip())
        return response.stdout.decode("utf-8")

    # Some build images use a Python distribution with its own stale CA bundle.
    # Prefer the administrator-maintained system bundle on Linux (while still
    # honoring an explicit SSL_CERT_FILE) so corporate/system trust roots work.
    cafile = os.environ.get("SSL_CERT_FILE")
    if cafile is None:
        cafile = next((candidate for candidate in (
            "/etc/ssl/certs/ca-certificates.crt",
            "/etc/pki/tls/certs/ca-bundle.crt",
            "/etc/ssl/cert.pem",
        ) if Path(candidate).is_file()), None)
    context = ssl.create_default_context(cafile=cafile)
    with urlopen(url, timeout=30, context=context) as response:
        return response.read().decode("utf-8")


def render(arch, entries, version, local):
    path, abis = SOURCES[arch]
    command = [
        "python3", "build/scripts/gen_linux_syscalls.py", "--arch", arch,
        "--linux-version", version, "--output-dir", "<output-dir>"
    ]
    if local:
        command.extend(["--linux-dir", "<linux-dir>"])
    lines = [
        f"//! Linux syscall numbers for `{arch}`.",
        "// Generated by build/scripts/gen_linux_syscalls.py. Do not edit.",
        f"// Requested Linux revision: {version}",
        f"// Source: {path}",
        f"// ABIs: {', '.join(abis)}",
        f"// Regenerate: {shlex.join(command)}",
    ]
    if local:
        lines.append("// Local source revision is supplied by the caller; "
                     "it is not verified.")
    lines.extend([
        "",
        "#[allow(non_camel_case_types)]",
        "#[repr(usize)]",
        "#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]",
        "pub enum LinuxSysno {",
    ])
    lines.extend(f"    {entry.variant} = {entry.number}," for entry in entries)
    lines.extend([
        "}",
        "",
        "impl LinuxSysno {",
        "    /// Decode a known Linux syscall number, preserving gaps in the table.",
        "    pub const fn from_raw(number: usize) -> Option<Self> {",
        "        match number {",
    ])
    lines.extend(f"            {entry.number} => Some(Self::{entry.variant}),"
                 for entry in entries)
    lines.extend([
        "            _ => None,",
        "        }",
        "    }",
        "",
        "    /// Return the original Linux syscall name.",
        "    pub const fn name(self) -> &'static str {",
        "        match self {",
    ])
    lines.extend(f'            Self::{entry.variant} => "{entry.name}",'
                 for entry in entries)
    lines.extend(["        }", "    }", "}", ""])
    return "\n".join(lines)


def write_output(path, contents):
    """Replace each output atomically, only after all inputs have been parsed."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w",
                                         encoding="utf-8",
                                         newline="\n",
                                         dir=path.parent,
                                         prefix=f".{path.name}.",
                                         delete=False) as output:
            temporary = Path(output.name)
            output.write(contents)
        temporary.chmod(0o644)
        os.replace(temporary, path)
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--arch",
                        nargs="+",
                        choices=SOURCES,
                        default=list(SOURCES),
                        help="Architectures to generate (default: both)")
    parser.add_argument("--linux-version",
                        default=LINUX_VERSION,
                        help=f"Linux tag or commit (default: {LINUX_VERSION}; "
                        "metadata only for local sources)")
    parser.add_argument(
        "--linux-dir",
        type=Path,
        help="Read a local Linux source tree instead of downloading")
    parser.add_argument(
        "--output-dir",
        type=Path,
        required=True,
        help="Write standalone <arch>.rs files into this directory")
    args = parser.parse_args(argv)
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._/-]*", args.linux_version):
        parser.error("--linux-version must be a Linux tag or commit reference")
    try:
        outputs = []
        source_cache = {}
        # Validate every selected architecture before replacing existing files.
        for arch in dict.fromkeys(args.arch):
            path, abis = SOURCES[arch]
            if path not in source_cache:
                source_cache[path] = read_source(path, args.linux_version,
                                                 args.linux_dir)
            contents = source_cache[path]
            entries = parse_table(contents, abis, path)
            output = args.output_dir / f"{arch}.rs"
            generated = render(arch, entries, args.linux_version,
                               args.linux_dir is not None)
            outputs.append((output, generated, len(entries)))
        for output, contents, count in outputs:
            write_output(output, contents)
            print(f"Generated {output} ({count} syscalls)")
    except (OSError, URLError, UnicodeError, ValueError) as error:
        print(f"Error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
