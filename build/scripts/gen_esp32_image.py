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

import argparse
import os
import sys
import urllib.parse
import urllib.request

from esptool import arg_auto_chunk_size, arg_auto_int
from esptool.cmds import elf2image, merge_bin

FLASH_FREQ_CHOICES = [
    "80m",
    "60m",
    "48m",
    "40m",
    "30m",
    "26m",
    "24m",
    "20m",
    "16m",
    "15m",
    "12m",
]

FLASH_MODE_CHOICES = ["qio", "qout", "dio", "dout"]

FLASH_SIZE_CHOICES = [
    "256KB",
    "512KB",
    "1MB",
    "2MB",
    "2MB-c1",
    "4MB",
    "4MB-c1",
    "8MB",
    "16MB",
    "32MB",
    "64MB",
    "128MB",
]

FLASH_MMU_PAGE_SIZE_CHOICES = ["64KB", "32KB", "16KB", "8KB"]

FILL_FLASH_SIZE_CHOICES = [
    "256KB",
    "512KB",
    "1MB",
    "2MB",
    "4MB",
    "8MB",
    "16MB",
    "32MB",
    "64MB",
    "128MB",
]


def is_url(value: str) -> bool:
    parsed = urllib.parse.urlparse(value)
    return parsed.scheme in ("http", "https") and bool(parsed.netloc)


def download_if_url(value: str, output_dir: str, default_name: str) -> str:
    if not is_url(value):
        return value
    parsed = urllib.parse.urlparse(value)
    name = os.path.basename(parsed.path) or default_name
    dest_path = os.path.join(output_dir, name)
    os.makedirs(output_dir, exist_ok=True)
    # Download to a per-process temp file then atomically replace dest.
    # Concurrent merge actions share the same dest (same URL basename +
    # same output_dir); urlretrieve writes dest directly and is NOT atomic,
    # so a peer can open() a half-written file and merge garbage into the
    # image. os.replace is an atomic rename on the same filesystem, so
    # readers only ever see a complete old or complete new file.
    tmp_path = f"{dest_path}.{os.getpid()}.tmp"
    try:
        urllib.request.urlretrieve(value, tmp_path)
        os.replace(tmp_path, dest_path)
    except Exception as exc:
        if os.path.exists(tmp_path):
            os.remove(tmp_path)
        raise SystemExit(f"Failed to download {value}: {exc}") from exc
    return dest_path


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="ESP32 image helpers using esptool")
    subparsers = parser.add_subparsers(dest="command")

    elf_parser = subparsers.add_parser("elf2image",
                                       help="Convert ELF file to ESP32 image")
    elf_parser.add_argument("input", help="Input ELF file")
    elf_parser.add_argument(
        "--output",
        "-o",
        help="Output image filename (if omitted, esptool decides)",
        default=None,
    )
    elf_parser.add_argument(
        "--chip",
        help="Target chip (default: esp32)",
        default="esp32",
    )
    elf_parser.add_argument(
        "--flash_freq",
        "-ff",
        help="SPI flash frequency",
        choices=FLASH_FREQ_CHOICES,
        default=os.environ.get("ESPTOOL_FF", None),
    )
    elf_parser.add_argument(
        "--flash_mode",
        "-fm",
        help="SPI flash mode",
        choices=FLASH_MODE_CHOICES,
        default=os.environ.get("ESPTOOL_FM", "qio"),
    )
    elf_parser.add_argument(
        "--flash_size",
        "-fs",
        help="SPI flash size",
        choices=FLASH_SIZE_CHOICES,
        default=os.environ.get("ESPTOOL_FS", "16MB"),
    )
    elf_parser.add_argument(
        "--min-rev",
        "-r",
        help=argparse.SUPPRESS,
        type=int,
        choices=range(256),
        metavar="{0..255}",
        default=0,
    )
    elf_parser.add_argument(
        "--min-rev-full",
        help="Minimal chip revision (major * 100 + minor)",
        type=int,
        choices=range(65536),
        metavar="{0..65535}",
        default=0,
    )
    elf_parser.add_argument(
        "--max-rev-full",
        help="Maximal chip revision (major * 100 + minor)",
        type=int,
        choices=range(65536),
        metavar="{0..65535}",
        default=65535,
    )
    elf_parser.add_argument(
        "--secure-pad",
        action="store_true",
        help="Pad image to 64KB boundary for Secure Boot v1",
    )
    elf_parser.add_argument(
        "--secure-pad-v2",
        action="store_true",
        help="Pad image to 64KB boundary for Secure Boot v2",
    )
    elf_parser.add_argument(
        "--elf-sha256-offset",
        help="Insert ELF SHA256 at specified offset in the image",
        type=arg_auto_int,
        default=None,
    )
    elf_parser.add_argument(
        "--dont-append-digest",
        dest="append_digest",
        help="Do not append SHA256 digest to the image",
        action="store_false",
        default=True,
    )
    elf_parser.add_argument(
        "--use_segments",
        "--use-segments",
        help="Use ELF segments instead of sections",
        action="store_true",
    )
    elf_parser.add_argument(
        "--flash-mmu-page-size",
        help="Flash MMU page size",
        choices=FLASH_MMU_PAGE_SIZE_CHOICES,
    )
    elf_parser.add_argument(
        "--pad-to-size",
        help="Pad final image to this block size (e.g. 64KB)",
        default=None,
    )
    elf_parser.add_argument(
        "--ram-only-header",
        help="Emit a RAM-only header (ROM loads RAM segments only)",
        action="store_true",
        default=None,
    )
    elf_parser.add_argument(
        "--version",
        help="ESP8266-only image version (ignored for ESP32)",
        choices=["1", "2", "3"],
        default="1",
    )
    elf_parser.set_defaults(func=run_elf2image)

    merge_parser = subparsers.add_parser(
        "merge_bin", help="Merge bootloader, partition table and app image")
    merge_parser.add_argument(
        "--bootloader",
        required=True,
        help="Bootloader image path",
    )
    merge_parser.add_argument(
        "--partition_table",
        "--partition-table",
        required=True,
        help="Partition table image path",
    )
    merge_parser.add_argument(
        "--app_image",
        "--app-image",
        required=True,
        help="Application image path",
    )
    merge_parser.add_argument(
        "--output",
        "-o",
        required=True,
        help="Merged output image path",
    )
    merge_parser.add_argument(
        "--chip",
        help="Target chip (default: esp32)",
        default="esp32",
    )
    merge_parser.add_argument(
        "--bootloader_offset",
        "--bootloader-offset",
        type=arg_auto_int,
        default=0,
        help="Bootloader flash offset (default: 0x1000)",
    )
    merge_parser.add_argument(
        "--partition_table_offset",
        "--partition-table-offset",
        type=arg_auto_int,
        default=0x8000,
        help="Partition table flash offset (default: 0x8000)",
    )
    merge_parser.add_argument(
        "--app_offset",
        "--app-offset",
        type=arg_auto_int,
        default=0x10000,
        help="Application flash offset (default: 0x10000)",
    )
    merge_parser.add_argument(
        "--format",
        "-f",
        choices=["raw", "uf2", "hex"],
        default="raw",
        help="Output format",
    )
    merge_parser.add_argument(
        "--chunk-size",
        help="UF2 chunk size",
        type=arg_auto_chunk_size,
        default=None,
    )
    merge_parser.add_argument(
        "--md5-disable",
        action="store_true",
        help="Disable MD5 checksum in UF2 output",
    )
    merge_parser.add_argument(
        "--flash_freq",
        "-ff",
        help="SPI flash frequency",
        choices=["keep"] + FLASH_FREQ_CHOICES,
        default=os.environ.get("ESPTOOL_FF", "keep"),
    )
    merge_parser.add_argument(
        "--flash_mode",
        "-fm",
        help="SPI flash mode",
        choices=["keep"] + FLASH_MODE_CHOICES,
        default=os.environ.get("ESPTOOL_FM", "keep"),
    )
    merge_parser.add_argument(
        "--flash_size",
        "-fs",
        help="SPI flash size",
        choices=["keep"] + FLASH_SIZE_CHOICES,
        default=os.environ.get("ESPTOOL_FS", "keep"),
    )
    merge_parser.add_argument(
        "--target-offset",
        "-t",
        help="Target offset where the output file will be flashed",
        type=arg_auto_int,
        default=0,
    )
    merge_parser.add_argument(
        "--fill-flash-size",
        help="Pad output to this flash size",
        choices=FILL_FLASH_SIZE_CHOICES,
        default="16MB",
    )
    merge_parser.set_defaults(func=run_merge_bin)

    build_image_parser = subparsers.add_parser(
        "build_image",
        help=
        "Build merged ESP32 image from ELF, bootloader and partition table",
    )
    build_image_parser.add_argument("input", help="Input ELF file")
    build_image_parser.add_argument(
        "--output",
        "-o",
        required=True,
        help="Merged output image path",
    )
    build_image_parser.add_argument(
        "--bootloader",
        required=True,
        help="Bootloader image path",
    )
    build_image_parser.add_argument(
        "--partition_table",
        "--partition-table",
        required=True,
        help="Partition table image path",
    )
    build_image_parser.add_argument(
        "--chip",
        help="Target chip (default: esp32)",
        default="esp32",
    )
    build_image_parser.add_argument(
        "--bootloader_offset",
        "--bootloader-offset",
        type=arg_auto_int,
        default=0,
        help="Bootloader flash offset (default: 0)",
    )
    build_image_parser.add_argument(
        "--partition_table_offset",
        "--partition-table-offset",
        type=arg_auto_int,
        default=0x8000,
        help="Partition table flash offset (default: 0x8000)",
    )
    build_image_parser.add_argument(
        "--app_offset",
        "--app-offset",
        type=arg_auto_int,
        default=0x10000,
        help="Application flash offset (default: 0x10000)",
    )
    build_image_parser.add_argument(
        "--format",
        "-f",
        choices=["raw", "uf2", "hex"],
        default="raw",
        help="Output format",
    )
    build_image_parser.add_argument(
        "--chunk-size",
        help="UF2 chunk size",
        type=arg_auto_chunk_size,
        default=None,
    )
    build_image_parser.add_argument(
        "--md5-disable",
        action="store_true",
        help="Disable MD5 checksum in UF2 output",
    )
    build_image_parser.add_argument(
        "--flash_freq",
        "-ff",
        help="SPI flash frequency",
        choices=["keep"] + FLASH_FREQ_CHOICES,
        default=os.environ.get("ESPTOOL_FF", "keep"),
    )
    build_image_parser.add_argument(
        "--flash_mode",
        "-fm",
        help="SPI flash mode",
        choices=["keep"] + FLASH_MODE_CHOICES,
        default=os.environ.get("ESPTOOL_FM", "keep"),
    )
    build_image_parser.add_argument(
        "--flash_size",
        "-fs",
        help="SPI flash size",
        choices=["keep"] + FLASH_SIZE_CHOICES,
        default=os.environ.get("ESPTOOL_FS", "keep"),
    )
    build_image_parser.add_argument(
        "--target-offset",
        "-t",
        help="Target offset where the output file will be flashed",
        type=arg_auto_int,
        default=0,
    )
    build_image_parser.add_argument(
        "--fill-flash-size",
        help="Pad output to this flash size",
        choices=FILL_FLASH_SIZE_CHOICES,
        default="16MB",
    )
    build_image_parser.set_defaults(func=run_build_image)
    return parser


def run_elf2image(args: argparse.Namespace) -> int:
    elf2image(args)
    return 0


def run_merge_bin(args: argparse.Namespace) -> int:
    output_dir = os.path.dirname(os.path.abspath(args.output)) or os.getcwd()
    args.bootloader = download_if_url(args.bootloader, output_dir,
                                      "bootloader.bin")
    args.partition_table = download_if_url(args.partition_table, output_dir,
                                           "partition_table.bin")

    input_pairs = [
        (args.bootloader_offset, args.bootloader),
        (args.partition_table_offset, args.partition_table),
        (args.app_offset, args.app_image),
    ]
    files = []
    try:
        for addr, path in input_pairs:
            files.append((addr, open(path, "rb")))
        merge_args = argparse.Namespace(
            chip=args.chip,
            output=args.output,
            format=args.format,
            chunk_size=args.chunk_size,
            md5_disable=args.md5_disable,
            flash_freq=args.flash_freq,
            flash_mode=args.flash_mode,
            flash_size=args.flash_size,
            target_offset=args.target_offset,
            fill_flash_size=args.fill_flash_size,
            addr_filename=files,
        )
        merge_bin(merge_args)
    finally:
        for _, f in files:
            f.close()
    return 0


def run_build_image(args: argparse.Namespace) -> int:
    output_dir = os.path.dirname(os.path.abspath(args.output)) or os.getcwd()
    os.makedirs(output_dir, exist_ok=True)
    app_image = os.path.join(output_dir,
                             f".{os.path.basename(args.output)}.app.img")
    try:
        elf_args = argparse.Namespace(
            input=args.input,
            output=app_image,
            chip=args.chip,
            flash_freq=os.environ.get("ESPTOOL_FF", None),
            flash_mode=os.environ.get("ESPTOOL_FM", "qio"),
            flash_size=os.environ.get("ESPTOOL_FS", "16MB"),
            min_rev=0,
            min_rev_full=0,
            max_rev_full=65535,
            secure_pad=False,
            secure_pad_v2=False,
            elf_sha256_offset=None,
            append_digest=True,
            use_segments=False,
            flash_mmu_page_size=None,
            pad_to_size=None,
            ram_only_header=None,
            version="1",
        )
        run_elf2image(elf_args)
        merge_args = argparse.Namespace(
            bootloader=args.bootloader,
            partition_table=args.partition_table,
            app_image=app_image,
            output=args.output,
            chip=args.chip,
            bootloader_offset=args.bootloader_offset,
            partition_table_offset=args.partition_table_offset,
            app_offset=args.app_offset,
            format=args.format,
            chunk_size=args.chunk_size,
            md5_disable=args.md5_disable,
            flash_freq=args.flash_freq,
            flash_mode=args.flash_mode,
            flash_size=args.flash_size,
            target_offset=args.target_offset,
            fill_flash_size=args.fill_flash_size,
        )
        return run_merge_bin(merge_args)
    finally:
        if os.path.exists(app_image):
            os.remove(app_image)


def main():
    parser = build_parser()
    argv = sys.argv[1:]
    if not argv:
        parser.print_help()
        return 1
    if argv[0] not in ("elf2image", "merge_bin", "build_image"):
        argv = ["elf2image"] + argv
    args = parser.parse_args(argv)
    if not hasattr(args, "func"):
        parser.print_help()
        return 1
    return args.func(args)


if __name__ == '__main__':
    sys.exit(main())
