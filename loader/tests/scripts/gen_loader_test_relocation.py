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
import pathlib
import re

LINKER_SCRIPT_PLACEHOLDER_PATTERN = re.compile(r"@[A-Z][A-Z0-9_]*@")


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--region", required=True)
    parser.add_argument("--origin", required=True)
    parser.add_argument("--length", required=True)
    parser.add_argument("--permissions", required=True)
    parser.add_argument("--linker-script-template", required=True)
    parser.add_argument("--linker-script", required=True)
    return parser.parse_args()


def validate_identifier(value, description):
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", value):
        raise ValueError(f"invalid {description}: {value}")


def parse_number(value, description):
    try:
        result = int(value, 0)
    except ValueError as error:
        raise ValueError(f"invalid {description}: {value}") from error
    if result <= 0:
        raise ValueError(f"{description} must be positive")
    return result


def write_linker_script(template_path, path, region, origin, length,
                        permissions):
    replacements = {
        "@REGION@": region,
        "@ORIGIN@": f"0x{origin:x}",
        "@LENGTH@": f"0x{length:x}",
        "@PERMISSIONS@": permissions,
    }
    template = pathlib.Path(template_path).read_text(encoding="utf-8")
    placeholders = set(LINKER_SCRIPT_PLACEHOLDER_PATTERN.findall(template))
    expected_placeholders = set(replacements)

    unknown_placeholders = placeholders - expected_placeholders
    if unknown_placeholders:
        values = ", ".join(sorted(unknown_placeholders))
        raise ValueError(f"unknown linker script placeholders: {values}")

    missing_placeholders = expected_placeholders - placeholders
    if missing_placeholders:
        values = ", ".join(sorted(missing_placeholders))
        raise ValueError(f"missing linker script placeholders: {values}")

    content = template
    for placeholder, value in replacements.items():
        content = content.replace(placeholder, value)

    unresolved_placeholders = LINKER_SCRIPT_PLACEHOLDER_PATTERN.findall(
        content)
    if unresolved_placeholders:
        values = ", ".join(sorted(set(unresolved_placeholders)))
        raise ValueError(f"unresolved linker script placeholders: {values}")

    pathlib.Path(path).write_text(content, encoding="utf-8")


def main():
    args = parse_args()
    validate_identifier(args.region, "region name")
    origin = parse_number(args.origin, "origin")
    length = parse_number(args.length, "length")
    if length <= 16:
        raise ValueError("length must be greater than 16 bytes")
    if origin + length <= origin:
        raise ValueError("region address overflow")
    if args.permissions != "rwx":
        raise ValueError(
            "the EXEC loader test region must have rwx permissions")

    write_linker_script(
        args.linker_script_template,
        args.linker_script,
        args.region,
        origin,
        length,
        args.permissions,
    )


if __name__ == "__main__":
    main()
