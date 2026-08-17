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
    parser.add_argument("--region")
    parser.add_argument("--origin")
    parser.add_argument("--length")
    parser.add_argument("--permissions")
    parser.add_argument("--irom-origin")
    parser.add_argument("--irom-length")
    parser.add_argument("--irom-permissions")
    parser.add_argument("--rodata-origin")
    parser.add_argument("--rodata-length")
    parser.add_argument("--rodata-permissions")
    parser.add_argument("--rwdata-origin")
    parser.add_argument("--rwdata-length")
    parser.add_argument("--rwdata-permissions")
    parser.add_argument("--flash-mmu-page-size")
    parser.add_argument("--linker-script-template", required=True)
    parser.add_argument("--linker-script", required=True)
    return parser.parse_args()


def validate_identifier(value, description):
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", value):
        raise ValueError(f"invalid {description}: {value}")
    return value


def parse_number(value, description):
    try:
        result = int(value, 0)
    except ValueError as error:
        raise ValueError(f"invalid {description}: {value}") from error
    if result <= 0:
        raise ValueError(f"{description} must be positive")
    return result


def validate_permissions(value, description):
    if (
        not value
        or any(permission not in "rwx" for permission in value)
        or len(set(value)) != len(value)
    ):
        raise ValueError(f"{description} must contain unique r, w, or x permissions")
    return value


def write_linker_script(template_path, path, replacements):
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

    unresolved_placeholders = LINKER_SCRIPT_PLACEHOLDER_PATTERN.findall(content)
    if unresolved_placeholders:
        values = ", ".join(sorted(set(unresolved_placeholders)))
        raise ValueError(f"unresolved linker script placeholders: {values}")

    pathlib.Path(path).write_text(content, encoding="utf-8")


def main():
    args = parse_args()
    values = {
        "origin": args.origin,
        "length": args.length,
        "irom_origin": args.irom_origin,
        "irom_length": args.irom_length,
        "rodata_origin": args.rodata_origin,
        "rodata_length": args.rodata_length,
        "rwdata_origin": args.rwdata_origin,
        "rwdata_length": args.rwdata_length,
        "flash_mmu_page_size": args.flash_mmu_page_size,
    }
    values = {name: value for name, value in values.items() if value is not None}
    parsed = {
        name: parse_number(value, name.replace("_", " "))
        for name, value in values.items()
    }
    generic_region = [args.region, args.origin, args.length, args.permissions]
    if any(value is not None for value in generic_region) and any(
        value is None for value in generic_region
    ):
        raise ValueError("incomplete generic region")
    if args.region is not None:
        origin = parsed["origin"]
        length = parsed["length"]
        if origin + length <= origin:
            raise ValueError("generic region address overflow")

    for region in ("irom", "rodata", "rwdata"):
        provided = [
            getattr(args, f"{region}_origin"),
            getattr(args, f"{region}_length"),
            getattr(args, f"{region}_permissions"),
        ]
        if any(value is not None for value in provided) and any(
            value is None for value in provided
        ):
            raise ValueError(f"incomplete {region.replace('_', ' ')} region")
        if provided[0] is None:
            continue
        origin = parsed[f"{region}_origin"]
        length = parsed[f"{region}_length"]
        if origin + length <= origin:
            raise ValueError(f"{region} address overflow")

    replacements = {
        f"@{name.upper()}@": f"0x{value:x}" for name, value in parsed.items()
    }
    if args.region is not None:
        replacements["@REGION@"] = validate_identifier(args.region, "region name")
        replacements["@PERMISSIONS@"] = validate_permissions(
            args.permissions, "generic region permissions"
        )

    for region in ("irom", "rodata", "rwdata"):
        if getattr(args, f"{region}_permissions") is None:
            continue
        permissions = validate_permissions(
            getattr(args, f"{region}_permissions"),
            f"{region.replace('_', ' ')} permissions",
        )
        replacements[f"@{region.upper()}_PERMISSIONS@"] = permissions

    write_linker_script(
        args.linker_script_template,
        args.linker_script,
        replacements,
    )


if __name__ == "__main__":
    main()
