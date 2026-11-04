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
"""Rewrite aliased_deps with the same bindings used for Rust dependencies."""

import json
from pathlib import Path
import posixpath
import sys


def canonical_label(label, directory, toolchain):
    if "(" in label:
        label, toolchain = label.rsplit("(", 1)
        toolchain = toolchain.removesuffix(")")
    if not label.startswith("//"):
        label = directory + label if label.startswith(
            ":") else directory + "/" + label
    if ":" not in label:
        label += ":" + posixpath.basename(label)
    path, name = label.rsplit(":", 1)
    path = posixpath.normpath(path.removeprefix("//"))
    path = "//" + ("" if path == "." else path)
    return f"{path}:{name}({toolchain})"


def resolve(data):
    if len(data["original_deps"]) != len(data["resolved_deps"]):
        raise ValueError("original and resolved dependency counts differ")
    mappings = {}
    for original, resolved in zip(data["original_deps"],
                                  data["resolved_deps"]):
        original = canonical_label(original, data["directory"],
                                   data["toolchain"])
        resolved = canonical_label(resolved, data["directory"],
                                   data["toolchain"])
        if original in mappings and mappings[original] != resolved:
            raise ValueError(f"ambiguous dependency binding for {original}")
        mappings[original] = resolved
    aliases = {}
    for name, label in data["aliases"].items():
        canonical = canonical_label(label, data["directory"],
                                    data["toolchain"])
        if canonical not in mappings:
            raise ValueError(
                f"alias {name} does not match a dependency: {label}")
        aliases[name] = mappings[canonical]
    return aliases


if __name__ == "__main__":
    data = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    print(json.dumps(resolve(data)))
