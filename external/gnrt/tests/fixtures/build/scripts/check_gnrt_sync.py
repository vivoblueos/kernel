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

"""Validate gnrt preparation offline before GN reads the crate index."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


STATE_VERSION = 1
MARKER = ".gnrt-sync-in-progress.json"
DIGEST_CACHE_VERSION = 1
DIGEST_CACHE_NAME = ".gnrt-sync-digest-cache.json"


def file_digest(path):
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(64 * 1024), b""):
            hasher.update(block)
    return hasher.hexdigest()


def file_signature(stat):
    return [
        stat.st_dev,
        stat.st_ino,
        stat.st_size,
        stat.st_mtime_ns,
        stat.st_ctime_ns,
    ]


def cached_file_digest(path, digest_cache, stat=None):
    key = path.as_posix()
    signature = file_signature(stat or path.stat())
    cached = digest_cache["files"].get(key)
    if isinstance(cached, dict) and cached.get("signature") == signature:
        digest = cached.get("sha256")
        if isinstance(digest, str) and len(digest) == 64:
            return digest

    digest = file_digest(path)
    digest_cache["files"][key] = {
        "signature": signature,
        "sha256": digest,
    }
    digest_cache["_dirty"] = True
    return digest


def ignored_name(name):
    return (
        name in (".git", ".gnrt.lock")
        or name.endswith(".build_script_outputs.stamp")
    )


def tree_digest(path, digest_cache):
    entries = []
    pending = [(path, Path())]
    while pending:
        directory, relative_directory = pending.pop()
        with os.scandir(directory) as children:
            for child in children:
                if ignored_name(child.name):
                    continue
                relative_path = relative_directory / child.name
                entry = Path(child.path)
                if child.is_symlink():
                    value = hashlib.sha256(
                        ("symlink:" + os.readlink(entry)).encode()
                    ).hexdigest()
                elif child.is_dir(follow_symlinks=False):
                    pending.append((entry, relative_path))
                    continue
                elif child.is_file(follow_symlinks=False):
                    value = cached_file_digest(
                        entry,
                        digest_cache,
                        child.stat(follow_symlinks=False),
                    )
                else:
                    continue
                entries.append((relative_path.as_posix(), value))
    hasher = hashlib.sha256()
    for name, value in sorted(entries):
        hasher.update(name.encode())
        hasher.update(b"\0")
        hasher.update(value.encode())
        hasher.update(b"\0")
    return hasher.hexdigest()


def resolve_tool(name):
    variable = {"cargo": "GNRT_CARGO_BIN", "gn": "GNRT_GN_BIN"}.get(name)
    executable = os.environ.get(variable, name) if variable else name
    found = shutil.which(executable)
    if not found:
        raise ValueError(f"preparation tool is missing: {name}")
    return Path(found).resolve()


def record_path(root, record):
    return (root / record["path"]).resolve(strict=True)


def check_record(root, record, digest_cache):
    path = record_path(root, record)
    directory = record["kind"] == "directory"
    if directory != path.is_dir():
        raise ValueError(f"preparation input type changed: {record['path']}")
    value = (
        tree_digest(path, digest_cache)
        if directory
        else cached_file_digest(path, digest_cache)
    )
    if value != record["sha256"]:
        raise ValueError(
            f"preparation input or artifact changed: {record['path']}"
        )


def normalize_args(source):
    process = subprocess.run(
        [str(resolve_tool("gn")), "format", "--stdin"],
        input=source,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if process.returncode:
        raise ValueError("cannot normalize GN arguments: " + process.stderr)
    lines = []
    skip_value = False
    for line in process.stdout.splitlines():
        if skip_value:
            skip_value = False
            continue
        if re.match(r"\s*gnrt_mode\s*=", line):
            skip_value = line.strip().endswith("=")
            continue
        lines.append(line)
    return "\n".join(lines) + "\n" if lines else ""


def tracked_inputs(root, state):
    records = list(state.get("inputs", [])) + list(state.get("artifacts", []))
    for request in state.get("requests", []):
        records.extend(request.get("inputs", []))
    records.extend(state.get("tools", {}).values())
    inputs = set()
    for record in records:
        path = Path(record["path"])
        if path.is_absolute():
            continue
        inputs.add(path.as_posix())
        if record.get("kind") == "directory" and (root / path).is_dir():
            for directory, subdirs, files in os.walk(root / path):
                subdirs[:] = [name for name in subdirs if not ignored_name(name)]
                for name in files:
                    if not ignored_name(name):
                        inputs.add(
                            (Path(directory) / name).relative_to(root).as_posix()
                        )
    return sorted(inputs)


def validate(root, state, args_file, digest_cache):
    if state.get("version") != STATE_VERSION:
        raise ValueError("unsupported gnrt preparation state version")
    for record in state["inputs"] + state["artifacts"]:
        check_record(root, record, digest_cache)
    for name, expected in state["environment"].items():
        current = os.environ.get(name)
        if current is not None:
            current = current.replace(str(root), "${GNRT_ROOT}")
        if current != expected:
            raise ValueError(f"preparation environment changed: {name}")
    for name, record in state["tools"].items():
        executable = resolve_tool(name)
        if executable != record_path(root, record):
            raise ValueError(f"preparation tool changed: {name}")
        check_record(root, record, digest_cache)
    if state["complete"]:
        return
    # Scoped records share outputs, so every recorded request must remain valid.
    for request in state["requests"]:
        for record in request["inputs"]:
            check_record(root, record, digest_cache)
    if args_file is None:
        raise ValueError("partial preparation requires the build's args.gn")
    source = args_file.read_text(encoding="utf-8")
    normalized = normalize_args(source)
    for request in state["requests"]:
        if request["args"] != normalized:
            continue
        if not set(request["roots"]).issubset(state["roots"]):
            continue
        return
    raise ValueError("this GN configuration has not been synced")


def load_digest_cache(root, state_digest):
    # Reuse verified hashes across GN output directories for the same sync state.
    cache_path = root / "out" / DIGEST_CACHE_NAME
    try:
        cache = json.loads(cache_path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        cache = None
    if (
        isinstance(cache, dict)
        and cache.get("version") == DIGEST_CACHE_VERSION
        and cache.get("state_sha256") == state_digest
        and isinstance(cache.get("files"), dict)
    ):
        return cache
    return {
        "version": DIGEST_CACHE_VERSION,
        "state_sha256": state_digest,
        "files": {},
        "_dirty": True,
    }


def save_digest_cache(root, digest_cache):
    if not digest_cache.get("_dirty"):
        return
    cache_path = root / "out" / DIGEST_CACHE_NAME
    digest_cache.pop("_dirty", None)
    temporary_path = None
    try:
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=cache_path.parent,
            prefix=cache_path.name,
            delete=False,
        ) as temporary:
            temporary_path = Path(temporary.name)
            json.dump(digest_cache, temporary, separators=(",", ":"))
        os.replace(temporary_path, cache_path)
    except OSError:
        if temporary_path is not None:
            try:
                temporary_path.unlink()
            except FileNotFoundError:
                pass
            except OSError:
                pass


def check(root, state_file, args_file, inputs_only=False):
    result = {
        "valid": False,
        "reason": "",
        "inputs": [],
        "sync_command": "gnrt sync --all",
    }
    marker = state_file.parent / MARKER
    try:
        if marker.exists():
            raise ValueError("sync publication is unfinished; rerun gnrt sync")
        state_contents = state_file.read_bytes()
        state = json.loads(state_contents)
        state_digest = hashlib.sha256(state_contents).hexdigest()
        digest_cache = load_digest_cache(root, state_digest)
        if inputs_only:
            inputs = digest_cache.get("inputs")
            if not isinstance(inputs, list) or not all(
                isinstance(path, str) for path in inputs
            ):
                inputs = tracked_inputs(root, state)
                digest_cache["inputs"] = inputs
                digest_cache["_dirty"] = True
            result["inputs"] = inputs
            save_digest_cache(root, digest_cache)
            result["valid"] = True
            return result
        validate(root, state, args_file, digest_cache)
        if marker.exists():
            raise ValueError("sync publication started during validation")
        save_digest_cache(root, digest_cache)
        result["valid"] = True
    except (OSError, ValueError, KeyError, TypeError) as error:
        result["reason"] = str(error)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path)
    parser.add_argument("--state", type=Path)
    parser.add_argument("--args-file", type=Path)
    parser.add_argument("--inputs-only", action="store_true")
    parser.add_argument("--missing-proxy")
    args = parser.parse_args()
    if args.missing_proxy:
        print(
            f"Third-party declaration {args.missing_proxy} is not prepared. "
            "Run `gnrt sync --all` or sync the product target with matching "
            "GN arguments before building.",
            file=sys.stderr,
        )
        return 1
    if args.root is None or args.state is None:
        parser.error("--root and --state are required for validation")
    root = args.root.resolve()
    state = root / args.state
    print(json.dumps(check(root, state, args.args_file, args.inputs_only)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
