#!/usr/bin/env python3

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
"""Run a Rust compiler with build.rs-provided environment variables.

The GN rust toolchain routes every rustc/clippy invocation through this script:

    python3 run_rustc.py <compiler> [compiler args...]

`<compiler>` is the real driver (e.g. `rustc` or `clippy-driver`) and every
remaining argument is forwarded to it unchanged.

When `BUILD_SCRIPT_RUSTC_ENV_FILE` points at an environment file, the variables
it defines are merged into the compiler environment, overriding inherited ones.
The file holds one `[export ]KEY=VALUE` per line; blank lines and `#` comments
are ignored and the value may be single- or double-quoted. This is how a crate's
build script (cargo:rustc-env) reaches its own compilation without a per-target
tool command.

The compiler replaces this process via exec, so its exit status and signals are
preserved.
"""

import os
import sys

_ENV_FILE_VAR = "BUILD_SCRIPT_RUSTC_ENV_FILE"

# Variables used by this wrapper that must not leak into the compiler.
_INTERNAL_VARS = (_ENV_FILE_VAR, )

_DOUBLE_QUOTE_ESCAPES = {
    "n": "\n",
    "t": "\t",
    "r": "\r",
    "\\": "\\",
    '"': '"',
    "$": "$",
    "`": "`",
}


def _unquote(value):
    """Returns `value` with one layer of shell-style quoting removed."""
    if len(value) >= 2 and value[0] == "'" and value[-1] == "'":
        return value[1:-1].replace("'\\''", "'")
    if len(value) >= 2 and value[0] == '"' and value[-1] == '"':
        out = []
        escaped = False
        for ch in value[1:-1]:
            if escaped:
                out.append(_DOUBLE_QUOTE_ESCAPES.get(ch, ch))
                escaped = False
            elif ch == "\\":
                escaped = True
            else:
                out.append(ch)
        if escaped:
            out.append("\\")
        return "".join(out)
    return value


def _parse_env_file(path):
    env = {}
    with open(path, "r", encoding="utf-8") as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            if line.startswith("export "):
                line = line[len("export "):].lstrip()
            if "=" not in line:
                raise ValueError(f"{path}:{lineno}: expected KEY=VALUE")
            key, value = line.split("=", 1)
            key = key.strip()
            if not key:
                raise ValueError(f"{path}:{lineno}: empty variable name")
            env[key] = _unquote(value.strip())
    return env


def main():
    if len(sys.argv) < 2:
        sys.stderr.write("run_rustc.py: missing compiler command\n")
        return 1

    args = sys.argv[1:]
    env = dict(os.environ)
    for name in _INTERNAL_VARS:
        env.pop(name, None)

    env_file = os.environ.get(_ENV_FILE_VAR)
    if env_file:
        try:
            env.update(_parse_env_file(env_file))
        except OSError as e:
            sys.stderr.write(f"run_rustc.py: cannot read {env_file}: {e}\n")
            return 1
        except ValueError as e:
            sys.stderr.write(f"run_rustc.py: {e}\n")
            return 1

    try:
        os.execvpe(args[0], args, env)
    except OSError as e:
        sys.stderr.write(f"run_rustc.py: cannot exec {args[0]}: {e}\n")
        return 1


if __name__ == "__main__":
    sys.exit(main())
