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

# This code is based on https://chromium.googlesource.com/chromium/src/+/refs/heads/main/build/rust/gni_impl/run_build_script.py
# Copyright 2021 The Chromium Authors
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.
"""Run a Cargo build script and collect its rustc flags and environment.

GN supplies target cfgs and Cargo environment variables. Generated files stay
in OUT_DIR, and stamps trigger dependent compilation when the script reruns.
"""

import argparse
import json
import os
import re
import shlex
import subprocess
import sys

import action_helpers

# Accept both cargo: and cargo:: directive prefixes.
RUSTC_CFG_LINE = re.compile("cargo::?rustc-cfg=(.*)")
RUSTC_ENV_LINE = re.compile("cargo::?rustc-env=(.*)")
RUSTC_LINK_SEARCH_LINE = re.compile("cargo::?rustc-link-search=(.*)")
RUSTC_LINK_LIB_LINE = re.compile("cargo::?rustc-link-lib=(.*)")
RUSTC_FLAGS_LINE = re.compile("cargo::?rustc-flags=(.*)")

LINK_SEARCH_NATIVE = re.compile("native=(.*)")

NATIVE_VARIABLES = (
    'CC',
    'CXX',
    'AR',
    'RANLIB',
    'NVCC',
    'CC_MASM_ASM',
    'CXXSTDLIB',
    'CXXSTDLIB_STATIC',
    'CFLAGS',
    'CXXFLAGS',
    'ARFLAGS',
    'RANLIBFLAGS',
)
NATIVE_SETTINGS = (
    'CROSS_COMPILE',
    'CRATE_CC_NO_DEFAULTS',
    'RUSTC_LINKER',
    'SDKROOT',
    'MACOSX_DEPLOYMENT_TARGET',
    'IPHONEOS_DEPLOYMENT_TARGET',
    'TVOS_DEPLOYMENT_TARGET',
    'WATCHOS_DEPLOYMENT_TARGET',
    'XROS_DEPLOYMENT_TARGET',
    'WASI_SDK_PATH',
    'WASI_SYSROOT',
    'WASM_MUSL_SYSROOT',
    'PAUTHTEST_SYSROOT',
    'PAUTHTEST_RESOURCE_DIR',
    'VCINSTALLDIR',
    'VSINSTALLDIR',
)


def shell_quote(value):
    """Quotes `value` so run_rustc.py can parse it back as a shell literal."""
    return "'" + value.replace("'", "'\\''") + "'"


def parse_link_lib(value):
    """Splits name or kind=name into (kind, name)."""
    kind, sep, name = value.partition("=")
    if not sep:
        return "", value
    return kind, name


def write_stamps(stamp_files):
    """Updates stamp mtimes so dependents rebuild after the build script runs."""
    for path in stamp_files:
        parent = os.path.dirname(path)
        if parent:
            os.makedirs(parent, exist_ok=True)
        with open(path, "w"):
            pass


def cargo_cfg_env(cfgs):
    """Converts GN's rustc cfg lines into build-script environment variables."""
    values = {}
    for line in cfgs:
        key, separator, value = line.partition('=')
        entries = values.setdefault(key, [])
        if separator:
            entries.append(json.loads(value))
    return {
        'CARGO_CFG_' + key.upper(): ','.join(entries)
        for key, entries in values.items()
    }


def read_native_context(path, host, target):
    """Reads and validates GN's native tools and argument arrays."""
    with open(path, encoding='utf8') as source:
        context = json.load(source)
    if not isinstance(context, dict) or set(context) != {
            'version', 'host', 'target'
    }:
        raise ValueError(
            'native context must contain version, host, and target')
    if type(context['version']) is not int or context['version'] != 1:
        raise ValueError('unsupported native context version')
    fields = {'triple', 'cc', 'cxx', 'ar', 'cflags', 'cxxflags', 'arflags'}
    for role, triple in [('host', host), ('target', target)]:
        entry = context[role]
        if not isinstance(entry, dict) or set(entry) != fields:
            raise ValueError(
                f'native context {role} must contain {sorted(fields)}')
        if entry['triple'] != triple:
            raise ValueError(
                f'native context {role} triple does not match {triple}')
        for name in ('cc', 'cxx', 'ar'):
            value = entry[name]
            if not isinstance(value,
                              str) or not value.strip() or '\0' in value:
                raise ValueError(
                    f'native context {role}.{name} must be a tool command')
        for name in ('cflags', 'cxxflags', 'arflags'):
            value = entry[name]
            if not isinstance(value, list) or any(
                    not isinstance(flag, str) or '\0' in flag
                    for flag in value):
                raise ValueError(
                    f'native context {role}.{name} must be a string array')
    return context


def set_native_context(env, context):
    """Replaces inherited cc-rs settings with GN's native contexts."""
    for key in list(env):
        if key in NATIVE_SETTINGS or any(
                key == name or key.startswith(name + '_') or key in
            ('HOST_' + name, 'TARGET_' + name) for name in NATIVE_VARIABLES):
            del env[key]
    for role in ('host', 'target'):
        entry = context[role]
        triple = entry['triple']
        for name in ('CC', 'CXX', 'AR'):
            command = entry[name.lower()]
            env[role.upper() + '_' + name] = command
            for suffix in (triple, triple.replace('-', '_').replace('.', '_')):
                env[name + '_' + suffix] = command
            if role == 'target':
                env[name] = command
        # cc-rs accumulates flags from every lookup form, so populate just one.
        for name in ('CFLAGS', 'CXXFLAGS', 'ARFLAGS'):
            env[name + '_' + triple] = shlex.join(entry[name.lower()])
    env['CC_SHELL_ESCAPED_FLAGS'] = '1'


def main():
    parser = argparse.ArgumentParser(description='Run Rust build script.')
    parser.add_argument('--build-script',
                        required=True,
                        help='build script to run')
    parser.add_argument('--env', help='environment variable', nargs='+')
    parser.add_argument('--rustc-flags-file',
                        required=True,
                        help='where to write the rustc flags rsp file')
    parser.add_argument(
        '--rustc-env-file',
        required=True,
        help='where to write the environment exported by the build script')
    parser.add_argument('--host',
                        required=True,
                        help='host triple collected by GN, exported as HOST')
    parser.add_argument(
        '--rustc',
        required=True,
        help='host compiler configured by GN, exported as RUSTC')
    parser.add_argument('--target',
                        required=True,
                        help='rustc target triple exported as TARGET')
    parser.add_argument('--native-context-file',
                        required=True,
                        help='GN-generated host and crate native contexts')
    parser.add_argument('--profile',
                        required=True,
                        choices=['debug', 'release'],
                        help='Cargo-compatible profile name')
    parser.add_argument('--cfgs',
                        required=True,
                        nargs='+',
                        help='rustc cfg lines collected by GN')
    parser.add_argument(
        '--rustflag',
        action='append',
        default=[],
        help='extra crate rustc argument; repeat as --rustflag=<value>')
    parser.add_argument('--stamp-file',
                        nargs='+',
                        help='build-script stamp file(s) to write')
    parser.add_argument('--out-dir', required=True, help='target out dir')
    args = parser.parse_args()
    try:
        native_context = read_native_context(args.native_context_file,
                                             args.host, args.target)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    # build.rs runs with a fixed OUT_DIR that the main crate also compiles
    # with, so the files it writes are visible without a copy step.
    out_dir = os.path.abspath(args.out_dir)
    os.makedirs(out_dir, exist_ok=True)

    # Keep PATH, but discard another crate's links value.
    env = dict(os.environ)
    env.pop('CARGO_MANIFEST_LINKS', None)

    # Apply package metadata and features supplied by GN.
    if args.env:
        for entry in args.env:
            key, value = entry.split('=', 1)
            env[key] = value

    # Apply GN's native settings after package-specific --env entries.
    set_native_context(env, native_context)

    # Use GN's compiler and platform settings for this invocation.
    env["RUSTC"] = args.rustc
    # /usr/bin/env forwards wrapper-aware compiler probes to RUSTC unchanged.
    env["RUSTC_WRAPPER"] = "/usr/bin/env"
    env["OUT_DIR"] = out_dir
    env["HOST"] = args.host
    env["TARGET"] = args.target

    env.update(cargo_cfg_env(args.cfgs))
    env['CARGO_ENCODED_RUSTFLAGS'] = '\x1f'.join(args.rustflag)
    # Build scripts must read the encoded flags passed to the crate's rustc.
    env.pop('RUSTFLAGS', None)
    # GN invokes rustc directly, without a Cargo workspace wrapper.
    env.pop('RUSTC_WORKSPACE_WRAPPER', None)

    # Export profile settings from the crate's actual compiler flags.
    opt_level = '0'
    debuginfo = '0'
    # The last -C value wins, matching rustc.
    flags = iter(args.rustflag)
    for flag in flags:
        if flag == '-C':
            flag = next(flags, '')
        elif flag.startswith('-C'):
            flag = flag[2:]
        else:
            continue
        key, _, value = flag.partition('=')
        if key == 'opt-level':
            opt_level = value
        elif key == 'debuginfo':
            debuginfo = value or '2'
    env['OPT_LEVEL'] = opt_level
    env['DEBUG'] = str(debuginfo not in ['0', 'none']).lower()
    env['PROFILE'] = args.profile

    # Actions start in root_build_dir; build.rs needs absolute manifest paths.
    if "CARGO_MANIFEST_DIR" not in env:
        sys.exit("run_build_script.py: CARGO_MANIFEST_DIR missing from --env")
    manifest_dir = os.path.abspath(env["CARGO_MANIFEST_DIR"])
    env["CARGO_MANIFEST_DIR"] = manifest_dir
    env['CARGO_MANIFEST_PATH'] = os.path.join(manifest_dir, 'Cargo.toml')

    # Run build.rs, then publish its directives and success stamps.
    proc = subprocess.run([os.path.abspath(args.build_script)],
                          env=env,
                          cwd=manifest_dir,
                          encoding='utf8',
                          stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE)
    if proc.stderr.rstrip():
        print(proc.stderr.rstrip(), file=sys.stderr)
    proc.check_returncode()

    flags = ""
    rustc_env = {}
    for line in proc.stdout.split("\n"):
        line = line.rstrip()
        m = RUSTC_CFG_LINE.match(line)
        if m:
            flags = f"{flags}--cfg\n{m.group(1)}\n"
            continue
        m = RUSTC_ENV_LINE.match(line)
        if m:
            key, sep, value = m.group(1).partition("=")
            if sep:
                rustc_env[key] = value
            continue
        m = RUSTC_LINK_SEARCH_LINE.match(line)
        if m:
            # Keep native search paths and treat an omitted kind as native.
            value = m.group(1)
            nm = LINK_SEARCH_NATIVE.match(value)
            if nm:
                flags = f"{flags}-L\nnative={nm.group(1)}\n"
            elif "=" not in value:
                flags = f"{flags}-L\nnative={value}\n"
            continue
        m = RUSTC_LINK_LIB_LINE.match(line)
        if m:
            kind, name = parse_link_lib(m.group(1))
            flags = f"{flags}-l\n{name}\n"
            continue
        m = RUSTC_FLAGS_LINE.match(line)
        if m:
            for f in m.group(1).split():
                flags = f"{flags}-Clink-arg={f}\n"

    # rustc @file reads one argument per line, without shell quoting.
    # Preserve unchanged files to avoid unnecessary rebuilds.
    with action_helpers.atomic_output(args.rustc_flags_file) as output:
        output.write(flags.encode("utf-8"))

    env_contents = "".join(f"{key}={shell_quote(value)}\n"
                           for key, value in rustc_env.items())
    with action_helpers.atomic_output(args.rustc_env_file) as output:
        output.write(env_contents.encode("utf-8"))

    if args.stamp_file:
        write_stamps(args.stamp_file)


if __name__ == '__main__':
    sys.exit(main())
