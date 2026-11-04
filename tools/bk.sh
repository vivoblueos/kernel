#!/usr/bin/env bash
#
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
#
# Single entry point for BlueKernel developer workflows.
#
#   tools/bk.sh env      report toolchain status and per-tool install hints
#   tools/bk.sh build    gn gen + ninja default, then verify the ELF exists
#   tools/bk.sh test     ninja check_all
#   tools/bk.sh run      boot the shell app under QEMU
#   tools/bk.sh audit    run the POSIX coverage auditor (P0-03)
#   tools/bk.sh clean    remove this profile's out dir (--all for all profiles)
#
# The GN argument rules deliberately live in tools/ci/run_profile.py. This
# script never restates them: a local `bk.sh build` and a CI profile therefore
# share the same out dir and the same args by construction.
#
# Environment overrides: BK_BOARD, BK_BUILD_TYPE, BK_OUT_DIR, BK_IMAGE,
# BK_CONTAINER={auto,always,never}, BK_JOBS, BK_IN_CONTAINER.

set -euo pipefail

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "${SCRIPT_DIR}/.." && pwd)

BOARD=${BK_BOARD:-qemu_virt64_aarch64}
BUILD_TYPE=${BK_BUILD_TYPE:-debug}
CONTAINER_MODE=${BK_CONTAINER:-auto}
IMAGE=${BK_IMAGE:-ghcr.io/vivoblueos/kernel:latest}
JOBS=${BK_JOBS:-}
DRY_RUN=0
COMMAND=
ENGINE=
MODE=
EXTRA_ARGS=()

if [[ -t 1 ]]; then
  C_RESET=$'\033[0m'
  C_BOLD=$'\033[1m'
  C_RED=$'\033[31m'
  C_GREEN=$'\033[32m'
  C_YELLOW=$'\033[33m'
  C_DIM=$'\033[2m'
else
  C_RESET= C_BOLD= C_RED= C_GREEN= C_YELLOW= C_DIM=
fi

usage() {
  cat <<'EOF'
用法: tools/bk.sh [全局选项] <命令> [命令选项]

命令:
  env                打印工具链状态与逐条安装指引
  build              gn gen + ninja default，并校验内核 ELF 产物
  test               ninja check_all
  run                构建并在 QEMU 中启动 shell_runner
  audit              运行 POSIX 覆盖度审计器
  lang-gate          检查 kernel/ 下是否混入 C/汇编源码（内核只写 Rust）
  clean              删除当前 profile 的 out 目录（--all 删除整个 out/）

全局选项:
  --board NAME           目标板，默认 qemu_virt64_aarch64
  --build-type TYPE      debug | release，默认 debug
  --container WHEN       auto | always | never，默认 auto
  --image REF            容器镜像，默认 ghcr.io/vivoblueos/kernel:latest
  -j N                   传给 ninja 的并行度
  -n, --dry-run          只打印将执行的命令
  -h, --help             显示本帮助

命令选项:
  run   --target NAME    要构建的运行目标，默认 shell_runner
  clean --all            删除整个 out/ 而不只是当前 profile

示例:
  tools/bk.sh env
  tools/bk.sh build -j 8
  tools/bk.sh test --board none
  tools/bk.sh run --target shell_runner
EOF
}

info() { printf '%s\n' "$*"; }
ok() { printf '%s%s%s\n' "$C_GREEN" "$*" "$C_RESET"; }
warn() { printf '%s警告: %s%s\n' "$C_YELLOW" "$*" "$C_RESET" >&2; }
die() {
  printf '%s错误: %s%s\n' "$C_RED" "$*" "$C_RESET" >&2
  exit 2
}

have() { command -v "$1" >/dev/null 2>&1; }

quote_cmd() {
  local out= arg
  for arg in "$@"; do
    if [[ $arg =~ ^[A-Za-z0-9_./:=@+-]+$ ]]; then
      out+="$arg "
    else
      out+="'${arg//\'/\'\\\'\'}' "
    fi
  done
  printf '%s' "${out% }"
}

# The profile definition is owned by run_profile.py. Importing it here keeps a
# single source of truth for validation and out-dir naming.
py_profile() {
  python3 - "$BOARD" "$BUILD_TYPE" "$1" <<'PY'
import sys
sys.path.insert(0, "tools/ci")
from run_profile import Profile

board, build_type, attribute = sys.argv[1:4]
profile = Profile(board, build_type)
try:
    profile.validate()
except ValueError as error:
    print(error, file=sys.stderr)
    sys.exit(2)
print(getattr(profile, attribute))
PY
}

resolve_profile() {
  [[ -d $REPO_ROOT/tools/ci ]] || die "缺少 tools/ci，请在仓库根目录运行"
  # py_profile prints its diagnostic to stderr, so a failed validation cannot
  # contaminate OUT_DIR.
  OUT_DIR=$( cd "$REPO_ROOT" && py_profile out_dir ) ||
    die "profile 非法: ${BOARD}/${BUILD_TYPE}"
}

# Tools are grouped so `env` can report precisely what a given board needs.
core_tools() { printf '%s\n' gn ninja python3; }
cross_tools() {
  printf '%s\n' aarch64-none-elf-gcc aarch64-none-elf-g++ \
    aarch64-none-elf-ar aarch64-none-elf-objcopy aarch64-none-elf-cpp
}
rust_tools() { printf '%s\n' rustc clippy-driver bindgen cbindgen; }
emu_tools() { printf '%s\n' qemu-system-aarch64; }

required_tools() {
  core_tools
  if [[ $BOARD != none ]]; then
    case $BOARD in
      qemu_riscv64 | qemu_riscv32) printf '%s\n' riscv64-unknown-elf-gcc ;;
      *) cross_tools ;;
    esac
    rust_tools
    emu_tools
  fi
}

missing_tools() {
  local tool
  while IFS= read -r tool; do
    if [[ -z $tool ]]; then continue; fi
    have "$tool" || printf '%s\n' "$tool"
  done < <(required_tools | sort -u)
}

rust_target_ok() {
  local target=aarch64-vivo-blueos-newlib
  [[ $BOARD == none ]] && return 0
  case $BOARD in
    qemu_riscv64 | qemu_riscv32) target=riscv64-vivo-blueos ;;
  esac
  rustc --print target-list 2>/dev/null | grep -qx "$target"
}

local_toolchain_ok() {
  [[ -z $(missing_tools) ]] && rust_target_ok
}

install_hint() {
  case $1 in
    gn) info '    sudo apt-get install -y generate-ninja          # 提供 /usr/bin/gn' ;;
    ninja) info '    sudo apt-get install -y ninja-build' ;;
    python3) info '    sudo apt-get install -y python3' ;;
    aarch64-none-elf-*)
      info '    下载 Arm GNU Toolchain 14.2.rel1 (aarch64-none-elf) 并加入 PATH'
      info '    https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads'
      ;;
    riscv64-unknown-elf-gcc)
      info '    下载 xPack riscv-none-elf-gcc 14.2.0-3 并加入 PATH'
      info '    https://github.com/xpack-dev-tools/riscv-none-elf-gcc-xpack/releases'
      ;;
    rustc | clippy-driver)
      info '    安装 BlueOS Rust 工具链（含 aarch64-vivo-blueos-newlib target）'
      info '    https://github.com/vivoblueos/toolchain/releases'
      ;;
    bindgen) info '    cargo install bindgen-cli@0.72.1 --locked' ;;
    cbindgen) info '    cargo install cbindgen --locked' ;;
    qemu-system-aarch64)
      info '    下载 BlueOS 预编译 QEMU 或 sudo apt-get install -y qemu-system-arm'
      ;;
    *) info "    安装 $1" ;;
  esac
}

container_engine() {
  local candidate
  for candidate in docker podman; do
    if have "$candidate"; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done
  return 1
}

image_present() {
  [[ -n $ENGINE ]] && "$ENGINE" image inspect "$IMAGE" >/dev/null 2>&1
}

in_official_image() {
  [[ ${BK_IN_CONTAINER:-0} == 1 ]] && return 0
  [[ -x /opt/sysroot/usr/local/bin/gn && -d /opt/sysroot/usr/local/lib/rustlib ]]
}

resolve_mode() {
  case $CONTAINER_MODE in
    never) MODE=local ;;
    always)
      ENGINE=$(container_engine) || die "未找到 docker/podman，无法使用 --container=always"
      MODE=container
      ;;
    auto)
      if in_official_image; then
        MODE=local
      elif ENGINE=$(container_engine) && image_present; then
        MODE=container
      elif local_toolchain_ok; then
        MODE=local
      else
        MODE=none
      fi
      ;;
    *) die "--container 只接受 auto/always/never" ;;
  esac
}

container_prefix() {
  local -a prefix=("$ENGINE" run --rm --init -v "$REPO_ROOT:/work" -w /work)
  if [[ -n $JOBS ]]; then prefix+=(-e "NINJAFLAGS=-j${JOBS}"); fi
  prefix+=("$IMAGE")
  printf '%s\0' "${prefix[@]}"
}

run_cmd() {
  local -a prefix=()
  if [[ $MODE == container ]]; then
    local -a raw=()
    while IFS= read -r -d '' part; do raw+=("$part"); done < <(container_prefix)
    prefix=("${raw[@]}")
  fi
  if ((DRY_RUN)); then
    printf '+ %s\n' "$(quote_cmd "${prefix[@]}" "$@")"
    return 0
  fi
  ( cd "$REPO_ROOT" && "${prefix[@]}" "$@" )
}

ensure_toolchain() {
  resolve_mode
  # A dry run is also the escape hatch for a machine with no toolchain at all:
  # it must show the exact commands without demanding that they can run.
  if ((DRY_RUN)); then return 0; fi
  if [[ $MODE == none ]]; then
    warn "本地工具链不完整，且未找到可用的 $IMAGE 镜像"
    info ""
    report_env
    info ""
    info "${C_BOLD}补齐方式${C_RESET}（任选其一）:"
    info "  A. 使用官方容器（推荐，与 CI 完全一致）"
    info "     docker pull $IMAGE"
    info "     tools/bk.sh build"
    info "  B. 在本机安装缺失工具"
    local tool
    while IFS= read -r tool; do
      if [[ -z $tool ]]; then continue; fi
      info "  - $tool"
      install_hint "$tool"
    done < <(missing_tools)
    exit 2
  fi
  if [[ $MODE == container ]] && ! image_present; then
    die "镜像 $IMAGE 不存在，请先执行: $ENGINE pull $IMAGE"
  fi
}

report_env() {
  printf '%sBlueKernel 构建环境%s\n' "$C_BOLD" "$C_RESET"
  printf '  board        %s\n' "$BOARD"
  printf '  build_type   %s\n' "$BUILD_TYPE"
  printf '  out_dir      %s\n' "${OUT_DIR:-<未解析>}"
  printf '  容器模式     %s\n' "$CONTAINER_MODE"
  if [[ -n $ENGINE ]]; then
    printf '  容器引擎     %s (%s)\n' "$ENGINE" "$([[ $MODE == container ]] && echo 使用 || echo 未使用)"
  fi
  printf '\n'
  printf '  %-26s %-6s %s\n' "工具" "状态" "路径 / 说明"
  local tool status detail missing=0
  while IFS= read -r tool; do
    if [[ -z $tool ]]; then continue; fi
    if have "$tool"; then
      status="OK"
      detail=$(command -v "$tool")
      printf '  %-26s %s%-6s%s %s\n' "$tool" "$C_GREEN" "$status" "$C_RESET" "$detail"
    else
      status="MISS"
      missing=$((missing + 1))
      printf '  %-26s %s%-6s%s %s\n' "$tool" "$C_RED" "$status" "$C_RESET" "(见下方安装指引)"
    fi
  done < <(required_tools | sort -u)
  if [[ $BOARD != none ]]; then
    if rust_target_ok; then
      printf '  %-26s %s%-6s%s %s\n' "rust target" "$C_GREEN" "OK" "$C_RESET" \
        "$(case $BOARD in qemu_riscv64 | qemu_riscv32) echo riscv64-vivo-blueos ;; *) echo aarch64-vivo-blueos-newlib ;; esac)"
    else
      printf '  %-26s %s%-6s%s %s\n' "rust target" "$C_RED" "MISS" "$C_RESET" "BlueOS 自定义 target 不在 rustc 中"
      missing=$((missing + 1))
    fi
  fi
  printf '\n'
  if ((missing == 0)); then
    ok "工具链完整，可以执行 tools/bk.sh build"
  else
    warn "缺失 $missing 项；tools/bk.sh build 将自动改用容器或打印安装指引"
  fi
}

verify_elf() {
  ((DRY_RUN)) && return 0
  [[ $BOARD == none ]] && return 0
  local bin_dir="$REPO_ROOT/$OUT_DIR/bin" found=0 file magic
  [[ -d $bin_dir ]] || die "构建结束但 $OUT_DIR/bin 不存在"
  while IFS= read -r file; do
    magic=$(head -c 4 "$file" 2>/dev/null | od -An -tx1 | tr -d ' \n')
    if [[ $magic == 7f454c46 ]]; then found=$((found + 1)); fi
  done < <(find "$bin_dir" -maxdepth 1 -type f ! -name '*.sh' ! -name '*.bin' ! -name '*.log' ! -name '*.syslog')
  ((found > 0)) || die "$OUT_DIR/bin 下没有 ELF 产物，构建未真正完成"
  ok "产物校验通过: $OUT_DIR/bin 下 $found 个 ELF"
}

cmd_env() {
  resolve_mode
  report_env
  if [[ $MODE != container ]]; then
    info "${C_BOLD}逐条安装指引${C_RESET}"
    local tool
    while IFS= read -r tool; do
      if [[ -z $tool ]]; then continue; fi
      info "  - $tool"
      install_hint "$tool"
    done < <(missing_tools)
    info ""
    info "或直接使用官方镜像: docker run --rm -it -v \"\$PWD:/work\" -w /work $IMAGE bash"
  fi
}

cmd_build() {
  ensure_toolchain
  # The kernel is written in Rust; fail before the build if a C or assembly
  # source has crept back into kernel/.
  cmd_lang_gate
  if [[ -n $JOBS ]]; then export NINJAFLAGS="-j${JOBS}"; fi
  run_cmd python3 tools/ci/run_profile.py --board "$BOARD" --build-type "$BUILD_TYPE" \
    --only gen
  run_cmd python3 tools/ci/run_profile.py --board "$BOARD" --build-type "$BUILD_TYPE" \
    --only build
  if ((DRY_RUN)); then
    info "${C_DIM}dry-run：以上命令未执行${C_RESET}"
    return 0
  fi
  verify_elf
  ok "构建完成: $OUT_DIR"
}

cmd_test() {
  ensure_toolchain
  if [[ -n $JOBS ]]; then export NINJAFLAGS="-j${JOBS}"; fi
  # `test` is a standalone entry point: make sure the profile is generated and
  # built first, otherwise a fresh checkout fails with a missing out dir.
  run_cmd python3 tools/ci/run_profile.py --board "$BOARD" --build-type "$BUILD_TYPE" \
    --only gen
  run_cmd python3 tools/ci/run_profile.py --board "$BOARD" --build-type "$BUILD_TYPE" \
    --only build
  run_cmd python3 tools/ci/run_profile.py --board "$BOARD" --build-type "$BUILD_TYPE" \
    --only test
  if ((DRY_RUN)); then
    info "${C_DIM}dry-run：以上命令未执行${C_RESET}"
    return 0
  fi
  ok "check_all 通过"
}

cmd_run() {
  local target=shell_runner
  local -a rest=()
  while ((${#EXTRA_ARGS[@]})); do
    case ${EXTRA_ARGS[0]} in
      --target)
        [[ ${#EXTRA_ARGS[@]} -ge 2 ]] || die "--target 需要一个值"
        target=${EXTRA_ARGS[1]}
        EXTRA_ARGS=("${EXTRA_ARGS[@]:2}")
        ;;
      --target=*)
        target=${EXTRA_ARGS[0]#*=}
        EXTRA_ARGS=("${EXTRA_ARGS[@]:1}")
        ;;
      *) rest+=("${EXTRA_ARGS[0]}"); EXTRA_ARGS=("${EXTRA_ARGS[@]:1}") ;;
    esac
  done
  ensure_toolchain
  run_cmd python3 tools/ci/run_profile.py --board "$BOARD" --build-type "$BUILD_TYPE" \
    --only gen
  if ((DRY_RUN)); then
    printf '+ ninja -C %s %s\n' "$OUT_DIR" "$target"
    printf '+ %s/bin/%s-qemu.sh\n' "$OUT_DIR" "$target"
    return 0
  fi
  run_cmd ninja -C "$OUT_DIR" "$target"
  local runner="$REPO_ROOT/$OUT_DIR/bin/${target}-qemu.sh"
  [[ -f $runner ]] || die "未找到 $runner；该 board 可能没有 QEMU runner"
  chmod +x "$runner"
  info "${C_DIM}启动 $target（Ctrl-A X 退出）${C_RESET}"
  exec "$runner"
}

cmd_audit() {
  [[ -f $REPO_ROOT/tools/posix_audit.py ]] ||
    die "tools/posix_audit.py 不存在（由 P0-03 提供），无法审计"
  run_cmd python3 tools/posix_audit.py "${EXTRA_ARGS[@]}"
}

# The kernel is written in Rust. C and assembly are not allowed under kernel/,
# so this gate runs before the build: it fails fast on a stray .c file instead
# of letting it reach the link step.
cmd_lang_gate() {
  [[ -f $REPO_ROOT/tools/kernel_lang_gate.py ]] ||
    die "tools/kernel_lang_gate.py 不存在，无法执行语言门禁"
  run_cmd python3 tools/kernel_lang_gate.py "${EXTRA_ARGS[@]}"
}

cmd_clean() {
  local all=0
  if [[ ${EXTRA_ARGS[0]:-} == --all ]]; then all=1; fi
  local -a targets=()
  if ((all)); then
    targets=("$REPO_ROOT/out")
  else
    targets=("$REPO_ROOT/$OUT_DIR")
  fi
  local path
  for path in "${targets[@]}"; do
    if ((DRY_RUN)); then
      printf '+ rm -rf %s\n' "$path"
    elif [[ -e $path ]]; then
      rm -rf "$path"
      ok "已删除 $path"
    else
      info "无需删除（不存在）: $path"
    fi
  done
}

parse_args() {
  while (($#)); do
    case $1 in
      -h | --help) usage; exit 0 ;;
      --board) BOARD=${2:?--board 需要参数}; shift 2 ;;
      --board=*) BOARD=${1#*=}; shift ;;
      --build-type) BUILD_TYPE=${2:?--build-type 需要参数}; shift 2 ;;
      --build-type=*) BUILD_TYPE=${1#*=}; shift ;;
      --container) CONTAINER_MODE=${2:?--container 需要参数}; shift 2 ;;
      --container=*) CONTAINER_MODE=${1#*=}; shift ;;
      --image) IMAGE=${2:?--image 需要参数}; shift 2 ;;
      --image=*) IMAGE=${1#*=}; shift ;;
      -j) JOBS=${2:?-j 需要参数}; shift 2 ;;
      -j*) JOBS=${1#-j}; shift ;;
      -n | --dry-run) DRY_RUN=1; shift ;;
      --) shift; EXTRA_ARGS+=("$@"); break ;;
      -*)
        # Command-specific flags (for example `run --target`) are kept for the
        # command to parse after the command name is known.
        if [[ -n $COMMAND ]]; then EXTRA_ARGS+=("$1"); shift; else die "未知选项: $1"; fi
        ;;
      env | build | test | run | audit | lang-gate | clean)
        [[ -z $COMMAND ]] || die "只能指定一个命令（已有: $COMMAND，又遇到: $1）"
        COMMAND=$1
        shift
        ;;
      *)
        # Anything after the command name belongs to that command (for
        # example `audit --json path`).
        if [[ -n $COMMAND ]]; then EXTRA_ARGS+=("$1"); shift; else
          die "未知参数: $1（用 --help 查看用法）"
        fi
        ;;
    esac
  done
  [[ -n $COMMAND ]] || { usage; exit 2; }
}

main() {
  parse_args "$@"
  resolve_profile
  case $COMMAND in
    env) cmd_env ;;
    build) cmd_build ;;
    test) cmd_test ;;
    run) cmd_run ;;
    audit) cmd_audit ;;
    lang-gate) cmd_lang_gate ;;
    clean) cmd_clean ;;
    *) die "未知命令: $COMMAND" ;;
  esac
}

main "$@"
