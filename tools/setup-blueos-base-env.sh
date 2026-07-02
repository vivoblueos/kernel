#!/usr/bin/env bash
set -Eeuo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
WORKSPACE="${SCRIPT_DIR}/blueos-dev"
BLUEOS_BIN_TOOLS_PREFIX="${HOME}/.local/opt/blueos"
ENV_FILE="${SCRIPT_DIR}/blueos-env.sh"
CACHE_DIR="${HOME}/.cache/blueos-dev/downloads"
REPO_URL="https://github.com/vivoblueos/manifests.git"
DRY_RUN=0
SKIP_APT=0
SKIP_QEMU=0
SKIP_REPO_SYNC=0
ARM_VERSION="14.3.rel1"
QEMU_VERSION="10.0.2"

APT_PACKAGES=(
  build-essential cmake ninja-build pkg-config libssl-dev gdb-multiarch
  curl git wget libslirp-dev python3 python3-pip meson libglib2.0-dev
  flex bison libfdt-dev gcc-riscv64-unknown-elf clang llvm lld
  python3-kconfiglib python3-tomli clang-format yapf3 xz-utils
  ca-certificates tar make file repo generate-ninja
)

usage() {
  cat <<'EOF'
Usage: ./setup-blueos-base-env.sh [options]

Prepare the Linux development environment documented by BlueOS.

Options:
  --workspace PATH      BlueOS repo workspace. Default: <script-dir>/blueos-dev
  --prefix PATH         Tool install prefix. Default: ~/.local/opt/blueos
  --env-file PATH       Environment file to generate. Default: <script-dir>/blueos-env.sh
  --ssh                 Use git@github.com:vivoblueos/manifests.git for repo init
  --https               Use https://github.com/vivoblueos/manifests.git for repo init
  --skip-apt            Do not run apt install
  --skip-qemu           Do not build/install QEMU
  --skip-repo-sync      Run repo init if needed, but skip repo sync
  --dry-run             Print commands without changing the system
  -h, --help            Show this help
EOF
}

log() {
  printf '[blueos-base] %s\n' "$*"
}

section() {
  local title="[blueos-base] $*"
  local width=78
  local inner_width=$((width - 4))
  local line
  line="$(printf '%*s' "$width" '' | tr ' ' '=')"

  printf '\n%s\n' "$line"
  printf '| %-*.*s |\n' "$inner_width" "$inner_width" "$title"
  printf '%s\n\n' "$line"
}

die() {
  printf '[blueos-base] error: %s\n' "$*" >&2
  exit 1
}

run() {
  if [[ "$DRY_RUN" == 1 ]]; then
    printf '[dry-run]'
    printf ' %q' "$@"
    printf '\n'
  else
    "$@"
  fi
}

as_abs_path() {
  local path="$1"
  if [[ "$path" == /* ]]; then
    printf '%s\n' "$path"
  else
    printf '%s/%s\n' "$PWD" "$path"
  fi
}

parse_args() {
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --workspace)
        [[ $# -ge 2 ]] || die "--workspace requires a path"
        WORKSPACE="$(as_abs_path "$2")"
        shift 2
        ;;
      --prefix)
        [[ $# -ge 2 ]] || die "--prefix requires a path"
        BLUEOS_BIN_TOOLS_PREFIX="$(as_abs_path "$2")"
        shift 2
        ;;
      --env-file)
        [[ $# -ge 2 ]] || die "--env-file requires a path"
        ENV_FILE="$(as_abs_path "$2")"
        shift 2
        ;;
      --ssh)
        REPO_URL="git@github.com:vivoblueos/manifests.git"
        shift
        ;;
      --https)
        REPO_URL="https://github.com/vivoblueos/manifests.git"
        shift
        ;;
      --skip-apt)
        SKIP_APT=1
        shift
        ;;
      --skip-qemu)
        SKIP_QEMU=1
        shift
        ;;
      --skip-repo-sync)
        SKIP_REPO_SYNC=1
        shift
        ;;
      --dry-run)
        DRY_RUN=1
        shift
        ;;
      -h|--help)
        usage
        exit 0
        ;;
      *)
        die "unknown option: $1"
        ;;
    esac
  done
}

check_platform() {
  section "Check platform"
  [[ -r /etc/os-release ]] || die "cannot read /etc/os-release"
  # shellcheck disable=SC1091
  . /etc/os-release

  case "${ID:-}" in
    ubuntu)
      [[ "${VERSION_ID%%.*}" -ge 24 ]] || die "Ubuntu 24.04+ is required; found ${VERSION_ID:-unknown}"
      ;;
    debian)
      [[ "${VERSION_ID%%.*}" -ge 12 ]] || die "Debian 12+ is required; found ${VERSION_ID:-unknown}"
      ;;
    *)
      die "Debian 12+ or Ubuntu 24.04+ is required; found ${PRETTY_NAME:-unknown}"
      ;;
  esac
}

install_apt_packages() {
  section "Install distribution packages"
  if [[ "$SKIP_APT" == 1 ]]; then
    log "Skipping apt install"
    return
  fi

  log "Installing distribution packages"
  run sudo apt-get update
  run sudo env DEBIAN_FRONTEND=noninteractive apt-get install -y "${APT_PACKAGES[@]}"
}

ensure_dirs() {
  section "Prepare install directories"
  run mkdir -p "${BLUEOS_BIN_TOOLS_PREFIX}/bin" "${BLUEOS_BIN_TOOLS_PREFIX}/toolchains" "${BLUEOS_BIN_TOOLS_PREFIX}/src" "${BLUEOS_BIN_TOOLS_PREFIX}/qemu" "$CACHE_DIR"
  export PATH="${BLUEOS_BIN_TOOLS_PREFIX}/bin:${PATH}"
}

install_repo_if_needed() {
  section "Install repo launcher"
  if command -v repo >/dev/null 2>&1; then
    log "repo already available: $(command -v repo)"
    return
  fi

  log "Installing repo into ${BLUEOS_BIN_TOOLS_PREFIX}/bin"
  run mkdir -p "${BLUEOS_BIN_TOOLS_PREFIX}/bin"
  run curl -fsSL "https://mirrors.tuna.tsinghua.edu.cn/git/git-repo" -o "${BLUEOS_BIN_TOOLS_PREFIX}/bin/repo"
  run chmod +x "${BLUEOS_BIN_TOOLS_PREFIX}/bin/repo"
}

check_gn() {
  section "Check GN"
  if command -v gn >/dev/null 2>&1; then
    log "gn available: $(command -v gn)"
    return
  fi

  if [[ -x /usr/bin/gn ]]; then
    log "gn available: /usr/bin/gn"
    return
  fi

  if [[ "$DRY_RUN" == 1 ]]; then
    log "Would verify gn after apt installs generate-ninja"
    return
  fi

  die "gn was not found after apt install. On Ubuntu this is usually provided by generate-ninja."
}

download_and_extract_arm_toolchain() {
  local target="$1"
  local archive="arm-gnu-toolchain-${ARM_VERSION}-x86_64-${target}.tar.xz"
  local url="https://developer.arm.com/-/media/Files/downloads/gnu/${ARM_VERSION}/binrel/${archive}"
  local install_dir="${BLUEOS_BIN_TOOLS_PREFIX}/toolchains/arm-gnu-toolchain-${ARM_VERSION}-x86_64-${target}"

  if [[ -x "${install_dir}/bin/${target}-gcc" ]]; then
    log "ARM toolchain already installed: ${install_dir}"
    return
  fi

  log "Installing ARM toolchain: ${target}"
  run wget -c "$url" -O "${CACHE_DIR}/${archive}"
  run tar -xJf "${CACHE_DIR}/${archive}" -C "${BLUEOS_BIN_TOOLS_PREFIX}/toolchains"
}

install_arm_toolchains() {
  section "Install ARM toolchains"
  download_and_extract_arm_toolchain "arm-none-eabi"
  download_and_extract_arm_toolchain "aarch64-none-elf"
}

install_qemu() {
  section "Build and install QEMU"
  if [[ "$SKIP_QEMU" == 1 ]]; then
    log "Skipping QEMU build"
    return
  fi

  local qemu_prefix="${BLUEOS_BIN_TOOLS_PREFIX}/qemu/${QEMU_VERSION}"
  local qemu_bin="${qemu_prefix}/bin/qemu-system-aarch64"
  local archive="qemu-${QEMU_VERSION}.tar.xz"
  local source_dir="${BLUEOS_BIN_TOOLS_PREFIX}/src/qemu-${QEMU_VERSION}"
  local build_dir="${source_dir}/build"

  if [[ -x "$qemu_bin" ]]; then
    log "QEMU already installed: ${qemu_bin}"
    return
  fi

  log "Building QEMU ${QEMU_VERSION}"
  run wget -c "https://download.qemu.org/${archive}" -O "${CACHE_DIR}/${archive}"
  run tar -xJf "${CACHE_DIR}/${archive}" -C "${BLUEOS_BIN_TOOLS_PREFIX}/src"
  run mkdir -p "$build_dir"
  run bash -lc "cd \"${build_dir}\" && ../configure --prefix=\"${qemu_prefix}\" --enable-slirp"
  run make -C "$build_dir" "-j$(nproc)" install
}

write_env_file() {
  section "Write environment file"
  if [[ "$DRY_RUN" == 1 ]]; then
    log "Would write environment file: ${ENV_FILE}"
    return
  fi

  cat >"$ENV_FILE" <<EOF
# Generated by ${SCRIPT_DIR}/setup-blueos-base-env.sh
export BLUEOS_WORKSPACE="${WORKSPACE}"
export BLUEOS_PREFIX="${BLUEOS_BIN_TOOLS_PREFIX}"
export BLUEOS_RUST_PREFIX="${BLUEOS_BIN_TOOLS_PREFIX}/rust"

blueos_path_prepend() {
  case ":\${PATH}:" in
    *":\$1:"*) ;;
    *) export PATH="\$1:\${PATH}" ;;
  esac
}

blueos_path_prepend "\${BLUEOS_PREFIX}/bin"
blueos_path_prepend "\${BLUEOS_PREFIX}/qemu/${QEMU_VERSION}/bin"
blueos_path_prepend "\${BLUEOS_PREFIX}/toolchains/arm-gnu-toolchain-${ARM_VERSION}-x86_64-arm-none-eabi/bin"
blueos_path_prepend "\${BLUEOS_PREFIX}/toolchains/arm-gnu-toolchain-${ARM_VERSION}-x86_64-aarch64-none-elf/bin"

if [ -d "\${BLUEOS_RUST_PREFIX}/usr/local/bin" ]; then
  blueos_path_prepend "\${BLUEOS_RUST_PREFIX}/usr/local/bin"
fi

unset -f blueos_path_prepend
EOF
  log "Wrote environment file: ${ENV_FILE}"
}

init_blueos_workspace() {
  section "Initialize and sync BlueOS workspace"
  log "Preparing BlueOS workspace: ${WORKSPACE}"
  run mkdir -p "$WORKSPACE"

  if [[ ! -d "${WORKSPACE}/.repo" ]]; then
    run bash -lc "cd \"${WORKSPACE}\" && repo init -u \"${REPO_URL}\" -b main -m manifest.xml"
  else
    log "repo workspace already initialized"
  fi

  if [[ "$SKIP_REPO_SYNC" == 1 ]]; then
    log "Skipping repo sync"
  else
    run bash -lc "cd \"${WORKSPACE}\" && repo sync -j\"\$(nproc)\""
  fi
}

main() {
  section "Parse options"
  parse_args "$@"
  check_platform
  install_apt_packages
  ensure_dirs
  install_repo_if_needed
  check_gn
  install_arm_toolchains
  install_qemu
  write_env_file
  init_blueos_workspace
  log "Load the environment with: source ${ENV_FILE}"
}

main "$@"
