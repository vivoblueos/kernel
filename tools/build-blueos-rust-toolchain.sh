#!/usr/bin/env bash
set -Eeuo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
WORKSPACE="${SCRIPT_DIR}/blueos-dev"
BLUEOS_PREFIX="${HOME}/.local/opt/blueos"
RUST_PREFIX="${BLUEOS_PREFIX}/rust"
SRC_DIR="${HOME}/.cache/blueos-dev/rust-toolchain"
ENV_FILE="${SCRIPT_DIR}/blueos-env.sh"
LINK_RUSTUP=0
DRY_RUN=0
USE_SSH=0

TARGETS=(
  aarch64-vivo-blueos-newlib
  thumbv7m-vivo-blueos-newlibeabi
  thumbv8m.main-vivo-blueos-newlibeabihf
  riscv64-vivo-blueos
  riscv32-vivo-blueos
  riscv32imc-vivo-blueos
)

usage() {
  cat <<'EOF'
Usage: ./build-blueos-rust-toolchain.sh [options]

Build the BlueOS forked Rust toolchain after the base environment and repo sync
are complete.

Options:
  --workspace PATH      BlueOS repo workspace. Default: <script-dir>/blueos-dev
  --prefix PATH         Rust toolchain DESTDIR. Default: ~/.local/opt/blueos/rust
  --src-dir PATH        Source/build directory. Default: ~/.cache/blueos-dev/rust-toolchain
  --env-file PATH       Environment file to source if present. Default: <script-dir>/blueos-env.sh
  --ssh                 Clone vivoblueos repos over SSH instead of HTTPS
  --link-rustup         Register the built toolchain as rustup toolchain "blueos-dev"
  --dry-run             Print commands without changing the system
  -h, --help            Show this help
EOF
}

log() {
  printf '[blueos-rust] %s\n' "$*"
}

section() {
  local title="[blueos-rust] $*"
  local width=78
  local inner_width=$((width - 4))
  local line
  line="$(printf '%*s' "$width" '' | tr ' ' '=')"

  printf '\n%s\n' "$line"
  printf '| %-*.*s |\n' "$inner_width" "$inner_width" "$title"
  printf '%s\n\n' "$line"
}

die() {
  printf '[blueos-rust] error: %s\n' "$*" >&2
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
        RUST_PREFIX="$(as_abs_path "$2")"
        shift 2
        ;;
      --src-dir)
        [[ $# -ge 2 ]] || die "--src-dir requires a path"
        SRC_DIR="$(as_abs_path "$2")"
        shift 2
        ;;
      --env-file)
        [[ $# -ge 2 ]] || die "--env-file requires a path"
        ENV_FILE="$(as_abs_path "$2")"
        shift 2
        ;;
      --ssh)
        USE_SSH=1
        shift
        ;;
      --link-rustup)
        LINK_RUSTUP=1
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

repo_url() {
  local name="$1"
  if [[ "$USE_SSH" == 1 ]]; then
    printf 'git@github.com:vivoblueos/%s.git\n' "$name"
  else
    printf 'https://github.com/vivoblueos/%s.git\n' "$name"
  fi
}

load_env_if_present() {
  section "Load environment"
  if [[ -r "$ENV_FILE" ]]; then
    # shellcheck disable=SC1090
    . "$ENV_FILE"
  fi
}

check_prereqs() {
  section "Check prerequisites"
  if [[ ! -d "${WORKSPACE}/.repo" ]]; then
    if [[ "$DRY_RUN" == 1 ]]; then
      log "Would require initialized BlueOS workspace: ${WORKSPACE}"
    else
      die "BlueOS workspace is not initialized: ${WORKSPACE}"
    fi
  fi

  for cmd in git python3 make cmake ninja clang lld; do
    if ! command -v "$cmd" >/dev/null 2>&1; then
      if [[ "$DRY_RUN" == 1 ]]; then
        log "Would require command: ${cmd}"
      else
        die "missing command: ${cmd}"
      fi
    fi
  done
}

clone_or_update() {
  local name="$1"
  local dest="${SRC_DIR}/${name}"
  local url
  url="$(repo_url "$name")"

  if [[ -d "${dest}/.git" ]]; then
    log "Updating ${name}"
    run git -C "$dest" pull --ff-only
  else
    log "Cloning ${name}"
    run git clone "$url" "$dest"
  fi

  if [[ "$name" == "rust" ]]; then
    run git -C "$dest" submodule update --init --recursive
  fi
}

prepare_sources() {
  section "Clone or update Rust sources"
  run mkdir -p "$SRC_DIR" "$RUST_PREFIX"
  clone_or_update rust
  clone_or_update cc-rs
  clone_or_update libc
}

build_toolchain() {
  section "Build BlueOS Rust toolchain"
  local rust_src="${SRC_DIR}/rust"
  local host="x86_64-unknown-linux-gnu"
  if [[ ! -f "${rust_src}/config.blueos.toml" ]]; then
    if [[ "$DRY_RUN" == 1 ]]; then
      log "Would require ${rust_src}/config.blueos.toml after cloning rust"
    else
      die "missing ${rust_src}/config.blueos.toml"
    fi
  fi

  log "Building BlueOS Rust toolchain into ${RUST_PREFIX}"
  run cp "${rust_src}/config.blueos.toml" "${rust_src}/config.toml"

  run bash -lc "cd \"${rust_src}\" && CARGO_NET_GIT_FETCH_WITH_CLI=true DESTDIR=\"${RUST_PREFIX}\" ./x.py install -i --stage 1 compiler/rustc"

  local target
  for target in "${TARGETS[@]}"; do
    run bash -lc "cd \"${rust_src}\" && CARGO_NET_GIT_FETCH_WITH_CLI=true DESTDIR=\"${RUST_PREFIX}\" ./x.py install -i --stage 1 library/std --target \"${target}\""
  done

  run bash -lc "cd \"${rust_src}\" && CARGO_NET_GIT_FETCH_WITH_CLI=true DESTDIR=\"${RUST_PREFIX}\" ./x.py install -i --stage 1 library/std --target \"${host}\""
  run bash -lc "cd \"${rust_src}\" && CARGO_NET_GIT_FETCH_WITH_CLI=true DESTDIR=\"${RUST_PREFIX}\" ./x.py install -i --stage 0 rustfmt"
  run bash -lc "cd \"${rust_src}\" && CARGO_NET_GIT_FETCH_WITH_CLI=true DESTDIR=\"${RUST_PREFIX}\" ./x.py install -i --stage 0 rust-analyzer"
  run bash -lc "cd \"${rust_src}\" && CARGO_NET_GIT_FETCH_WITH_CLI=true DESTDIR=\"${RUST_PREFIX}\" ./x.py install -i --stage 0 clippy"

  run mkdir -p "${RUST_PREFIX}/usr/local"
  run cp -rav "${rust_src}/build/${host}/llvm/bin" "${rust_src}/build/${host}/llvm/lib" "${RUST_PREFIX}/usr/local/"
}

link_rustup_toolchain() {
  section "Register rustup toolchain"
  if [[ "$LINK_RUSTUP" != 1 ]]; then
    log "Skipping rustup link. Re-run with --link-rustup to register blueos-dev."
    return
  fi

  command -v rustup >/dev/null 2>&1 || die "rustup is required for --link-rustup"
  run rustup toolchain link blueos-dev "${RUST_PREFIX}/usr/local"
}

main() {
  section "Parse options"
  parse_args "$@"
  load_env_if_present
  check_prereqs
  prepare_sources
  build_toolchain
  link_rustup_toolchain
  log "Use the toolchain with: source ${ENV_FILE}"
}

main "$@"
