# This script takes care of testing your crate

set -euxo pipefail

main() {
    cargo check --target $TARGET
}

main
