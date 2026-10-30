set -ex

main() {
    rustup component add rust-src
    rustup target add $TARGET
}

main
