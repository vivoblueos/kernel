set -euxo pipefail

main() {
    cargo check

    case $TARGET in
        x86_64-unknown-linux-gnu)
            cargo test
            ;;
    esac

    if [ $TRAVIS_RUST_VERSION = nightly ]; then
        cargo check --features const-fn
    fi
}

main
