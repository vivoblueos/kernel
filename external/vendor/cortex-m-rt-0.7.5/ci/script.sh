#!/usr/bin/env bash

set -euxo pipefail

main() {
    cargo check --target "$TARGET"

    cargo check --target "$TARGET" --features device

    # A `critical_section` implementation is always needed.
    needed_features=cortex-m/critical-section-single-core

    if [ "$TARGET" = x86_64-unknown-linux-gnu ] && [ "$TRAVIS_RUST_VERSION" = stable ]; then
        ( cd macros && cargo check && cargo test )

        cargo test --features "device,${needed_features}" --test compiletest
    fi

    local examples=(
        alignment
        divergent-default-handler
        divergent-exception
        entry-static
        hard-fault-trampoline
        main
        minimal
        override-exception
        pre_init
        qemu
        state
        unsafe-default-handler
        unsafe-entry
        unsafe-exception
        unsafe-hard-fault
    )
    local fail_examples=(
        data_overflow
    )
    local linkers=(
        # Link with arm-none-eabi-ld
        "-C linker=arm-none-eabi-ld"
        # Link with arm-none-eabi-gcc, requires -nostartfiles
        "-C linker=arm-none-eabi-gcc -C link-arg=-nostartfiles"
        # Link with rust-lld (default)
        ""
    )
    if [ "$TARGET" != x86_64-unknown-linux-gnu ]; then
        # Only test on stable and nightly, not MSRV.
        if [ "$TRAVIS_RUST_VERSION" = stable ] || [ "$TRAVIS_RUST_VERSION" = nightly ]; then
            RUSTDOCFLAGS="-Cpanic=abort" cargo test --features "${needed_features}" --doc
        fi

        for linker in "${linkers[@]}"; do
            for ex in "${examples[@]}"; do
                cargo rustc --target "$TARGET" --example "$ex" --features "${needed_features}" -- $linker
                cargo rustc --target "$TARGET" --example "$ex" --features "${needed_features}" --release -- $linker
            done
            for ex in "${fail_examples[@]}"; do
                cargo rustc --target "$TARGET" --example "$ex" --features "${needed_features}" -- $linker && exit 1
                cargo rustc --target "$TARGET" --example "$ex" --features "${needed_features}" --release -- $linker && exit 1
            done
            cargo rustc --target "$TARGET" --example device --features "device,${needed_features}" -- $linker
            cargo rustc --target "$TARGET" --example device --features "device,${needed_features}" --release -- $linker

            cargo rustc --target "$TARGET" --example minimal --features "set-sp,${needed_features}" -- $linker
            cargo rustc --target "$TARGET" --example minimal --features "set-sp,${needed_features}" --release -- $linker
            cargo rustc --target "$TARGET" --example minimal --features "zero-init-ram,${needed_features}" -- $linker
            cargo rustc --target "$TARGET" --example minimal --features "zero-init-ram,${needed_features}" --release -- $linker
            cargo rustc --target "$TARGET" --example minimal --features "set-vtor,${needed_features}" -- $linker
            cargo rustc --target "$TARGET" --example minimal --features "set-vtor,${needed_features}" --release -- $linker
        done
    fi

    case $TARGET in
        thumbv6m-none-eabi|thumbv7m-none-eabi)
            for linker in "${linkers[@]}"; do
                env RUSTFLAGS="$linker -C link-arg=-Tlink.x" cargo run \
                    --target "$TARGET" --features "${needed_features}" --example qemu | grep "x = 42"
                env RUSTFLAGS="$linker -C link-arg=-Tlink.x" cargo run \
                    --target "$TARGET" --features "${needed_features}" --example qemu --release | grep "x = 42"
            done

            ;;
    esac
}

main
