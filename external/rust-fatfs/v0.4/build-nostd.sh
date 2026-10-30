#!/bin/sh
set -e
cargo build --no-default-features
cargo build --no-default-features --features alloc
cargo build --no-default-features --features lfn,alloc
