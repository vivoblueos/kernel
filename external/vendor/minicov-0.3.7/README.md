minicov
=======

[![Crates.io](https://img.shields.io/crates/v/minicov.svg)](https://crates.io/crates/minicov)
[![Documentation](https://docs.rs/minicov/badge.svg)](https://docs.rs/minicov)

This crate provides code coverage and profile-guided optimization (PGO) support
for `no_std` and embedded programs.

This is done through a modified version of the LLVM profiling runtime (normally
part of compiler-rt) from which all dependencies on libc have been removed.

All types of instrumentation using the LLVM profiling runtime are supported:
- Rust code coverage with `-Cinstrument-coverage`.
- Rust profile-guided optimization with `-Cprofile-generate`.
- Clang code coverage with `-fprofile-instr-generate -fcoverage-mapping`.
- Clang profile-guided optimization with `-fprofile-instr-generate`.
- Clang LLVM IR profile-guided optimization with `-fprofile-generate`.

Note that to profile both C and Rust code at the same time you must use Clang
with the same LLVM version as the LLVM used by rustc. You can pass these flags
to C code compiled with the `cc` crates using [environment variables].

[environment variables]: https://github.com/rust-lang/cc-rs#external-configuration-via-environment-variables

## Usage

Note: This crate requires a recent nightly compiler.

1. Ensure that the following environment variables are set up:

```sh
export RUSTFLAGS="-Cinstrument-coverage -Zno-profiler-runtime"
```

Note that these flags also apply to build-dependencies and proc
macros by default. This can be worked around by explicitly
specifying a target when invoking cargo:

```sh
# Applies RUSTFLAGS to everything
cargo build

# Doesn't apply RUSTFLAGS to build dependencies and proc macros
cargo build --target x86_64-unknown-linux-gnu
```

2. Add the `minicov` crate as a dependency to your program:

```toml
[dependencies]
minicov = "0.3"
```

3. Before your program exits, call `minicov::capture_coverage` with a sink (such
   as `Vec<u8>`) and then dump its contents to a file with the `.profraw` extension:

```ignore
fn main() {
    // ...

    let mut coverage = vec![];
    unsafe {
        // Note that this function is not thread-safe! Use a lock if needed.
        minicov::capture_coverage(&mut coverage).unwrap();
    }
    std::fs::write("output.profraw", coverage).unwrap();
}
```

If your program is running on a different system than your build system then
you will need to transfer this file back to your build system.

Sinks must implement the `CoverageWriter` trait. If the default `alloc` feature
is enabled then an implementation is provided for `Vec<u8>`.

4. Use a tool such as [grcov] or llvm-cov to generate a human-readable coverage
   report:

```sh
grcov output.profraw -b ./target/debug/my_program -s . -t html -o cov_report
```

[grcov]: https://github.com/mozilla/grcov

## Profile-guided optimization

The steps for profile-guided optimization are similar. The only difference is the
flags passed in `RUSTFLAGS`:

```sh
# First run to generate profiling information.
export RUSTFLAGS="-Cprofile-generate -Zno-profiler-runtime"
cargo run --target x86_64-unknown-linux-gnu --release

# Post-process the profiling information.
# The rust-profdata tool comes from cargo-binutils.
rust-profdata merge -o output.profdata output.profraw

# Optimized build using PGO. minicov is not needed in this step.
export RUSTFLAGS="-Cprofile-use=output.profdata"
cargo build --target x86_64-unknown-linux-gnu --release
```

## [Change log](CHANGELOG.md)

## License

Licensed under either of:

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
