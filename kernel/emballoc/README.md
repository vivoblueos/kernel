# `emballoc` — Embedded Memory Allocator

[![crates.io](https://img.shields.io/crates/v/emballoc)](https://crates.io/crates/emballoc)
[![circleci](https://img.shields.io/circleci/build/github/jfrimmel/emballoc)](https://app.circleci.com/pipelines/github/jfrimmel/emballoc)
[![codecov](https://codecov.io/gh/jfrimmel/emballoc/branch/main/graph/badge.svg?token=XU4EG0HGRP)](https://codecov.io/gh/jfrimmel/emballoc)
[![docs.rs](https://img.shields.io/docsrs/emballoc)](https://docs.rs/emballoc)

This repository provides the [`emballoc`](https://crates.io/crates/emballoc) crate: a simple memory allocator developed for usage in small embedded systems.
It is one possible way to support dynamic memory on targets without the standard library, i.e. ones with `#![no_std]`.
This is achieved by providing a type [`Allocator`](https://docs.rs/emballoc/*/emballoc/struct.Allocator.html) which can be registered as the global allocator for the binary.
See the usage description below.

An allocator is a rather critical part of a software project:
when using dynamic memory many operations implicitly can or will allocate, sometimes unexpectedly.
Therefore a misbehaving allocator can "randomly" crash the program in very obscure ways.
As such an allocator has to be well-tested and battle-proven (see more information [here][docu-testing] and a [real world example][gist_hosted-test]).
Furthermore it has to be _simple_: the simpler the algorithm is, the more likely is a correct implementation.

Refer to the [crate-documentation](https://docs.rs/emballoc/) for details on the algorithm and usage hints.

# Usage

Copy the following snippet to your `Cargo.toml` to pull the crate in as one of your dependencies.

```toml
[dependencies.emballoc]
version = "*" # replace with current version from crates.io
```

After that the usage is very simple: just copy the following code to the binary crate of the project.
Substitute the `4096` with the desired heap size in bytes.

```rust
#[global_allocator]
static ALLOCATOR: emballoc::Allocator<4096> = emballoc::Allocator::new();

extern crate alloc;
```

Now the crate can use the `std` collections such as `Vec<T>`, `BTreeMap<K, V>`, etc. together with important types like `Box<T>` and `Rc<T>`.
Note, that things in the `std`-prelude (e.g. `Vec<T>`, `Box<T>`, ...) have to be imported explicitly.

# Why choosing this crate

This crate started as part of an embedded project, but was extracted to make it usable in other projects and for other users.
This sections answers the question:

> Why should you consider using this crate in your project?

- the core algorithm is _simple_ and thus implementation errors are less likely
- rigorous testing is done (see [here][docu-testing])
- crate is free of undefined behavior according to `miri`
- statically determined heap size preventing growing the heap into the stack
- it is used in real-world applications
- it even works on a PC (see [here][gist_hosted-test]), although that is not the primary use case
- supports the stable compiler as there are only stable features used
- has only a single dependency on the popular `spin`-crate (without any transitive dependencies)

I'm glad, if that convinced you, but if you have any questions simply [open an issue](https://github.com/jfrimmel/emballoc/issues/new/choose).

A note to users on systems with advanced memory features like MMUs and MPUs:

- if you have an _memory protection unit_ (MPU) or similar available, you have to configure it yourself as this crate is platform-agnostic.
  An example usage might be to configure it, that reading from and writing to the heap is allowed, but execution is not.
  It is not necessary to surround the heap with guard pages, as this allocator will never read/write outside of the internal byte array.
  However it might be advised to guard the stack, so that it doesn't grow into the heap (or any other variable).
- if you have an (active) _memory management unit_ (MMU), this is likely not the crate for you: it doesn't use any of the important features, which makes it perform much worse than possible.
  Use a proper memory allocator for that use case (one that supports paging, etc.).
  However, if you need dynamic memory before enabling the MMU, this crate certainly is an option.

# Platform support

This crate does not use any platform-specific features (e.g. an MMU or specific instructions), except for the requirement for a atomic compare-and-swap-instruction (CAS), which is widely available.
Therefore this crate works out-of-the-box on most architectures.

Some platforms however don't provide such an instruction (e.g. `thumbv6m-none-eabi` or the RISC-V OpenTitan) or totally lack atomic instructions (e.g. AVR) due to only a single-core nature.
On those platforms, where the CAS instruction is not available, one can use the workaround, that [`spin`][spin-docs] use: you can enable the `portable_atomic`-feature in your `Cargo.toml`, like this:
```toml
[dependencies.emballoc]
version = "*" # replace with current version from crates.io
features = ["portable_atomic"]
```
This enables the use of the `portable_atomic` instead of the `core`-atomics.
This is safe on any platform.

To actually enable atomics support on platforms without hardware support, the `--cfg portable_atomic_unsafe_assume_single_core`-option needs to be explicitly enabled when compiling.
For more details see the [documentation of `spin`][spin-docs].

# Minimum supported Rust version

This crate has a stability guarantee about the compiler version supported.
The so-called minimum supported Rust version is currently set to **1.57** and won't be raised without a proper increase in the semantic version number scheme.
This MSRV is specified in `Cargo.toml` and is tested in CI.

# License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or [http://www.apache.org/licenses/LICENSE-2.0](http://www.apache.org/licenses/LICENSE-2.0))
- MIT license ([LICENSE-MIT](LICENSE-MIT) or [http://opensource.org/licenses/MIT](http://opensource.org/licenses/MIT))

at your option.

[docu-testing]: https://docs.rs/emballoc/latest/emballoc/#testing
[gist_hosted-test]: https://gist.github.com/jfrimmel/61943f9879adfbe760a78efa17a0ecaa
[spin-docs]: https://crates.io/crates/spin#Feature_flags