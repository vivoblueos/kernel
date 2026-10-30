# allocator-api2

[![crates](https://img.shields.io/crates/v/allocator-api2.svg?style=for-the-badge&label=allocator-api2)](https://crates.io/crates/allocator-api2)
[![docs](https://img.shields.io/badge/docs.rs-allocator--api2-66c2a5?style=for-the-badge&labelColor=555555&logoColor=white)](https://docs.rs/allocator-api2)
[![actions](https://img.shields.io/github/actions/workflow/status/zakarumych/allocator-api2/badge.yml?branch=main&style=for-the-badge)](https://github.com/zakarumych/allocator-api2/actions/workflows/badge.yml)
[![MIT/Apache](https://img.shields.io/badge/license-MIT%2FApache-blue.svg?style=for-the-badge)](COPYING)
![loc](https://img.shields.io/tokei/lines/github/zakarumych/allocator-api2?style=for-the-badge)

This crate mirrors types and traits from Rust's unstable [`allocator_api`]
The intention of this crate is to serve as a substitution for the actual thing
for libs when built on stable and beta channels.
The target users are library authors who implement allocators or collection types
that use allocators, or anyone else who wants to use [`allocator_api`]

The crate should be frequently updated with a minor version bump.
When [`allocator_api`] is stable, this crate will get version `1.0` and simply
re-export from `core`, `alloc` and `std`.

The code is mostly a verbatim copy from rust repository.
Mostly attributes are removed.

## Usage

This section describes how to use this crate correctly to ensure
compatibility and interoperability on both stable and nightly channels.

If you are writing a library that interacts with an allocator API, you can
add this crate as a dependency and use the types and traits from this
crate instead of the ones in `core` or `alloc`.
This will allow your library to compile on stable and beta channels.

If you wish to be able to use Rust's unstable [`allocator_api`] in place of the
API provided by this crate when your crate is built on the nightly channel,
you can do so by adding a `nightly` feature to your crate and taking the
following steps.

Add the following line to the crate root:

```rust
#![cfg_attr(feature = "nightly", feature(allocator_api))]
```

Next, wherever `allocator-api2` is used, lock the import behind a
`#[cfg(not(feature = "nightly"))]` statement and add an import of the equivalent
unstable [`allocator_api`] item, locked behind a `#[cfg(feature = "nightly")]`
statement. For example:

```rust
#[cfg(not(feature = "nightly"))]
use allocator_api2::alloc::Allocator;
#[cfg(feature = "nightly")]
use std::alloc::Allocator;
```

Alternatively, one could add similar statements to a module, export them with
`pub use` and import the required items from the module, in order to avoid
cluttering the rest of the code with `#[cfg]` statements.

With this setup, the `nightly` feature will, when enabled, demand that the crate
be built on the nightly channel and use the unstable API instead of the one
provided by `allocator-api2`. Note that this is not necessary to build a crate
depending on `allocator-api2` on the nightly channel: Without this setup, the
crate will simply continue to use the API provided by `allocator-api2` even when
built on the nightly channel.

If you depend on a crate that implements the above instructions and exposes
API from the allocator API directly, you may need to enable
`#![feature(allocator_api)]` in your crate when the dependency has the `nightly`
feature enabled.

### Note about older `allocator-api2` versions

In `allocator-api2` versions `0.2` and below, a `nightly` feature was provided
which re-exported the unstable [`allocator_api`] in replacement of the normal
API provided by this crate. This was found to be problematic, as any crate
utilizing `allocator-api2` without providing a feature to enable
`#![feature(allocator_api)]` would be unable to compile if another crate in the
tree enabled the `allocator-api2/nightly` feature. And even when such a feature
was provided, other crates transitively depending on such crates may have had to
pull in their transitive dependencies explicitly in order to enable it. For
these reasons, the `nightly` feature of this crate has been removed. Users of
any of these older versions are urged to update to a newer version of
`allocator-api2` to ensure compatibility with other crates. The instructions
above have been provided as a substitute for those wishing to be able to switch
between using the API provided by this crate and the unstable [`allocator_api`].

# Minimal Supported Rust Version (MSRV)

This crate is guaranteed to compile on stable Rust 1.64 and up.
A feature "fresh-rust" bumps the MSRV to unspecified higher version, but should be compatible with
at least few latest stable releases. The feature enables some additional functionality:

* `CStr` without "std" feature

## License

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contributions

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.


[`allocator_api`]: https://doc.rust-lang.org/unstable-book/library-features/allocator-api.html
