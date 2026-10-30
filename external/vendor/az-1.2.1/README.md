<!-- Copyright © 2019–2021 Trevor Spiteri -->

<!-- Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved. This file is offered
as-is, without any warranty. -->

# Numeric casts

This crate provides casts and checked casts.

# What’s new

### Version 1.2.1 news (2022-07-25)

  * Fix build issue using rustc 1.64.0-nightly under Windows.

### Version 1.2.0 news (2021-11-24)

  * The following traits were added, which can be used for constraints in the
    opposite direction to the other cast traits.
      * [CastFrom][cf-1-2]
      * [CheckedCastFrom][ccf-1-2]
      * [SaturatingCastFrom][scf-1-2]
      * [WrappingCastFrom][wcf-1-2]
      * [OverflowingCastFrom][ocf-1-2]
      * [UnwrappedCastFrom][ucf-1-2]

[ccf-1-2]: https://docs.rs/az/~1.2/az/trait.CheckedCastFrom.html
[cf-1-2]: https://docs.rs/az/~1.2/az/trait.CastFrom.html
[ocf-1-2]: https://docs.rs/az/~1.2/az/trait.OverflowingCastFrom.html
[scf-1-2]: https://docs.rs/az/~1.2/az/trait.SaturatingCastFrom.html
[ucf-1-2]: https://docs.rs/az/~1.2/az/trait.UnwrappedCastFrom.html
[wcf-1-2]: https://docs.rs/az/~1.2/az/trait.WrappingCastFrom.html

### Other releases

Details on other releases can be found in [*RELEASES.md*].

[*RELEASES.md*]: https://gitlab.com/tspiteri/az/blob/master/RELEASES.md

## Quick examples

```rust
use az::{Az, OverflowingAs, WrappingAs};
use core::num::Wrapping;

// Panics on overflow with `debug_assertions`, otherwise wraps
assert_eq!(12i32.az::<u32>(), 12u32);

// Always wraps
let wrapped = 1u32.wrapping_neg();
assert_eq!((-1).wrapping_as::<u32>(), wrapped);
assert_eq!((-1).overflowing_as::<u32>(), (wrapped, true));

// Wrapping can also be obtained using `Wrapping`
assert_eq!((-1).az::<Wrapping<u32>>().0, wrapped);
```

Conversions from floating-point to integers are also supported.
Numbers are rounded towards zero, but the [`Round`] wrapper can be
used to convert floating-point numbers to integers with rounding to
the nearest, with ties rounded to even.

```rust
use az::{Az, CheckedAs, Round, SaturatingAs};
use core::f32;

assert_eq!(15.7.az::<i32>(), 15);
assert_eq!(Round(15.5).az::<i32>(), 16);
assert_eq!(1.5e20.saturating_as::<i32>(), i32::max_value());
assert_eq!(f32::NAN.checked_as::<i32>(), None);
```

## Implementing casts for other types

To provide casts for another type, you should implement the [`Cast`]
trait and if necessary the [`CheckedCast`], [`SaturatingCast`],
[`WrappingCast`], [`OverflowingCast`] and [`UnwrappedCast`] traits.
The [`Az`], [`CheckedAs`], [`SaturatingAs`], [`WrappingAs`],
[`OverflowingAs`] and [`UnwrappedAs`] traits are already implemented
for all types using blanket implementations that make use of the
former traits.

The cast traits can also be implemented for references. This can be
useful for expensive types that are not [`Copy`]. For example if you
have your own integer type that does not implement [`Copy`], you could
implement casts like in the following example. (`I` could be an
expensive type, for example a bignum integer, but for the example it
is only a wrapped [`i32`].)

```rust
use az::{Az, Cast};
use core::borrow::Borrow;

struct I(i32);
impl Cast<i64> for &'_ I {
    fn cast(self) -> i64 { self.0.cast() }
}

let owned = I(12);
assert_eq!(owned.borrow().az::<i64>(), 12);
```

## Using the *az* crate

The *az* crate is available on [crates.io][*az* crate]. To use it in
your crate, add it as a dependency inside [*Cargo.toml*]:

```toml
[dependencies]
az = "1.2"
```

The crate requires rustc version 1.31.0 or later.

## License

This crate is free software: you can redistribute it and/or modify it
under the terms of either

  * the [Apache License, Version 2.0][LICENSE-APACHE] or
  * the [MIT License][LICENSE-MIT]

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache
License, Version 2.0, shall be dual licensed as above, without any
additional terms or conditions.

[*Cargo.toml*]: https://doc.rust-lang.org/cargo/guide/dependencies.html
[*az* crate]: https://crates.io/crates/az
[LICENSE-APACHE]: https://www.apache.org/licenses/LICENSE-2.0
[LICENSE-MIT]: https://opensource.org/licenses/MIT
[`Az`]: https://docs.rs/az/~1.2/az/trait.Az.html
[`Cast`]: https://docs.rs/az/~1.2/az/trait.Cast.html
[`CheckedAs`]: https://docs.rs/az/~1.2/az/trait.CheckedAs.html
[`CheckedCast`]: https://docs.rs/az/~1.2/az/trait.CheckedCast.html
[`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
[`OverflowingAs`]: https://docs.rs/az/~1.2/az/trait.OverflowingAs.html
[`OverflowingCast`]: https://docs.rs/az/~1.2/az/trait.OverflowingCast.html
[`Round`]: https://docs.rs/az/~1.2/az/struct.Round.html
[`SaturatingAs`]: https://docs.rs/az/~1.2/az/trait.SaturatingAs.html
[`SaturatingCast`]: https://docs.rs/az/~1.2/az/trait.SaturatingCast.html
[`UnwrappedAs`]: https://docs.rs/az/~1.2/az/trait.UnwrappedAs.html
[`UnwrappedCast`]: https://docs.rs/az/~1.2/az/trait.UnwrappedCast.html
[`WrappingAs`]: https://docs.rs/az/~1.2/az/trait.WrappingAs.html
[`WrappingCast`]: https://docs.rs/az/~1.2/az/trait.WrappingCast.html
[`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
