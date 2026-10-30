// Copyright © 2019–2021 Trevor Spiteri

// This library is free software: you can redistribute it and/or
// modify it under the terms of either
//
//   * the Apache License, Version 2.0 or
//   * the MIT License
//
// at your option.
//
// You should have recieved copies of the Apache License and the MIT
// License along with the library. If not, see
// <https://www.apache.org/licenses/LICENSE-2.0> and
// <https://opensource.org/licenses/MIT>.

/*!
# Numeric casts

This crate provides casts and checked casts.

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
implement casts like in the following example. (The type `I` could be
an expensive type, for example a bignum integer, but for the example
it is only a wrapped [`i32`].)

```rust
use az::{Az, Cast};
use core::borrow::Borrow;

struct I(i32);
impl Cast<i64> for &'_ I {
    fn cast(self) -> i64 { self.0.cast() }
}

let owned = I(12);
assert_eq!((&owned).az::<i64>(), 12);
// borrow can be used if chaining is required
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
*/
#![no_std]
#![warn(missing_docs)]
#![doc(html_root_url = "https://docs.rs/az/~1.2")]
#![doc(test(attr(deny(warnings))))]
#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]

#[cfg(test)]
extern crate std;

mod float;
mod int;
#[cfg(test)]
mod tests;

/**
Used to cast values.

It is normally easier to use the [`Az`] trait instead of this trait.

# Panics

When debug assertions are enabled, this trait’s method panics if the
value does not fit in the destination. When debug assertions are *not*
enabled (usual in release mode), the wrapped value can be returned,
but it is not considered a breaking change if in the future it panics;
if wrapping is required use [`WrappingCast`] instead.

This trait’s method also panics with no debug assertions if the value
does not fit and cannot be wrapped, for example when trying to cast
floating-point ∞ into an integer type.

# Examples

```rust
use az::Cast;
let a: u32 = 5i32.cast();
assert_eq!(a, 5);
assert_eq!(Cast::<u8>::cast(17.1f32), 17);
```
*/
pub trait Cast<Dst> {
    /// Casts the value.
    fn cast(self) -> Dst;
}

/**
Used for checked casts.

This trait’s method returns [`None`] if the value does not fit.

It is normally easier to use the [`CheckedAs`] trait instead of this trait.

# Examples

```rust
use az::CheckedCast;
use core::f32;

let a: Option<u32> = 5i32.checked_cast();
assert_eq!(a, Some(5));
assert_eq!(CheckedCast::<u32>::checked_cast(-5i32), None);
assert_eq!(CheckedCast::<u8>::checked_cast(17.1f32), Some(17));
let b: Option<u8> = f32::NAN.checked_cast();
assert_eq!(b, None);
```
*/
pub trait CheckedCast<Dst> {
    /// Casts the value.
    fn checked_cast(self) -> Option<Dst>;
}

/**
Used to cast into the destination type, saturating if the value does not fit.

It is normally easier to use the [`SaturatingAs`] trait instead of this trait.

# Panics

This trait’s method panics if the value does not fit and saturation
does not make sense, for example when trying to cast floating-point
NaN into an integer type.

# Examples

```rust
use az::SaturatingCast;
let a: u32 = (-1).saturating_cast();
assert_eq!(a, 0);
assert_eq!(SaturatingCast::<u8>::saturating_cast(17.0 + 256.0), 255);
```
*/
pub trait SaturatingCast<Dst> {
    /// Casts the value.
    fn saturating_cast(self) -> Dst;
}

/**
Wrapping cast.

It is normally easier to use the [`WrappingAs`] trait instead of this trait.

# Panics

This trait’s method panics if the value does not fit and cannot be
wrapped, for example when trying to cast floating-point ∞ into an
integer type.

# Examples

```rust
use az::WrappingCast;
let a: u32 = (-1).wrapping_cast();
assert_eq!(a, u32::max_value());
assert_eq!(WrappingCast::<u8>::wrapping_cast(17.0 + 256.0), 17);
```
*/
pub trait WrappingCast<Dst> {
    /// Casts the value.
    fn wrapping_cast(self) -> Dst;
}

/**
Used for overflowing casts.

This trait’s method returns a [tuple] of the value and a [`bool`],
indicating whether an overflow has occurred. On overflow, the wrapped
value is returned.

It is normally easier to use the [`OverflowingAs`] trait instead of this trait.

# Examples

```rust
use az::OverflowingCast;
let a: (u8, bool) = 17i32.overflowing_cast();
assert_eq!(a, (17, false));
assert_eq!(OverflowingCast::<u32>::overflowing_cast(-1), (u32::max_value(), true));
assert_eq!(OverflowingCast::<u8>::overflowing_cast(17.0 + 256.0), (17, true));
```

# Panics

This trait’s method panics if the value does not fit and cannot be
wrapped, for example when trying to cast floating-point ∞ into an
integer type.
*/
pub trait OverflowingCast<Dst> {
    /// Casts the value.
    fn overflowing_cast(self) -> (Dst, bool);
}

/**
Used to cast values, panicking if the value does not fit.

It is normally easier to use the [`UnwrappedAs`] trait instead of this trait.

# Panics

This trait’s method panics if the value does not fit in the
destination, even when debug assertions are not enabled.

# Examples

```rust
use az::UnwrappedCast;
let a: u32 = 5i32.unwrapped_cast();
assert_eq!(a, 5);
assert_eq!(UnwrappedCast::<u8>::unwrapped_cast(17.1f32), 17);
```

The following panics because of overflow.

```rust,should_panic
use az::UnwrappedCast;
let _overflow: u32 = (-5i32).unwrapped_cast();
```
*/
pub trait UnwrappedCast<Dst> {
    /// Casts the value.
    #[cfg_attr(track_caller, track_caller)]
    fn unwrapped_cast(self) -> Dst;
}

/**
Used to cast values.

This trait enables trait constraints for casting in the opposite direction to
[`Cast`].

# Examples

```rust
use az::CastFrom;
trait Tr {
    type Assoc: CastFrom<u8>;
    fn assoc_from_u8(a: u8) -> Self::Assoc {
        CastFrom::cast_from(a)
    }
}
impl Tr for () {
    type Assoc = i8;
}
assert_eq!(<() as Tr>::assoc_from_u8(5u8), 5i8);
```
*/
pub trait CastFrom<Src> {
    /// Casts the value.
    fn cast_from(src: Src) -> Self;
}

impl<Src: Cast<Dst>, Dst> CastFrom<Src> for Dst {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn cast_from(src: Src) -> Self {
        src.cast()
    }
}

/**
Used for checked casts.

This trait enables trait constraints for casting in the opposite direction to
[`CheckedCast`].

# Examples

```rust
use az::CheckedCastFrom;
trait Tr {
    type Assoc: CheckedCastFrom<u8>;
    fn checked_assoc_from_u8(a: u8) -> Option<Self::Assoc> {
        CheckedCastFrom::checked_cast_from(a)
    }
}
impl Tr for () {
    type Assoc = i8;
}
assert_eq!(<() as Tr>::checked_assoc_from_u8(5u8), Some(5i8));
assert_eq!(<() as Tr>::checked_assoc_from_u8(255u8), None);
```
*/
pub trait CheckedCastFrom<Src>: Sized {
    /// Casts the value.
    fn checked_cast_from(src: Src) -> Option<Self>;
}

impl<Src: CheckedCast<Dst>, Dst> CheckedCastFrom<Src> for Dst {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn checked_cast_from(src: Src) -> Option<Self> {
        src.checked_cast()
    }
}

/**
Used to cast, saturating if the value does not fit.

This trait enables trait constraints for casting in the opposite direction to
[`SaturatingCast`].

# Examples

```rust
use az::SaturatingCastFrom;
trait Tr {
    type Assoc: SaturatingCastFrom<u8>;
    fn saturating_assoc_from_u8(a: u8) -> Self::Assoc {
        SaturatingCastFrom::saturating_cast_from(a)
    }
}
impl Tr for () {
    type Assoc = i8;
}
assert_eq!(<() as Tr>::saturating_assoc_from_u8(5u8), 5i8);
assert_eq!(<() as Tr>::saturating_assoc_from_u8(255u8), 127i8);
```
*/
pub trait SaturatingCastFrom<Src> {
    /// Casts the value.
    fn saturating_cast_from(src: Src) -> Self;
}

impl<Src: SaturatingCast<Dst>, Dst> SaturatingCastFrom<Src> for Dst {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn saturating_cast_from(src: Src) -> Self {
        src.saturating_cast()
    }
}

/**
Wrapping cast.

This trait enables trait constraints for casting in the opposite direction to
[`WrappingCast`].

# Examples

```rust
use az::WrappingCastFrom;
trait Tr {
    type Assoc: WrappingCastFrom<u8>;
    fn wrapping_assoc_from_u8(a: u8) -> Self::Assoc {
        WrappingCastFrom::wrapping_cast_from(a)
    }
}
impl Tr for () {
    type Assoc = i8;
}
assert_eq!(<() as Tr>::wrapping_assoc_from_u8(5u8), 5i8);
assert_eq!(<() as Tr>::wrapping_assoc_from_u8(255u8), -1i8);
```
*/
pub trait WrappingCastFrom<Src> {
    /// Casts the value.
    fn wrapping_cast_from(src: Src) -> Self;
}

impl<Src: WrappingCast<Dst>, Dst> WrappingCastFrom<Src> for Dst {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn wrapping_cast_from(src: Src) -> Self {
        src.wrapping_cast()
    }
}

/**
Used for overflowing casts.

This trait enables trait constraints for casting in the opposite direction to
[`OverflowingCast`].

# Examples

```rust
use az::OverflowingCastFrom;
trait Tr {
    type Assoc: OverflowingCastFrom<u8>;
    fn overflowing_assoc_from_u8(a: u8) -> (Self::Assoc, bool) {
        OverflowingCastFrom::overflowing_cast_from(a)
    }
}
impl Tr for () {
    type Assoc = i8;
}
assert_eq!(<() as Tr>::overflowing_assoc_from_u8(5u8), (5i8, false));
assert_eq!(<() as Tr>::overflowing_assoc_from_u8(255u8), (-1i8, true));
```
*/
pub trait OverflowingCastFrom<Src>: Sized {
    /// Casts the value.
    fn overflowing_cast_from(src: Src) -> (Self, bool);
}

impl<Src: OverflowingCast<Dst>, Dst> OverflowingCastFrom<Src> for Dst {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn overflowing_cast_from(src: Src) -> (Self, bool) {
        src.overflowing_cast()
    }
}

/**
Used to cast values, panicking if the value does not fit.

This trait enables trait constraints for casting in the opposite direction to
[`UnwrappedCast`].

# Examples

```rust
use az::UnwrappedCastFrom;
trait Tr {
    type Assoc: UnwrappedCastFrom<u8>;
    fn unwrapped_assoc_from_u8(a: u8) -> Self::Assoc {
        UnwrappedCastFrom::unwrapped_cast_from(a)
    }
}
impl Tr for () {
    type Assoc = i8;
}
assert_eq!(<() as Tr>::unwrapped_assoc_from_u8(5u8), 5i8);
```

The following assertion would panic because of overflow.

```rust, should_panic
# use az::UnwrappedCastFrom;
# trait Tr {
#     type Assoc: UnwrappedCastFrom<u8>;
#     fn unwrapped_assoc_from_u8(a: u8) -> Self::Assoc {
#         UnwrappedCastFrom::unwrapped_cast_from(a)
#     }
# }
# impl Tr for () {
#     type Assoc = i8;
# }
let _overflow = <() as Tr>::unwrapped_assoc_from_u8(255u8);
```

*/
pub trait UnwrappedCastFrom<Src> {
    /// Casts the value.
    fn unwrapped_cast_from(src: Src) -> Self;
}

impl<Src: UnwrappedCast<Dst>, Dst> UnwrappedCastFrom<Src> for Dst {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn unwrapped_cast_from(src: Src) -> Self {
        src.unwrapped_cast()
    }
}

/**
Used to cast values.

This is a convenience trait to enable writing
<code>src.[az][`Az::az`]::&lt;Dst&gt;()</code>. This would not work with
the <code>[Cast][`Cast`]::[cast][`Cast::cast`]</code> method because
the [`Cast`] trait is generic while its [`cast`][`Cast::cast`] method
is not generic.

This trait’s method is suitable for chaining.

If there is an implementation of
<code>[Cast][`Cast`]&lt;Dst&gt;</code> for `&Src` but not for `Src`,
and the variable `src` is of type `Src`, then
<code>src.[az][`Az::az`]::&lt;Dst&gt;()</code> would not work and
<code>(&src).[az][`Az::az`]::&lt;Dst&gt;()</code> is not easy to use with
chaining, but
<code>src.[borrow][`borrow`]().[az][`Az::az`]::&lt;Dst&gt;()</code> works.

# Panics

When debug assertions are enabled, this trait’s method panics if the
value does not fit in the destination. When debug assertions are *not*
enabled (usual in release mode), the wrapped value can be returned,
but it is not considered a breaking change if in the future it panics;
if wrapping is required use [`WrappingAs`] instead.

This trait’s method also panics with no debug assertions if the value
does not fit and cannot be wrapped, for example when trying to cast
floating-point ∞ into an integer type.

# Examples

```rust
use az::Az;
assert_eq!(5i32.az::<u32>(), 5);
assert_eq!(17.1f32.az::<u8>(), 17);
```

The following example shows how this trait can be used when [`Cast`]
is implemented for a reference type.

```rust
use az::{Az, Cast};
use core::borrow::Borrow;
struct I(i32);
impl Cast<i64> for &'_ I {
    fn cast(self) -> i64 { self.0.cast() }
}

let r = &I(-5);
assert_eq!(r.az::<i64>(), -5);
let owned = I(12);
assert_eq!(owned.borrow().az::<i64>(), 12);
```

[`borrow`]: `core::borrow::Borrow::borrow`
*/
pub trait Az {
    /// Casts the value.
    fn az<Dst>(self) -> Dst
    where
        Self: Cast<Dst>;
}

impl<T> Az for T {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn az<Dst>(self) -> Dst
    where
        Self: Cast<Dst>,
    {
        self.cast()
    }
}

/**
Used for checked casts.

This trait’s method returns [`None`] if the value does not fit.

This is a convenience trait to enable writing
<code>src.[checked\_as][`CheckedAs::checked_as`]::&lt;Dst&gt;()</code>. This
would not work with the
<code>[CheckedCast][`CheckedCast`]::[checked\_cast][`CheckedCast::checked_cast`]</code>
method because the [`CheckedCast`] trait is generic while its
[`checked_cast`][`CheckedCast::checked_cast`] method is not generic.

This trait’s method is suitable for chaining.

If there is an implementation of
<code>[CheckedCast][`CheckedCast`]&lt;Dst&gt;</code> for `&Src` but
not for `Src`, and the variable `src` is of type `Src`, then
<code>src.[checked\_as][`CheckedAs::checked_as`]::&lt;Dst&gt;()</code> would not
work and
<code>(&src).[checked\_as][`CheckedAs::checked_as`]::&lt;Dst&gt;()</code> is not
easy to use with chaining, but
<code>src.[borrow][`borrow`]().[checked\_as][`CheckedAs::checked_as`]::&lt;Dst&gt;()</code>
works.

# Examples

```rust
use az::CheckedAs;
use core::f32;

assert_eq!(5i32.checked_as::<u32>(), Some(5));
assert_eq!((-5i32).checked_as::<u32>(), None);
assert_eq!(17.1f32.checked_as::<u8>(), Some(17));
assert_eq!(f32::NAN.checked_as::<u8>(), None);
```

The following example shows how this trait can be used when
[`CheckedCast`] is implemented for a reference type.

```rust
use az::{CheckedAs, CheckedCast};
use core::borrow::Borrow;
struct I(i32);
impl CheckedCast<u32> for &'_ I {
    fn checked_cast(self) -> Option<u32> { self.0.checked_cast() }
}

let r = &I(-5);
assert_eq!(r.checked_as::<u32>(), None);
let owned = I(12);
assert_eq!(owned.borrow().checked_as::<u32>(), Some(12));
```

[`borrow`]: `core::borrow::Borrow::borrow`
*/
pub trait CheckedAs {
    /// Casts the value.
    fn checked_as<Dst>(self) -> Option<Dst>
    where
        Self: CheckedCast<Dst>;
}

impl<T> CheckedAs for T {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn checked_as<Dst>(self) -> Option<Dst>
    where
        Self: CheckedCast<Dst>,
    {
        self.checked_cast()
    }
}

/**
Used to cast into the destination type, saturating if the value does not fit.

This is a convenience trait to enable writing
<code>src.[saturating\_as][`SaturatingAs::saturating_as`]::&lt;Dst&gt;()</code>.
This would not work with the
<code>[SaturatingCast][`SaturatingCast`]::[saturating\_cast][`SaturatingCast::saturating_cast`]</code>
method because the [`SaturatingCast`] trait is generic while its
[`SaturatingCast::saturating_cast`] method is not generic.

This trait’s method is suitable for chaining.

If there is an implementation of
<code>[SaturatingCast][`SaturatingCast`]&lt;Dst&gt;</code> for `&Src`
but not for `Src`, and the variable `src` is of type `Src`, then
<code>src.[saturating\_as][`SaturatingAs::saturating_as`]::&lt;Dst&gt;()</code>
would not work and
<code>(&src).[saturating\_as][`SaturatingAs::saturating_as`]::&lt;Dst&gt;()</code>
is not easy to use with chaining, but
<code>src.[borrow][`borrow`]().[saturating\_as][`SaturatingAs::saturating_as`]::&lt;Dst&gt;()</code>
works.

# Panics

This trait’s method panics if the value does not fit and saturation
does not make sense, for example when trying to cast floating-point
NaN into an integer type.

# Examples

```rust
use az::SaturatingAs;
assert_eq!((-1).saturating_as::<u32>(), 0);
assert_eq!((17.0 + 256.0).saturating_as::<u8>(), 255);
```

The following example shows how this trait can be used when
[`SaturatingCast`] is implemented for a reference type.

```rust
use az::{SaturatingAs, SaturatingCast};
use core::borrow::Borrow;
struct I(i32);
impl SaturatingCast<u32> for &'_ I {
    fn saturating_cast(self) -> u32 { self.0.saturating_cast() }
}

let r = &I(-5);
assert_eq!(r.saturating_as::<u32>(), 0);
let owned = I(12);
assert_eq!(owned.borrow().saturating_as::<u32>(), 12);
```

[`borrow`]: `core::borrow::Borrow::borrow`
*/
pub trait SaturatingAs {
    /// Casts the value.
    fn saturating_as<Dst>(self) -> Dst
    where
        Self: SaturatingCast<Dst>;
}

impl<T> SaturatingAs for T {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn saturating_as<Dst>(self) -> Dst
    where
        Self: SaturatingCast<Dst>,
    {
        self.saturating_cast()
    }
}

/**
Wrapping cast.

This is a convenience trait to enable writing
<code>src.[wrapping\_as][`WrappingAs::wrapping_as`]::&lt;Dst&gt;()</code>. This
would not work with the
<code>[WrappingCast][`WrappingCast`]::[wrapping\_cast][`WrappingCast::wrapping_cast`]</code>
method because the [`WrappingCast`] trait is generic while its
[`WrappingCast::wrapping_cast`] method is not generic.

This trait’s method is suitable for chaining.

If there is an implementation of
<code>[WrappingCast][`WrappingCast`]&lt;Dst&gt;</code> for `&Src` but
not for `Src`, and the variable `src` is of type `Src`, then
<code>src.[wrapping\_as][`WrappingAs::wrapping_as`]::&lt;Dst&gt;()</code> would
not work and
<code>(&src).[wrapping\_as][`WrappingAs::wrapping_as`]::&lt;Dst&gt;()</code> is
not easy to use with chaining, but
<code>src.[borrow][`borrow`]().[wrapping\_as][`WrappingAs::wrapping_as`]::&lt;Dst&gt;()</code>
works.

# Panics

This trait’s method panics if the value does not fit and cannot be
wrapped, for example when trying to cast floating-point ∞ into an
integer type.

# Examples

```rust
use az::WrappingAs;
assert_eq!((-1).wrapping_as::<u32>(), u32::max_value());
assert_eq!((17.0 + 256.0).wrapping_as::<u8>(), 17);
```

The following example shows how this trait can be used when
[`WrappingCast`] is implemented for a reference type.

```rust
use az::{WrappingAs, WrappingCast};
use core::borrow::Borrow;
struct I(i32);
impl WrappingCast<u32> for &'_ I {
    fn wrapping_cast(self) -> u32 { self.0.wrapping_cast() }
}

let r = &I(-5);
assert_eq!(r.wrapping_as::<u32>(), 5u32.wrapping_neg());
let owned = I(12);
assert_eq!(owned.borrow().wrapping_as::<u32>(), 12);
```

[`borrow`]: `core::borrow::Borrow::borrow`
*/
pub trait WrappingAs {
    /// Casts the value.
    fn wrapping_as<Dst>(self) -> Dst
    where
        Self: WrappingCast<Dst>;
}

impl<T> WrappingAs for T {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn wrapping_as<Dst>(self) -> Dst
    where
        Self: WrappingCast<Dst>,
    {
        self.wrapping_cast()
    }
}

/**
Used for overflowing casts.

This trait’s method returns a [tuple] of the value and a [`bool`],
indicating whether an overflow has occurred. On overflow, the wrapped
value is returned.

This is a convenience trait to enable writing
<code>src.[overflowing\_as][`OverflowingAs::overflowing_as`]::&lt;Dst&gt;()</code>.
This would not work with the
<code>[OverflowingCast][`OverflowingCast`]::[overflowing\_cast][`OverflowingCast::overflowing_cast`]</code>
method because the [`OverflowingCast`] trait is generic while its
[`OverflowingCast::overflowing_cast`] method is not generic.

This trait’s method is suitable for chaining.

If there is an implementation of
<code>[OverflowingCast][`OverflowingCast`]&lt;Dst&gt;</code> for
`&Src` but not for `Src`, and the variable `src` is of type `Src`,
then
<code>src.[overflowing\_as][`OverflowingAs::overflowing_as`]::&lt;Dst&gt;()</code>
would not work and
<code>(&src).[overflowing\_as][`OverflowingAs::overflowing_as`]::&lt;Dst&gt;()</code>
is not easy to use with chaining, but
<code>src.[borrow][`borrow`]().[overflowing\_as][`OverflowingAs::overflowing_as`]::&lt;Dst&gt;()</code>
works.

# Panics

This trait’s method panics if the value does not fit and cannot be
wrapped, for example when trying to cast floating-point ∞ into an
integer type.

# Examples

```rust
use az::OverflowingAs;
assert_eq!(17i32.overflowing_as::<u8>(), (17, false));
assert_eq!((-1).overflowing_as::<u32>(), (u32::max_value(), true));
assert_eq!((17.0 + 256.0).overflowing_as::<u8>(), (17, true));
```

The following example shows how this trait can be used when
[`OverflowingCast`] is implemented for a reference type.

```rust
use az::{OverflowingAs, OverflowingCast};
use core::borrow::Borrow;
struct I(i32);
impl OverflowingCast<u32> for &'_ I {
    fn overflowing_cast(self) -> (u32, bool) { self.0.overflowing_cast() }
}

let r = &I(-5);
assert_eq!(r.overflowing_as::<u32>(), (5u32.wrapping_neg(), true));
let owned = I(12);
assert_eq!(owned.borrow().overflowing_as::<u32>(), (12, false));
```

[`borrow`]: `core::borrow::Borrow::borrow`
*/
pub trait OverflowingAs {
    /// Casts the value.
    fn overflowing_as<Dst>(self) -> (Dst, bool)
    where
        Self: OverflowingCast<Dst>;
}

impl<T> OverflowingAs for T {
    #[inline]
    #[cfg_attr(track_caller, track_caller)]
    fn overflowing_as<Dst>(self) -> (Dst, bool)
    where
        Self: OverflowingCast<Dst>,
    {
        self.overflowing_cast()
    }
}

/**
Used to cast values, panicking if the value does not fit.

This is a convenience trait to enable writing
<code>src.[unwrapped\_as][`UnwrappedAs::unwrapped_as`]::&lt;Dst&gt;()</code>.
This would not work with the
<code>[UnwrappedCast][`UnwrappedCast`]::[unwrapped\_cast][`UnwrappedCast::unwrapped_cast`]</code>
method because the [`UnwrappedCast`] trait is generic while its
[`UnwrappedCast::unwrapped_cast`] method is not generic.

This trait’s method is suitable for chaining.

If there is an implementation of
<code>[UnwrappedCast][`UnwrappedCast`]&lt;Dst&gt;</code> for `&Src`
but not for `Src`, and the variable `src` is of type `Src`, then
<code>src.[unwrapped\_as][`UnwrappedAs::unwrapped_as`]::&lt;Dst&gt;()</code>
would not work and
<code>(&src).[unwrapped\_as][`UnwrappedAs::unwrapped_as`]::&lt;Dst&gt;()</code>
is not easy to use with chaining, but
<code>src.[borrow][`borrow`]().[unwrapped\_as][`UnwrappedAs::unwrapped_as`]::&lt;Dst&gt;()</code>
works.

# Panics

This trait’s method panics if the value does not fit in the
destination, even when debug assertions are not enabled.

# Examples

```rust
use az::UnwrappedAs;
assert_eq!(5i32.unwrapped_as::<u32>(), 5);
assert_eq!(17.1f32.unwrapped_as::<u8>(), 17);
```

The following panics because of overflow.

```rust,should_panic
use az::UnwrappedAs;
let _overflow = (-5i32).unwrapped_as::<u32>();
```

The following example shows how this trait can be used when
[`UnwrappedCast`] is implemented for a reference type.

```rust
use az::{UnwrappedAs, UnwrappedCast};
use core::borrow::Borrow;
struct I(i32);
impl UnwrappedCast<i64> for &'_ I {
    fn unwrapped_cast(self) -> i64 { self.0.unwrapped_cast() }
}

let r = &I(-5);
assert_eq!(r.unwrapped_as::<i64>(), -5);
let owned = I(12);
assert_eq!(owned.borrow().unwrapped_as::<i64>(), 12);
```

[`borrow`]: `core::borrow::Borrow::borrow`
*/
pub trait UnwrappedAs {
    /// Casts the value.
    #[cfg_attr(track_caller, track_caller)]
    fn unwrapped_as<Dst>(self) -> Dst
    where
        Self: UnwrappedCast<Dst>;
}

impl<T> UnwrappedAs for T {
    #[inline]
    fn unwrapped_as<Dst>(self) -> Dst
    where
        Self: UnwrappedCast<Dst>,
    {
        self.unwrapped_cast()
    }
}

/// Casts the value.
///
/// # Panics
///
/// When debug assertions are enabled, panics if the value does not
/// fit in the destination. When debug assertions are *not* enabled
/// (usual in release mode), the wrapped value can be returned, but it
/// is not considered a breaking change if in the future it panics; if
/// wrapping is required use [`wrapping_cast`] instead.
///
/// This function also panics with no debug assertions if the value
/// does not fit and cannot be wrapped, for example when trying to
/// cast floating-point ∞ into an integer type.
///
/// # Examples
///
/// ```rust
/// assert_eq!(az::cast::<i32, u32>(5), 5);
/// assert_eq!(az::cast::<f32, u8>(17.1), 17);
/// ```
#[inline]
#[cfg_attr(track_caller, track_caller)]
pub fn cast<Src: Cast<Dst>, Dst>(src: Src) -> Dst {
    src.cast()
}

/// Casts the value, returning [`None`] if the value does not fit.
///
/// # Examples
///
/// ```rust
/// use core::f32;
///
/// assert_eq!(az::checked_cast::<i32, u32>(5), Some(5));
/// assert_eq!(az::checked_cast::<i32, u32>(-5), None);
/// assert_eq!(az::checked_cast::<f32, u8>(17.1), Some(17));
/// assert_eq!(az::checked_cast::<f32, u8>(f32::NAN), None);
/// ```
#[inline]
#[cfg_attr(track_caller, track_caller)]
pub fn checked_cast<Src: CheckedCast<Dst>, Dst>(src: Src) -> Option<Dst> {
    src.checked_cast()
}

/// Casts the value, saturating if the value does not fit.
///
/// # Panics
///
/// Panics if the value does not fit and saturation does not make
/// sense, for example when trying to cast floating-point NaN into an
/// integer type.
///
/// # Examples
///
/// ```rust
/// assert_eq!(az::saturating_cast::<i32, u32>(-1), 0);
/// assert_eq!(az::saturating_cast::<f32, u8>(17.0 + 256.0), 255);
/// ```
#[inline]
#[cfg_attr(track_caller, track_caller)]
pub fn saturating_cast<Src: SaturatingCast<Dst>, Dst>(src: Src) -> Dst {
    src.saturating_cast()
}

/// Casts the value, wrapping on overflow.
///
/// # Panics
///
/// Panics if the value does not fit and cannot be wrapped, for
/// example when trying to cast floating-point ∞ into an integer type.
///
/// # Examples
///
/// ```rust
/// assert_eq!(az::wrapping_cast::<i32, u32>(-1), u32::max_value());
/// assert_eq!(az::wrapping_cast::<f32, u8>(17.0 + 256.0), 17);
/// ```
#[inline]
#[cfg_attr(track_caller, track_caller)]
pub fn wrapping_cast<Src: WrappingCast<Dst>, Dst>(src: Src) -> Dst {
    src.wrapping_cast()
}

/// Overflowing cast.
///
/// Returns a [tuple] of the value and a [`bool`], indicating whether
/// an overflow has occurred. On overflow, the wrapped value is
/// returned.
///
/// # Panics
///
/// Panics if the value does not fit and cannot be wrapped, for
/// example when trying to cast floating-point ∞ into an integer type.
///
/// # Examples
///
/// ```rust
/// assert_eq!(az::overflowing_cast::<i32, u32>(-1), (u32::max_value(), true));
/// assert_eq!(az::overflowing_cast::<f32, u8>(17.0 + 256.0), (17, true));
/// ```
#[inline]
#[cfg_attr(track_caller, track_caller)]
pub fn overflowing_cast<Src: OverflowingCast<Dst>, Dst>(src: Src) -> (Dst, bool) {
    src.overflowing_cast()
}

/// Casts the value, panicking if the value does not fit.
///
/// # Panics
///
/// Panics if the value does not fit in the destination, even when
/// debug assertions are not enabled.
///
/// # Examples
///
/// ```rust
/// assert_eq!(az::unwrapped_cast::<i32, u32>(5), 5);
/// assert_eq!(az::unwrapped_cast::<f32, u8>(17.1), 17);
/// ```
///
/// The following panics because of overflow.
///
/// ```rust,should_panic
/// let _overflow = az::unwrapped_cast::<i32, u32>(-5);
/// ```
#[inline]
#[cfg_attr(track_caller, track_caller)]
pub fn unwrapped_cast<Src: UnwrappedCast<Dst>, Dst>(src: Src) -> Dst {
    src.unwrapped_cast()
}

/// Used to convert floating-point numbers to integers with rounding
/// to the nearest, with ties rounded to even.
///
/// The underlying value can be retrieved through the `.0` index.
///
/// # Examples
///
/// ```rust
/// use az::Round;
/// assert_eq!(az::cast::<_, i32>(Round(0.4)), 0);
/// assert_eq!(az::cast::<_, i32>(Round(0.6)), 1);
/// // ties rounded to even
/// assert_eq!(az::cast::<_, i32>(Round(-0.5)), 0);
/// assert_eq!(az::cast::<_, i32>(Round(-1.5)), -2);
/// ```
#[repr(transparent)]
#[derive(Clone, Copy, Default, Eq, PartialEq, PartialOrd, Ord)]
pub struct Round<T>(pub T);
