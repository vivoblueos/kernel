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

#![allow(clippy::float_cmp)]

mod float_to_int;
mod int_to_int;
mod to_float;

use crate::{
    Az, CastFrom, CheckedAs, CheckedCastFrom, OverflowingAs, OverflowingCastFrom, Round,
    SaturatingAs, SaturatingCastFrom, UnwrappedAs, UnwrappedCastFrom, WrappingAs, WrappingCastFrom,
};
use core::{
    f32, f64,
    fmt::Debug,
    ops::{Add, Neg, Not, Shl, Shr, Sub},
};

trait Int
where
    Self: Copy + Debug + Default + Ord,
    Self: Shl<usize, Output = Self> + Shr<usize, Output = Self>,
    Self: Not<Output = Self> + Add<Output = Self> + Sub<Output = Self>,
{
    #[inline]
    fn zero() -> Self {
        Self::default()
    }
    #[inline]
    fn one() -> Self {
        !(!Self::default() << 1)
    }
}

impl<I> Int for I
where
    I: Copy + Debug + Default + Ord,
    I: Shl<usize, Output = I> + Shr<usize, Output = I>,
    I: Not<Output = I> + Add<Output = I> + Sub<Output = I>,
{
}

trait Float
where
    Self: Copy + Debug + PartialOrd + From<i8>,
    Self: Neg<Output = Self> + Add<Output = Self> + Sub<Output = Self>,
{
    fn prec() -> usize;
    fn nan() -> Self;
    fn inf() -> Self;
    fn max() -> Self;
    fn int_shl(int: i8, shl: i8) -> Self;
    fn to_round(self) -> Round<Self>;
}

impl Float for f32 {
    fn prec() -> usize {
        24
    }
    fn nan() -> Self {
        f32::NAN
    }
    fn inf() -> Self {
        f32::INFINITY
    }
    fn max() -> Self {
        f32::MAX
    }
    fn int_shl(int: i8, shl: i8) -> Self {
        f32::from(int) * f32::from(shl).exp2()
    }
    fn to_round(self) -> Round<f32> {
        Round(self)
    }
}

impl Float for f64 {
    fn prec() -> usize {
        53
    }
    fn nan() -> Self {
        f64::NAN
    }
    fn inf() -> Self {
        f64::INFINITY
    }
    fn max() -> Self {
        f64::MAX
    }
    fn int_shl(int: i8, shl: i8) -> Self {
        f64::from(int) * f64::from(shl).exp2()
    }
    fn to_round(self) -> Round<f64> {
        Round(self)
    }
}

#[test]
fn from() {
    assert_eq!(<i8 as CastFrom<u8>>::cast_from(1u8), 1i8);
    assert_eq!(
        <i8 as CheckedCastFrom<u8>>::checked_cast_from(1u8),
        Some(1i8)
    );
    assert_eq!(<i8 as CheckedCastFrom<u8>>::checked_cast_from(255u8), None);
    assert_eq!(
        <i8 as SaturatingCastFrom<u8>>::saturating_cast_from(1u8),
        1i8
    );
    assert_eq!(
        <i8 as SaturatingCastFrom<u8>>::saturating_cast_from(255u8),
        127i8
    );
    assert_eq!(<i8 as WrappingCastFrom<u8>>::wrapping_cast_from(1u8), 1i8);
    assert_eq!(
        <i8 as WrappingCastFrom<u8>>::wrapping_cast_from(255u8),
        -1i8
    );
    assert_eq!(
        <i8 as OverflowingCastFrom<u8>>::overflowing_cast_from(1u8),
        (1i8, false)
    );
    assert_eq!(
        <i8 as OverflowingCastFrom<u8>>::overflowing_cast_from(255u8),
        (-1i8, true)
    );
    assert_eq!(<i8 as UnwrappedCastFrom<u8>>::unwrapped_cast_from(1u8), 1i8);
}

#[test]
fn az() {
    assert_eq!(1.az::<u8>(), 1);
    assert_eq!((-1).checked_as::<u8>(), None);
    assert_eq!(1.checked_as::<u8>(), Some(1));
    assert_eq!((-1).saturating_as::<u8>(), 0);
    assert_eq!(1000.saturating_as::<u8>(), 255);
    assert_eq!((-1).wrapping_as::<u8>(), 255);
    assert_eq!((-1).overflowing_as::<u8>(), (255, true));
    assert_eq!(1.overflowing_as::<u8>(), (1, false));
    assert_eq!(1.unwrapped_as::<u8>(), 1);
}

#[test]
fn borrow_as() {
    use crate::{Cast, CheckedCast, OverflowingCast, SaturatingCast, UnwrappedCast, WrappingCast};
    use core::borrow::Borrow;

    struct I(i32);
    impl Cast<u32> for &'_ I {
        fn cast(self) -> u32 {
            self.0.cast()
        }
    }
    impl CheckedCast<u32> for &'_ I {
        fn checked_cast(self) -> Option<u32> {
            self.0.checked_cast()
        }
    }
    impl SaturatingCast<u32> for &'_ I {
        fn saturating_cast(self) -> u32 {
            self.0.saturating_cast()
        }
    }
    impl WrappingCast<u32> for &'_ I {
        fn wrapping_cast(self) -> u32 {
            self.0.wrapping_cast()
        }
    }
    impl OverflowingCast<u32> for &'_ I {
        fn overflowing_cast(self) -> (u32, bool) {
            self.0.overflowing_cast()
        }
    }
    impl UnwrappedCast<u32> for &'_ I {
        fn unwrapped_cast(self) -> u32 {
            self.0.unwrapped_cast()
        }
    }

    let r = &I(12);
    assert_eq!(r.borrow().az::<u32>(), 12);
    assert_eq!(r.borrow().checked_as::<u32>(), Some(12));
    assert_eq!(r.borrow().saturating_as::<u32>(), 12);
    assert_eq!(r.borrow().borrow().wrapping_as::<u32>(), 12);
    assert_eq!(r.borrow().overflowing_as::<u32>(), (12, false));
    assert_eq!(r.borrow().unwrapped_as::<u32>(), 12);
    let r = &I(-5);
    assert_eq!(r.borrow().checked_as::<u32>(), None);
    assert_eq!(r.borrow().saturating_as::<u32>(), 0);
    assert_eq!(r.borrow().wrapping_as::<u32>(), 5u32.wrapping_neg());
    assert_eq!(
        r.borrow().overflowing_as::<u32>(),
        (5u32.wrapping_neg(), true)
    );
}
