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

use crate::{
    cast, checked_cast, overflowing_cast, saturating_cast, tests::Int, unwrapped_cast,
    wrapping_cast, Cast, CheckedCast, OverflowingCast, SaturatingCast, UnwrappedCast, WrappingCast,
};
use core::{mem, num::Wrapping};

fn bool_to_nonwrapping_int<Dst: Int>()
where
    bool: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let zero = Dst::zero();
    let one = Dst::one();

    assert_eq!(cast(false), zero);
    assert_eq!(cast(true), one);

    assert_eq!(checked_cast(false), Some(zero));
    assert_eq!(checked_cast(true), Some(one));

    assert_eq!(saturating_cast(false), zero);
    assert_eq!(saturating_cast(true), one);

    assert_eq!(wrapping_cast(false), zero);
    assert_eq!(wrapping_cast(true), one);

    assert_eq!(overflowing_cast(false), (zero, false));
    assert_eq!(overflowing_cast(true), (one, false));

    assert_eq!(unwrapped_cast(false), zero);
    assert_eq!(unwrapped_cast(true), one);
}

fn bool_to_wrapping_int<Dst: Int>()
where
    bool: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let zero = Wrapping(wrapping_cast(false));
    let one = Wrapping(wrapping_cast(true));

    assert_eq!(cast(false), zero);
    assert_eq!(cast(true), one);

    assert_eq!(checked_cast(false), Some(zero));
    assert_eq!(checked_cast(true), Some(one));

    assert_eq!(unwrapped_cast(false), zero);
    assert_eq!(unwrapped_cast(true), one);
}

fn bool_to_single_int<Dst: Int>()
where
    bool: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    bool_to_nonwrapping_int::<Dst>();
    bool_to_wrapping_int::<Dst>();
}

#[test]
fn bool_to_int() {
    bool_to_single_int::<i8>();
    bool_to_single_int::<i16>();
    bool_to_single_int::<i32>();
    bool_to_single_int::<i64>();
    bool_to_single_int::<i128>();
    bool_to_single_int::<isize>();

    bool_to_single_int::<u8>();
    bool_to_single_int::<u16>();
    bool_to_single_int::<u32>();
    bool_to_single_int::<u64>();
    bool_to_single_int::<u128>();
    bool_to_single_int::<usize>();
}

fn signed_to_smaller_nonwrapping_signed<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits > dst_nbits);

    let src_z00 = Src::zero();
    let src_m01 = !src_z00;
    let src_m08 = src_m01 << (dst_nbits - 1);
    let src_m09 = src_m08 + src_m01;
    let src_m10 = src_m01 << dst_nbits;
    let src_p01 = Src::one();
    let src_p07 = !src_m08;
    let src_p08 = src_p07 + src_p01;
    let src_p0f = src_p07 + src_p08;
    let src_p10 = src_p01 << dst_nbits;

    let dst_z0 = Dst::zero();
    let dst_m1 = !dst_z0;
    let dst_m8 = dst_m1 << (dst_nbits - 1);
    let dst_p1 = Dst::one();
    let dst_p7 = !dst_m8;

    assert_eq!(cast(src_m08), dst_m8);
    assert_eq!(cast(src_m01), dst_m1);
    assert_eq!(cast(src_z00), dst_z0);
    assert_eq!(cast(src_p01), dst_p1);
    assert_eq!(cast(src_p07), dst_p7);

    assert_eq!(checked_cast(src_m10), None);
    assert_eq!(checked_cast(src_m09), None);
    assert_eq!(checked_cast(src_m08), Some(dst_m8));
    assert_eq!(checked_cast(src_m01), Some(dst_m1));
    assert_eq!(checked_cast(src_z00), Some(dst_z0));
    assert_eq!(checked_cast(src_p01), Some(dst_p1));
    assert_eq!(checked_cast(src_p07), Some(dst_p7));
    assert_eq!(checked_cast(src_p08), None);
    assert_eq!(checked_cast(src_p0f), None);
    assert_eq!(checked_cast(src_p10), None);

    assert_eq!(saturating_cast(src_m10), dst_m8);
    assert_eq!(saturating_cast(src_m09), dst_m8);
    assert_eq!(saturating_cast(src_m08), dst_m8);
    assert_eq!(saturating_cast(src_m01), dst_m1);
    assert_eq!(saturating_cast(src_z00), dst_z0);
    assert_eq!(saturating_cast(src_p01), dst_p1);
    assert_eq!(saturating_cast(src_p07), dst_p7);
    assert_eq!(saturating_cast(src_p08), dst_p7);
    assert_eq!(saturating_cast(src_p0f), dst_p7);
    assert_eq!(saturating_cast(src_p10), dst_p7);

    assert_eq!(wrapping_cast(src_m10), dst_z0);
    assert_eq!(wrapping_cast(src_m09), dst_p7);
    assert_eq!(wrapping_cast(src_m08), dst_m8);
    assert_eq!(wrapping_cast(src_m01), dst_m1);
    assert_eq!(wrapping_cast(src_z00), dst_z0);
    assert_eq!(wrapping_cast(src_p01), dst_p1);
    assert_eq!(wrapping_cast(src_p07), dst_p7);
    assert_eq!(wrapping_cast(src_p08), dst_m8);
    assert_eq!(wrapping_cast(src_p0f), dst_m1);
    assert_eq!(wrapping_cast(src_p10), dst_z0);

    assert_eq!(overflowing_cast(src_m10), (dst_z0, true));
    assert_eq!(overflowing_cast(src_m09), (dst_p7, true));
    assert_eq!(overflowing_cast(src_m08), (dst_m8, false));
    assert_eq!(overflowing_cast(src_m01), (dst_m1, false));
    assert_eq!(overflowing_cast(src_z00), (dst_z0, false));
    assert_eq!(overflowing_cast(src_p01), (dst_p1, false));
    assert_eq!(overflowing_cast(src_p07), (dst_p7, false));
    assert_eq!(overflowing_cast(src_p08), (dst_m8, true));
    assert_eq!(overflowing_cast(src_p0f), (dst_m1, true));
    assert_eq!(overflowing_cast(src_p10), (dst_z0, true));

    assert_eq!(unwrapped_cast(src_m08), dst_m8);
    assert_eq!(unwrapped_cast(src_m01), dst_m1);
    assert_eq!(unwrapped_cast(src_z00), dst_z0);
    assert_eq!(unwrapped_cast(src_p01), dst_p1);
    assert_eq!(unwrapped_cast(src_p07), dst_p7);
}

fn signed_to_larger_same_nonwrapping_signed<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits <= dst_nbits);

    let src_z0 = Src::zero();
    let src_m1 = !src_z0;
    let src_m8 = src_m1 << (src_nbits - 1);
    let src_p1 = Src::one();
    let src_p7 = !src_m8;

    let dst_z00 = Dst::zero();
    let dst_m01 = !dst_z00;
    let dst_m08 = dst_m01 << (src_nbits - 1);
    let dst_p01 = Dst::one();
    let dst_p07 = !dst_m08;

    assert_eq!(cast(src_m8), dst_m08);
    assert_eq!(cast(src_m1), dst_m01);
    assert_eq!(cast(src_z0), dst_z00);
    assert_eq!(cast(src_p1), dst_p01);
    assert_eq!(cast(src_p7), dst_p07);

    assert_eq!(checked_cast(src_m8), Some(dst_m08));
    assert_eq!(checked_cast(src_m1), Some(dst_m01));
    assert_eq!(checked_cast(src_z0), Some(dst_z00));
    assert_eq!(checked_cast(src_p1), Some(dst_p01));
    assert_eq!(checked_cast(src_p7), Some(dst_p07));

    assert_eq!(saturating_cast(src_m8), dst_m08);
    assert_eq!(saturating_cast(src_m1), dst_m01);
    assert_eq!(saturating_cast(src_z0), dst_z00);
    assert_eq!(saturating_cast(src_p1), dst_p01);
    assert_eq!(saturating_cast(src_p7), dst_p07);

    assert_eq!(wrapping_cast(src_m8), dst_m08);
    assert_eq!(wrapping_cast(src_m1), dst_m01);
    assert_eq!(wrapping_cast(src_z0), dst_z00);
    assert_eq!(wrapping_cast(src_p1), dst_p01);
    assert_eq!(wrapping_cast(src_p7), dst_p07);

    assert_eq!(overflowing_cast(src_m8), (dst_m08, false));
    assert_eq!(overflowing_cast(src_m1), (dst_m01, false));
    assert_eq!(overflowing_cast(src_z0), (dst_z00, false));
    assert_eq!(overflowing_cast(src_p1), (dst_p01, false));
    assert_eq!(overflowing_cast(src_p7), (dst_p07, false));

    assert_eq!(unwrapped_cast(src_m8), dst_m08);
    assert_eq!(unwrapped_cast(src_m1), dst_m01);
    assert_eq!(unwrapped_cast(src_z0), dst_z00);
    assert_eq!(unwrapped_cast(src_p1), dst_p01);
    assert_eq!(unwrapped_cast(src_p7), dst_p07);
}

fn signed_to_smaller_wrapping_signed<Src: Int, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits > dst_nbits);

    let src_z00 = Src::zero();
    let src_m01 = !src_z00;
    let src_m08 = src_m01 << (dst_nbits - 1);
    let src_m09 = src_m08 + src_m01;
    let src_m10 = src_m01 << dst_nbits;
    let src_p01 = Src::one();
    let src_p07 = !src_m08;
    let src_p08 = src_p07 + src_p01;
    let src_p0f = src_p07 + src_p08;
    let src_p10 = src_p01 << dst_nbits;

    let dst_z0 = Wrapping(wrapping_cast(src_z00));
    let dst_m1 = Wrapping(wrapping_cast(src_m01));
    let dst_m8 = Wrapping(wrapping_cast(src_m08));
    let dst_p1 = Wrapping(wrapping_cast(src_p01));
    let dst_p7 = Wrapping(wrapping_cast(src_p07));

    assert_eq!(cast(src_m10), dst_z0);
    assert_eq!(cast(src_m09), dst_p7);
    assert_eq!(cast(src_m08), dst_m8);
    assert_eq!(cast(src_m01), dst_m1);
    assert_eq!(cast(src_z00), dst_z0);
    assert_eq!(cast(src_p01), dst_p1);
    assert_eq!(cast(src_p07), dst_p7);
    assert_eq!(cast(src_p08), dst_m8);
    assert_eq!(cast(src_p0f), dst_m1);
    assert_eq!(cast(src_p10), dst_z0);

    assert_eq!(checked_cast(src_m10), Some(dst_z0));
    assert_eq!(checked_cast(src_m09), Some(dst_p7));
    assert_eq!(checked_cast(src_m08), Some(dst_m8));
    assert_eq!(checked_cast(src_m01), Some(dst_m1));
    assert_eq!(checked_cast(src_z00), Some(dst_z0));
    assert_eq!(checked_cast(src_p01), Some(dst_p1));
    assert_eq!(checked_cast(src_p07), Some(dst_p7));
    assert_eq!(checked_cast(src_p08), Some(dst_m8));
    assert_eq!(checked_cast(src_p0f), Some(dst_m1));
    assert_eq!(checked_cast(src_p10), Some(dst_z0));

    assert_eq!(unwrapped_cast(src_m10), dst_z0);
    assert_eq!(unwrapped_cast(src_m09), dst_p7);
    assert_eq!(unwrapped_cast(src_m08), dst_m8);
    assert_eq!(unwrapped_cast(src_m01), dst_m1);
    assert_eq!(unwrapped_cast(src_z00), dst_z0);
    assert_eq!(unwrapped_cast(src_p01), dst_p1);
    assert_eq!(unwrapped_cast(src_p07), dst_p7);
    assert_eq!(unwrapped_cast(src_p08), dst_m8);
    assert_eq!(unwrapped_cast(src_p0f), dst_m1);
    assert_eq!(unwrapped_cast(src_p10), dst_z0);
}

fn signed_to_larger_same_wrapping_signed<Src: Int, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits <= dst_nbits);

    let src_z0 = Src::zero();
    let src_m1 = !src_z0;
    let src_m8 = src_m1 << (src_nbits - 1);
    let src_p1 = Src::one();
    let src_p7 = !src_m8;

    let dst_z00 = Wrapping(wrapping_cast(src_z0));
    let dst_m01 = Wrapping(wrapping_cast(src_m1));
    let dst_m08 = Wrapping(wrapping_cast(src_m8));
    let dst_p01 = Wrapping(wrapping_cast(src_p1));
    let dst_p07 = Wrapping(wrapping_cast(src_p7));

    assert_eq!(cast(src_m8), dst_m08);
    assert_eq!(cast(src_m1), dst_m01);
    assert_eq!(cast(src_z0), dst_z00);
    assert_eq!(cast(src_p1), dst_p01);
    assert_eq!(cast(src_p7), dst_p07);

    assert_eq!(checked_cast(src_m8), Some(dst_m08));
    assert_eq!(checked_cast(src_m1), Some(dst_m01));
    assert_eq!(checked_cast(src_z0), Some(dst_z00));
    assert_eq!(checked_cast(src_p1), Some(dst_p01));
    assert_eq!(checked_cast(src_p7), Some(dst_p07));

    assert_eq!(unwrapped_cast(src_m8), dst_m08);
    assert_eq!(unwrapped_cast(src_m1), dst_m01);
    assert_eq!(unwrapped_cast(src_z0), dst_z00);
    assert_eq!(unwrapped_cast(src_p1), dst_p01);
    assert_eq!(unwrapped_cast(src_p7), dst_p07);
}

fn signed_to_smaller_signed<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    signed_to_smaller_nonwrapping_signed::<Src, Dst>();
    signed_to_smaller_wrapping_signed::<Src, Dst>();
}

fn signed_to_larger_same_signed<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    signed_to_larger_same_nonwrapping_signed::<Src, Dst>();
    signed_to_larger_same_wrapping_signed::<Src, Dst>();
}

#[test]
fn signed_to_signed() {
    signed_to_larger_same_signed::<i8, i8>();
    signed_to_larger_same_signed::<i8, i16>();
    signed_to_larger_same_signed::<i8, i32>();
    signed_to_larger_same_signed::<i8, i64>();
    signed_to_larger_same_signed::<i8, i128>();
    signed_to_larger_same_signed::<i8, isize>();

    signed_to_smaller_signed::<i16, i8>();
    signed_to_larger_same_signed::<i16, i16>();
    signed_to_larger_same_signed::<i16, i32>();
    signed_to_larger_same_signed::<i16, i64>();
    signed_to_larger_same_signed::<i16, i128>();
    signed_to_larger_same_signed::<i16, isize>();

    signed_to_smaller_signed::<i32, i8>();
    signed_to_smaller_signed::<i32, i16>();
    signed_to_larger_same_signed::<i32, i32>();
    signed_to_larger_same_signed::<i32, i64>();
    signed_to_larger_same_signed::<i32, i128>();
    if cfg!(target_pointer_width = "16") {
        signed_to_smaller_signed::<i32, isize>();
    } else {
        signed_to_larger_same_signed::<i32, isize>();
    }

    signed_to_smaller_signed::<i64, i8>();
    signed_to_smaller_signed::<i64, i16>();
    signed_to_smaller_signed::<i64, i32>();
    signed_to_larger_same_signed::<i64, i64>();
    signed_to_larger_same_signed::<i64, i128>();
    if cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32") {
        signed_to_smaller_signed::<i64, isize>();
    } else {
        signed_to_larger_same_signed::<i64, isize>();
    }

    signed_to_smaller_signed::<i128, i8>();
    signed_to_smaller_signed::<i128, i16>();
    signed_to_smaller_signed::<i128, i32>();
    signed_to_smaller_signed::<i128, i64>();
    signed_to_larger_same_signed::<i128, i128>();
    if cfg!(target_pointer_width = "16")
        || cfg!(target_pointer_width = "32")
        || cfg!(target_pointer_width = "64")
    {
        signed_to_smaller_signed::<i128, isize>();
    } else {
        signed_to_larger_same_signed::<i32, isize>();
    }

    signed_to_smaller_signed::<isize, i8>();
    if cfg!(target_pointer_width = "16") {
        signed_to_larger_same_signed::<isize, i16>();
        signed_to_larger_same_signed::<isize, i32>();
        signed_to_larger_same_signed::<isize, i64>();
    } else if cfg!(target_pointer_width = "32") {
        signed_to_smaller_signed::<isize, i16>();
        signed_to_larger_same_signed::<isize, i32>();
        signed_to_larger_same_signed::<isize, i64>();
    } else if cfg!(target_pointer_width = "64") {
        signed_to_smaller_signed::<isize, i16>();
        signed_to_smaller_signed::<isize, i32>();
        signed_to_larger_same_signed::<isize, i64>();
    } else if cfg!(target_pointer_width = "128") {
        signed_to_smaller_signed::<isize, i16>();
        signed_to_smaller_signed::<isize, i32>();
        signed_to_smaller_signed::<isize, i64>();
    }
    signed_to_larger_same_signed::<isize, i128>();
    signed_to_larger_same_signed::<isize, isize>();
}

fn signed_to_smaller_nonwrapping_unsigned<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits > dst_nbits);

    let src_z00 = Src::zero();
    let src_m01 = !src_z00;
    let src_m08 = src_m01 << (dst_nbits - 1);
    let src_m09 = src_m08 + src_m01;
    let src_m10 = src_m01 << dst_nbits;
    let src_p01 = Src::one();
    let src_p07 = !src_m08;
    let src_p08 = src_p07 + src_p01;
    let src_p0f = src_p07 + src_p08;
    let src_p10 = src_p01 << dst_nbits;

    let dst_z0 = Dst::zero();
    let dst_p1 = Dst::one();
    let dst_p7 = !(!dst_z0 << (dst_nbits - 1));
    let dst_p8 = dst_p7 + dst_p1;
    let dst_pf = dst_p7 + dst_p8;

    assert_eq!(cast(src_z00), dst_z0);
    assert_eq!(cast(src_p01), dst_p1);
    assert_eq!(cast(src_p07), dst_p7);
    assert_eq!(cast(src_p08), dst_p8);
    assert_eq!(cast(src_p0f), dst_pf);

    assert_eq!(checked_cast(src_m10), None);
    assert_eq!(checked_cast(src_m09), None);
    assert_eq!(checked_cast(src_m08), None);
    assert_eq!(checked_cast(src_m01), None);
    assert_eq!(checked_cast(src_z00), Some(dst_z0));
    assert_eq!(checked_cast(src_p01), Some(dst_p1));
    assert_eq!(checked_cast(src_p07), Some(dst_p7));
    assert_eq!(checked_cast(src_p08), Some(dst_p8));
    assert_eq!(checked_cast(src_p0f), Some(dst_pf));
    assert_eq!(checked_cast(src_p10), None);

    assert_eq!(saturating_cast(src_m10), dst_z0);
    assert_eq!(saturating_cast(src_m09), dst_z0);
    assert_eq!(saturating_cast(src_m08), dst_z0);
    assert_eq!(saturating_cast(src_m01), dst_z0);
    assert_eq!(saturating_cast(src_z00), dst_z0);
    assert_eq!(saturating_cast(src_p01), dst_p1);
    assert_eq!(saturating_cast(src_p07), dst_p7);
    assert_eq!(saturating_cast(src_p08), dst_p8);
    assert_eq!(saturating_cast(src_p0f), dst_pf);
    assert_eq!(saturating_cast(src_p10), dst_pf);

    assert_eq!(wrapping_cast(src_m10), dst_z0);
    assert_eq!(wrapping_cast(src_m09), dst_p7);
    assert_eq!(wrapping_cast(src_m08), dst_p8);
    assert_eq!(wrapping_cast(src_m01), dst_pf);
    assert_eq!(wrapping_cast(src_z00), dst_z0);
    assert_eq!(wrapping_cast(src_p01), dst_p1);
    assert_eq!(wrapping_cast(src_p07), dst_p7);
    assert_eq!(wrapping_cast(src_p08), dst_p8);
    assert_eq!(wrapping_cast(src_p0f), dst_pf);
    assert_eq!(wrapping_cast(src_p10), dst_z0);

    assert_eq!(overflowing_cast(src_m10), (dst_z0, true));
    assert_eq!(overflowing_cast(src_m09), (dst_p7, true));
    assert_eq!(overflowing_cast(src_m08), (dst_p8, true));
    assert_eq!(overflowing_cast(src_m01), (dst_pf, true));
    assert_eq!(overflowing_cast(src_z00), (dst_z0, false));
    assert_eq!(overflowing_cast(src_p01), (dst_p1, false));
    assert_eq!(overflowing_cast(src_p07), (dst_p7, false));
    assert_eq!(overflowing_cast(src_p08), (dst_p8, false));
    assert_eq!(overflowing_cast(src_p0f), (dst_pf, false));
    assert_eq!(overflowing_cast(src_p10), (dst_z0, true));

    assert_eq!(unwrapped_cast(src_z00), dst_z0);
    assert_eq!(unwrapped_cast(src_p01), dst_p1);
    assert_eq!(unwrapped_cast(src_p07), dst_p7);
    assert_eq!(unwrapped_cast(src_p08), dst_p8);
    assert_eq!(unwrapped_cast(src_p0f), dst_pf);
}

fn signed_to_larger_same_nonwrapping_unsigned<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits <= dst_nbits);

    let src_z0 = Src::zero();
    let src_m1 = !src_z0;
    let src_m8 = src_m1 << (src_nbits - 1);
    let src_p1 = Src::one();
    let src_p7 = !src_m8;

    let dst_z00 = Dst::zero();
    let dst_p01 = Dst::one();
    let dst_p07 = !(!dst_z00 << (src_nbits - 1));
    let dst_pf8 = !dst_p07;
    let dst_pff = !dst_z00;

    assert_eq!(cast(src_z0), dst_z00);
    assert_eq!(cast(src_p1), dst_p01);
    assert_eq!(cast(src_p7), dst_p07);

    assert_eq!(checked_cast(src_m8), None);
    assert_eq!(checked_cast(src_m1), None);
    assert_eq!(checked_cast(src_z0), Some(dst_z00));
    assert_eq!(checked_cast(src_p1), Some(dst_p01));
    assert_eq!(checked_cast(src_p7), Some(dst_p07));

    assert_eq!(saturating_cast(src_m8), dst_z00);
    assert_eq!(saturating_cast(src_m1), dst_z00);
    assert_eq!(saturating_cast(src_z0), dst_z00);
    assert_eq!(saturating_cast(src_p1), dst_p01);
    assert_eq!(saturating_cast(src_p7), dst_p07);

    assert_eq!(wrapping_cast(src_m8), dst_pf8);
    assert_eq!(wrapping_cast(src_m1), dst_pff);
    assert_eq!(wrapping_cast(src_z0), dst_z00);
    assert_eq!(wrapping_cast(src_p1), dst_p01);
    assert_eq!(wrapping_cast(src_p7), dst_p07);

    assert_eq!(overflowing_cast(src_m8), (dst_pf8, true));
    assert_eq!(overflowing_cast(src_m1), (dst_pff, true));
    assert_eq!(overflowing_cast(src_z0), (dst_z00, false));
    assert_eq!(overflowing_cast(src_p1), (dst_p01, false));
    assert_eq!(overflowing_cast(src_p7), (dst_p07, false));

    assert_eq!(unwrapped_cast(src_z0), dst_z00);
    assert_eq!(unwrapped_cast(src_p1), dst_p01);
    assert_eq!(unwrapped_cast(src_p7), dst_p07);
}

fn signed_to_smaller_wrapping_unsigned<Src: Int, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits > dst_nbits);

    let src_z00 = Src::zero();
    let src_m01 = !src_z00;
    let src_m08 = src_m01 << (dst_nbits - 1);
    let src_m09 = src_m08 + src_m01;
    let src_m10 = src_m01 << dst_nbits;
    let src_p01 = Src::one();
    let src_p07 = !src_m08;
    let src_p08 = src_p07 + src_p01;
    let src_p0f = src_p07 + src_p08;
    let src_p10 = src_p01 << dst_nbits;

    let dst_z0 = Wrapping(wrapping_cast(src_z00));
    let dst_p1 = Wrapping(wrapping_cast(src_p01));
    let dst_p7 = Wrapping(wrapping_cast(src_p07));
    let dst_p8 = Wrapping(wrapping_cast(src_p08));
    let dst_pf = Wrapping(wrapping_cast(src_p0f));

    assert_eq!(cast(src_m10), dst_z0);
    assert_eq!(cast(src_m09), dst_p7);
    assert_eq!(cast(src_m08), dst_p8);
    assert_eq!(cast(src_m01), dst_pf);
    assert_eq!(cast(src_z00), dst_z0);
    assert_eq!(cast(src_p01), dst_p1);
    assert_eq!(cast(src_p07), dst_p7);
    assert_eq!(cast(src_p08), dst_p8);
    assert_eq!(cast(src_p0f), dst_pf);
    assert_eq!(cast(src_p10), dst_z0);

    assert_eq!(checked_cast(src_m10), Some(dst_z0));
    assert_eq!(checked_cast(src_m09), Some(dst_p7));
    assert_eq!(checked_cast(src_m08), Some(dst_p8));
    assert_eq!(checked_cast(src_m01), Some(dst_pf));
    assert_eq!(checked_cast(src_z00), Some(dst_z0));
    assert_eq!(checked_cast(src_p01), Some(dst_p1));
    assert_eq!(checked_cast(src_p07), Some(dst_p7));
    assert_eq!(checked_cast(src_p08), Some(dst_p8));
    assert_eq!(checked_cast(src_p0f), Some(dst_pf));
    assert_eq!(checked_cast(src_p10), Some(dst_z0));

    assert_eq!(unwrapped_cast(src_m10), dst_z0);
    assert_eq!(unwrapped_cast(src_m09), dst_p7);
    assert_eq!(unwrapped_cast(src_m08), dst_p8);
    assert_eq!(unwrapped_cast(src_m01), dst_pf);
    assert_eq!(unwrapped_cast(src_z00), dst_z0);
    assert_eq!(unwrapped_cast(src_p01), dst_p1);
    assert_eq!(unwrapped_cast(src_p07), dst_p7);
    assert_eq!(unwrapped_cast(src_p08), dst_p8);
    assert_eq!(unwrapped_cast(src_p0f), dst_pf);
    assert_eq!(unwrapped_cast(src_p10), dst_z0);
}

fn signed_to_larger_same_wrapping_unsigned<Src: Int, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits <= dst_nbits);

    let src_z0 = Src::zero();
    let src_m1 = !src_z0;
    let src_m8 = src_m1 << (src_nbits - 1);
    let src_p1 = Src::one();
    let src_p7 = !src_m8;

    let dst_z00 = Wrapping(wrapping_cast(src_z0));
    let dst_p01 = Wrapping(wrapping_cast(src_p1));
    let dst_p07 = Wrapping(wrapping_cast(src_p7));
    let dst_pf8 = Wrapping(wrapping_cast(src_m8));
    let dst_pff = Wrapping(wrapping_cast(src_m1));

    assert_eq!(cast(src_m8), dst_pf8);
    assert_eq!(cast(src_m1), dst_pff);
    assert_eq!(cast(src_z0), dst_z00);
    assert_eq!(cast(src_p1), dst_p01);
    assert_eq!(cast(src_p7), dst_p07);

    assert_eq!(checked_cast(src_m8), Some(dst_pf8));
    assert_eq!(checked_cast(src_m1), Some(dst_pff));
    assert_eq!(checked_cast(src_z0), Some(dst_z00));
    assert_eq!(checked_cast(src_p1), Some(dst_p01));
    assert_eq!(checked_cast(src_p7), Some(dst_p07));

    assert_eq!(unwrapped_cast(src_m8), dst_pf8);
    assert_eq!(unwrapped_cast(src_m1), dst_pff);
    assert_eq!(unwrapped_cast(src_z0), dst_z00);
    assert_eq!(unwrapped_cast(src_p1), dst_p01);
    assert_eq!(unwrapped_cast(src_p7), dst_p07);
}

fn signed_to_smaller_unsigned<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    signed_to_smaller_nonwrapping_unsigned::<Src, Dst>();
    signed_to_smaller_wrapping_unsigned::<Src, Dst>();
}

fn signed_to_larger_same_unsigned<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    signed_to_larger_same_nonwrapping_unsigned::<Src, Dst>();
    signed_to_larger_same_wrapping_unsigned::<Src, Dst>();
}

#[test]
fn signed_to_unsigned() {
    signed_to_larger_same_unsigned::<i8, u8>();
    signed_to_larger_same_unsigned::<i8, u16>();
    signed_to_larger_same_unsigned::<i8, u32>();
    signed_to_larger_same_unsigned::<i8, u64>();
    signed_to_larger_same_unsigned::<i8, u128>();
    signed_to_larger_same_unsigned::<i8, usize>();

    signed_to_smaller_unsigned::<i16, u8>();
    signed_to_larger_same_unsigned::<i16, u16>();
    signed_to_larger_same_unsigned::<i16, u32>();
    signed_to_larger_same_unsigned::<i16, u64>();
    signed_to_larger_same_unsigned::<i16, u128>();
    signed_to_larger_same_unsigned::<i16, usize>();

    signed_to_smaller_unsigned::<i32, u8>();
    signed_to_smaller_unsigned::<i32, u16>();
    signed_to_larger_same_unsigned::<i32, u32>();
    signed_to_larger_same_unsigned::<i32, u64>();
    signed_to_larger_same_unsigned::<i32, u128>();
    if cfg!(target_pointer_width = "16") {
        signed_to_smaller_unsigned::<i32, usize>();
    } else {
        signed_to_larger_same_unsigned::<i32, usize>();
    }

    signed_to_smaller_unsigned::<i64, u8>();
    signed_to_smaller_unsigned::<i64, u16>();
    signed_to_smaller_unsigned::<i64, u32>();
    signed_to_larger_same_unsigned::<i64, u64>();
    signed_to_larger_same_unsigned::<i64, u128>();
    if cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32") {
        signed_to_smaller_unsigned::<i64, usize>();
    } else {
        signed_to_larger_same_unsigned::<i64, usize>();
    }

    signed_to_smaller_unsigned::<i128, u8>();
    signed_to_smaller_unsigned::<i128, u16>();
    signed_to_smaller_unsigned::<i128, u32>();
    signed_to_smaller_unsigned::<i128, u64>();
    signed_to_larger_same_unsigned::<i128, u128>();
    if cfg!(target_pointer_width = "16")
        || cfg!(target_pointer_width = "32")
        || cfg!(target_pointer_width = "64")
    {
        signed_to_smaller_unsigned::<i128, usize>();
    } else {
        signed_to_larger_same_unsigned::<i128, usize>();
    }

    signed_to_smaller_unsigned::<isize, u8>();
    if cfg!(target_pointer_width = "16") {
        signed_to_larger_same_unsigned::<isize, u16>();
        signed_to_larger_same_unsigned::<isize, u32>();
        signed_to_larger_same_unsigned::<isize, u64>();
    } else if cfg!(target_pointer_width = "32") {
        signed_to_smaller_unsigned::<isize, u16>();
        signed_to_larger_same_unsigned::<isize, u32>();
        signed_to_larger_same_unsigned::<isize, u64>();
    } else if cfg!(target_pointer_width = "64") {
        signed_to_smaller_unsigned::<isize, u16>();
        signed_to_smaller_unsigned::<isize, u32>();
        signed_to_larger_same_unsigned::<isize, u64>();
    } else if cfg!(target_pointer_width = "128") {
        signed_to_smaller_unsigned::<isize, u16>();
        signed_to_smaller_unsigned::<isize, u32>();
        signed_to_smaller_unsigned::<isize, u64>();
    }
    signed_to_larger_same_unsigned::<isize, u128>();
    signed_to_larger_same_unsigned::<isize, usize>();
}

fn unsigned_to_smaller_nonwrapping_signed<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits > dst_nbits);

    let src_z00 = Src::zero();
    let src_p01 = Src::one();
    let src_p07 = !(!src_z00 << (dst_nbits - 1));
    let src_p08 = src_p07 + src_p01;
    let src_p0f = src_p07 + src_p08;
    let src_p10 = src_p01 << dst_nbits;

    let dst_z0 = Dst::zero();
    let dst_m1 = !dst_z0;
    let dst_m8 = dst_m1 << (dst_nbits - 1);
    let dst_p1 = Dst::one();
    let dst_p7 = !dst_m8;

    assert_eq!(cast(src_z00), dst_z0);
    assert_eq!(cast(src_p01), dst_p1);
    assert_eq!(cast(src_p07), dst_p7);

    assert_eq!(checked_cast(src_z00), Some(dst_z0));
    assert_eq!(checked_cast(src_p01), Some(dst_p1));
    assert_eq!(checked_cast(src_p07), Some(dst_p7));
    assert_eq!(checked_cast(src_p08), None);
    assert_eq!(checked_cast(src_p0f), None);
    assert_eq!(checked_cast(src_p10), None);

    assert_eq!(saturating_cast(src_z00), dst_z0);
    assert_eq!(saturating_cast(src_p01), dst_p1);
    assert_eq!(saturating_cast(src_p07), dst_p7);
    assert_eq!(saturating_cast(src_p08), dst_p7);
    assert_eq!(saturating_cast(src_p0f), dst_p7);
    assert_eq!(saturating_cast(src_p10), dst_p7);

    assert_eq!(wrapping_cast(src_z00), dst_z0);
    assert_eq!(wrapping_cast(src_p01), dst_p1);
    assert_eq!(wrapping_cast(src_p07), dst_p7);
    assert_eq!(wrapping_cast(src_p08), dst_m8);
    assert_eq!(wrapping_cast(src_p0f), dst_m1);
    assert_eq!(wrapping_cast(src_p10), dst_z0);

    assert_eq!(overflowing_cast(src_z00), (dst_z0, false));
    assert_eq!(overflowing_cast(src_p01), (dst_p1, false));
    assert_eq!(overflowing_cast(src_p07), (dst_p7, false));
    assert_eq!(overflowing_cast(src_p08), (dst_m8, true));
    assert_eq!(overflowing_cast(src_p0f), (dst_m1, true));
    assert_eq!(overflowing_cast(src_p10), (dst_z0, true));

    assert_eq!(unwrapped_cast(src_z00), dst_z0);
    assert_eq!(unwrapped_cast(src_p01), dst_p1);
    assert_eq!(unwrapped_cast(src_p07), dst_p7);
}

fn unsigned_to_same_nonwrapping_signed<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits == dst_nbits);

    let src_z0 = Src::zero();
    let src_p1 = Src::one();
    let src_p7 = !(!src_z0 << (src_nbits - 1));
    let src_p8 = src_p7 + src_p1;
    let src_pf = src_p7 + src_p8;

    let dst_z0 = Dst::zero();
    let dst_m1 = !dst_z0;
    let dst_m8 = dst_m1 << (dst_nbits - 1);
    let dst_p1 = Dst::one();
    let dst_p7 = !dst_m8;

    assert_eq!(cast(src_z0), dst_z0);
    assert_eq!(cast(src_p1), dst_p1);
    assert_eq!(cast(src_p7), dst_p7);

    assert_eq!(checked_cast(src_z0), Some(dst_z0));
    assert_eq!(checked_cast(src_p1), Some(dst_p1));
    assert_eq!(checked_cast(src_p7), Some(dst_p7));
    assert_eq!(checked_cast(src_p8), None);
    assert_eq!(checked_cast(src_pf), None);

    assert_eq!(saturating_cast(src_z0), dst_z0);
    assert_eq!(saturating_cast(src_p1), dst_p1);
    assert_eq!(saturating_cast(src_p7), dst_p7);
    assert_eq!(saturating_cast(src_p8), dst_p7);
    assert_eq!(saturating_cast(src_pf), dst_p7);

    assert_eq!(wrapping_cast(src_z0), dst_z0);
    assert_eq!(wrapping_cast(src_p1), dst_p1);
    assert_eq!(wrapping_cast(src_p7), dst_p7);
    assert_eq!(wrapping_cast(src_p8), dst_m8);
    assert_eq!(wrapping_cast(src_pf), dst_m1);

    assert_eq!(overflowing_cast(src_z0), (dst_z0, false));
    assert_eq!(overflowing_cast(src_p1), (dst_p1, false));
    assert_eq!(overflowing_cast(src_p7), (dst_p7, false));
    assert_eq!(overflowing_cast(src_p8), (dst_m8, true));
    assert_eq!(overflowing_cast(src_pf), (dst_m1, true));

    assert_eq!(unwrapped_cast(src_z0), dst_z0);
    assert_eq!(unwrapped_cast(src_p1), dst_p1);
    assert_eq!(unwrapped_cast(src_p7), dst_p7);
}

fn unsigned_to_larger_nonwrapping_signed<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits < dst_nbits);

    let src_z0 = Src::zero();
    let src_p1 = Src::one();
    let src_p7 = !(!src_z0 << (src_nbits - 1));
    let src_p8 = src_p7 + src_p1;
    let src_pf = src_p7 + src_p8;

    let dst_z00 = Dst::zero();
    let dst_p01 = Dst::one();
    let dst_p07 = !(!dst_z00 << (src_nbits - 1));
    let dst_p08 = dst_p07 + dst_p01;
    let dst_p0f = dst_p07 + dst_p08;

    assert_eq!(cast(src_z0), dst_z00);
    assert_eq!(cast(src_p1), dst_p01);
    assert_eq!(cast(src_p7), dst_p07);
    assert_eq!(cast(src_p8), dst_p08);
    assert_eq!(cast(src_pf), dst_p0f);

    assert_eq!(checked_cast(src_z0), Some(dst_z00));
    assert_eq!(checked_cast(src_p1), Some(dst_p01));
    assert_eq!(checked_cast(src_p7), Some(dst_p07));
    assert_eq!(checked_cast(src_p8), Some(dst_p08));
    assert_eq!(checked_cast(src_pf), Some(dst_p0f));

    assert_eq!(saturating_cast(src_z0), dst_z00);
    assert_eq!(saturating_cast(src_p1), dst_p01);
    assert_eq!(saturating_cast(src_p7), dst_p07);
    assert_eq!(saturating_cast(src_p8), dst_p08);
    assert_eq!(saturating_cast(src_pf), dst_p0f);

    assert_eq!(wrapping_cast(src_z0), dst_z00);
    assert_eq!(wrapping_cast(src_p1), dst_p01);
    assert_eq!(wrapping_cast(src_p7), dst_p07);
    assert_eq!(wrapping_cast(src_p8), dst_p08);
    assert_eq!(wrapping_cast(src_pf), dst_p0f);

    assert_eq!(overflowing_cast(src_z0), (dst_z00, false));
    assert_eq!(overflowing_cast(src_p1), (dst_p01, false));
    assert_eq!(overflowing_cast(src_p7), (dst_p07, false));
    assert_eq!(overflowing_cast(src_p8), (dst_p08, false));
    assert_eq!(overflowing_cast(src_pf), (dst_p0f, false));

    assert_eq!(unwrapped_cast(src_z0), dst_z00);
    assert_eq!(unwrapped_cast(src_p1), dst_p01);
    assert_eq!(unwrapped_cast(src_p7), dst_p07);
    assert_eq!(unwrapped_cast(src_p8), dst_p08);
    assert_eq!(unwrapped_cast(src_pf), dst_p0f);
}

fn unsigned_to_smaller_wrapping_signed<Src: Int, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits > dst_nbits);

    let src_z00 = Src::zero();
    let src_p01 = Src::one();
    let src_p07 = !(!src_z00 << (dst_nbits - 1));
    let src_p08 = src_p07 + src_p01;
    let src_p0f = src_p07 + src_p08;
    let src_p10 = src_p01 << dst_nbits;

    let dst_z0 = Wrapping(wrapping_cast(src_z00));
    let dst_m1 = Wrapping(wrapping_cast(src_p0f));
    let dst_m8 = Wrapping(wrapping_cast(src_p08));
    let dst_p1 = Wrapping(wrapping_cast(src_p01));
    let dst_p7 = Wrapping(wrapping_cast(src_p07));

    assert_eq!(cast(src_z00), dst_z0);
    assert_eq!(cast(src_p01), dst_p1);
    assert_eq!(cast(src_p07), dst_p7);
    assert_eq!(cast(src_p08), dst_m8);
    assert_eq!(cast(src_p0f), dst_m1);
    assert_eq!(cast(src_p10), dst_z0);

    assert_eq!(checked_cast(src_z00), Some(dst_z0));
    assert_eq!(checked_cast(src_p01), Some(dst_p1));
    assert_eq!(checked_cast(src_p07), Some(dst_p7));
    assert_eq!(checked_cast(src_p08), Some(dst_m8));
    assert_eq!(checked_cast(src_p0f), Some(dst_m1));
    assert_eq!(checked_cast(src_p10), Some(dst_z0));

    assert_eq!(unwrapped_cast(src_z00), dst_z0);
    assert_eq!(unwrapped_cast(src_p01), dst_p1);
    assert_eq!(unwrapped_cast(src_p07), dst_p7);
    assert_eq!(unwrapped_cast(src_p08), dst_m8);
    assert_eq!(unwrapped_cast(src_p0f), dst_m1);
    assert_eq!(unwrapped_cast(src_p10), dst_z0);
}

fn unsigned_to_same_wrapping_signed<Src: Int, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits == dst_nbits);

    let src_z0 = Src::zero();
    let src_p1 = Src::one();
    let src_p7 = !(!src_z0 << (src_nbits - 1));
    let src_p8 = src_p7 + src_p1;
    let src_pf = src_p7 + src_p8;

    let dst_z0 = Wrapping(wrapping_cast(src_z0));
    let dst_m1 = Wrapping(wrapping_cast(src_pf));
    let dst_m8 = Wrapping(wrapping_cast(src_p8));
    let dst_p1 = Wrapping(wrapping_cast(src_p1));
    let dst_p7 = Wrapping(wrapping_cast(src_p7));

    assert_eq!(cast(src_z0), dst_z0);
    assert_eq!(cast(src_p1), dst_p1);
    assert_eq!(cast(src_p7), dst_p7);
    assert_eq!(cast(src_p8), dst_m8);
    assert_eq!(cast(src_pf), dst_m1);

    assert_eq!(checked_cast(src_z0), Some(dst_z0));
    assert_eq!(checked_cast(src_p1), Some(dst_p1));
    assert_eq!(checked_cast(src_p7), Some(dst_p7));
    assert_eq!(checked_cast(src_p8), Some(dst_m8));
    assert_eq!(checked_cast(src_pf), Some(dst_m1));

    assert_eq!(unwrapped_cast(src_z0), dst_z0);
    assert_eq!(unwrapped_cast(src_p1), dst_p1);
    assert_eq!(unwrapped_cast(src_p7), dst_p7);
    assert_eq!(unwrapped_cast(src_p8), dst_m8);
    assert_eq!(unwrapped_cast(src_pf), dst_m1);
}

fn unsigned_to_larger_wrapping_signed<Src: Int, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits < dst_nbits);

    let src_z0 = Src::zero();
    let src_p1 = Src::one();
    let src_p7 = !(!src_z0 << (src_nbits - 1));
    let src_p8 = src_p7 + src_p1;
    let src_pf = src_p7 + src_p8;

    let dst_z00 = Wrapping(wrapping_cast(src_z0));
    let dst_p01 = Wrapping(wrapping_cast(src_p1));
    let dst_p07 = Wrapping(wrapping_cast(src_p7));
    let dst_p08 = Wrapping(wrapping_cast(src_p8));
    let dst_p0f = Wrapping(wrapping_cast(src_pf));

    assert_eq!(cast(src_z0), dst_z00);
    assert_eq!(cast(src_p1), dst_p01);
    assert_eq!(cast(src_p7), dst_p07);
    assert_eq!(cast(src_p8), dst_p08);
    assert_eq!(cast(src_pf), dst_p0f);

    assert_eq!(checked_cast(src_z0), Some(dst_z00));
    assert_eq!(checked_cast(src_p1), Some(dst_p01));
    assert_eq!(checked_cast(src_p7), Some(dst_p07));
    assert_eq!(checked_cast(src_p8), Some(dst_p08));
    assert_eq!(checked_cast(src_pf), Some(dst_p0f));

    assert_eq!(unwrapped_cast(src_z0), dst_z00);
    assert_eq!(unwrapped_cast(src_p1), dst_p01);
    assert_eq!(unwrapped_cast(src_p7), dst_p07);
    assert_eq!(unwrapped_cast(src_p8), dst_p08);
    assert_eq!(unwrapped_cast(src_pf), dst_p0f);
}

fn unsigned_to_smaller_signed<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    unsigned_to_smaller_nonwrapping_signed::<Src, Dst>();
    unsigned_to_smaller_wrapping_signed::<Src, Dst>();
}

fn unsigned_to_same_signed<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    unsigned_to_same_nonwrapping_signed::<Src, Dst>();
    unsigned_to_same_wrapping_signed::<Src, Dst>();
}

fn unsigned_to_larger_signed<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    unsigned_to_larger_nonwrapping_signed::<Src, Dst>();
    unsigned_to_larger_wrapping_signed::<Src, Dst>();
}

#[test]
fn unsigned_to_signed() {
    unsigned_to_same_signed::<u8, i8>();
    unsigned_to_larger_signed::<u8, i16>();
    unsigned_to_larger_signed::<u8, i32>();
    unsigned_to_larger_signed::<u8, i64>();
    unsigned_to_larger_signed::<u8, i128>();
    unsigned_to_larger_signed::<u8, isize>();

    unsigned_to_smaller_signed::<u16, i8>();
    unsigned_to_same_signed::<u16, i16>();
    unsigned_to_larger_signed::<u16, i32>();
    unsigned_to_larger_signed::<u16, i64>();
    unsigned_to_larger_signed::<u16, i128>();
    if cfg!(target_pointer_width = "16") {
        unsigned_to_same_signed::<u16, isize>();
    } else {
        unsigned_to_larger_signed::<u16, isize>();
    }

    unsigned_to_smaller_signed::<u32, i8>();
    unsigned_to_smaller_signed::<u32, i16>();
    unsigned_to_same_signed::<u32, i32>();
    unsigned_to_larger_signed::<u32, i64>();
    unsigned_to_larger_signed::<u32, i128>();
    if cfg!(target_pointer_width = "16") {
        unsigned_to_smaller_signed::<u32, isize>();
    } else if cfg!(target_pointer_width = "32") {
        unsigned_to_same_signed::<u32, isize>();
    } else {
        unsigned_to_larger_signed::<u32, isize>();
    }

    unsigned_to_smaller_signed::<u64, i8>();
    unsigned_to_smaller_signed::<u64, i16>();
    unsigned_to_smaller_signed::<u64, i32>();
    unsigned_to_same_signed::<u64, i64>();
    unsigned_to_larger_signed::<u64, i128>();
    if cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32") {
        unsigned_to_smaller_signed::<u64, isize>();
    } else if cfg!(target_pointer_width = "64") {
        unsigned_to_same_signed::<u64, isize>();
    } else {
        unsigned_to_larger_signed::<u64, isize>();
    }

    unsigned_to_smaller_signed::<u128, i8>();
    unsigned_to_smaller_signed::<u128, i16>();
    unsigned_to_smaller_signed::<u128, i32>();
    unsigned_to_smaller_signed::<u128, i64>();
    unsigned_to_same_signed::<u128, i128>();
    if cfg!(target_pointer_width = "16")
        || cfg!(target_pointer_width = "32")
        || cfg!(target_pointer_width = "64")
    {
        unsigned_to_smaller_signed::<u128, isize>();
    } else {
        unsigned_to_same_signed::<u128, isize>();
    }

    unsigned_to_smaller_signed::<usize, i8>();
    if cfg!(target_pointer_width = "16") {
        unsigned_to_same_signed::<usize, i16>();
        unsigned_to_larger_signed::<usize, i32>();
        unsigned_to_larger_signed::<usize, i64>();
        unsigned_to_larger_signed::<usize, i128>();
    } else if cfg!(target_pointer_width = "32") {
        unsigned_to_smaller_signed::<usize, i16>();
        unsigned_to_same_signed::<usize, i32>();
        unsigned_to_larger_signed::<usize, i64>();
        unsigned_to_larger_signed::<usize, i128>();
    } else if cfg!(target_pointer_width = "64") {
        unsigned_to_smaller_signed::<usize, i16>();
        unsigned_to_smaller_signed::<usize, i32>();
        unsigned_to_same_signed::<usize, i64>();
        unsigned_to_larger_signed::<usize, i128>();
    } else if cfg!(target_pointer_width = "128") {
        unsigned_to_smaller_signed::<usize, i16>();
        unsigned_to_smaller_signed::<usize, i32>();
        unsigned_to_smaller_signed::<usize, i64>();
        unsigned_to_same_signed::<usize, i128>();
    }
    unsigned_to_same_signed::<usize, isize>();
}

fn unsigned_to_smaller_nonwrapping_unsigned<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits > dst_nbits);

    let src_z00 = Src::zero();
    let src_p01 = Src::one();
    let src_p07 = !(!src_z00 << (dst_nbits - 1));
    let src_p08 = src_p07 + src_p01;
    let src_p0f = src_p07 + src_p08;
    let src_p10 = src_p01 << dst_nbits;

    let dst_z0 = Dst::zero();
    let dst_p1 = Dst::one();
    let dst_p7 = !(!dst_z0 << (dst_nbits - 1));
    let dst_p8 = dst_p7 + dst_p1;
    let dst_pf = dst_p7 + dst_p8;

    assert_eq!(cast(src_z00), dst_z0);
    assert_eq!(cast(src_p01), dst_p1);
    assert_eq!(cast(src_p07), dst_p7);
    assert_eq!(cast(src_p08), dst_p8);
    assert_eq!(cast(src_p0f), dst_pf);

    assert_eq!(checked_cast(src_z00), Some(dst_z0));
    assert_eq!(checked_cast(src_p01), Some(dst_p1));
    assert_eq!(checked_cast(src_p07), Some(dst_p7));
    assert_eq!(checked_cast(src_p08), Some(dst_p8));
    assert_eq!(checked_cast(src_p0f), Some(dst_pf));
    assert_eq!(checked_cast(src_p10), None);

    assert_eq!(saturating_cast(src_z00), dst_z0);
    assert_eq!(saturating_cast(src_p01), dst_p1);
    assert_eq!(saturating_cast(src_p07), dst_p7);
    assert_eq!(saturating_cast(src_p08), dst_p8);
    assert_eq!(saturating_cast(src_p0f), dst_pf);
    assert_eq!(saturating_cast(src_p10), dst_pf);

    assert_eq!(wrapping_cast(src_z00), dst_z0);
    assert_eq!(wrapping_cast(src_p01), dst_p1);
    assert_eq!(wrapping_cast(src_p07), dst_p7);
    assert_eq!(wrapping_cast(src_p08), dst_p8);
    assert_eq!(wrapping_cast(src_p0f), dst_pf);
    assert_eq!(wrapping_cast(src_p10), dst_z0);

    assert_eq!(overflowing_cast(src_z00), (dst_z0, false));
    assert_eq!(overflowing_cast(src_p01), (dst_p1, false));
    assert_eq!(overflowing_cast(src_p07), (dst_p7, false));
    assert_eq!(overflowing_cast(src_p08), (dst_p8, false));
    assert_eq!(overflowing_cast(src_p0f), (dst_pf, false));
    assert_eq!(overflowing_cast(src_p10), (dst_z0, true));

    assert_eq!(unwrapped_cast(src_z00), dst_z0);
    assert_eq!(unwrapped_cast(src_p01), dst_p1);
    assert_eq!(unwrapped_cast(src_p07), dst_p7);
    assert_eq!(unwrapped_cast(src_p08), dst_p8);
    assert_eq!(unwrapped_cast(src_p0f), dst_pf);
}

fn unsigned_to_larger_same_nonwrapping_unsigned<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits <= dst_nbits);

    let src_z0 = Src::zero();
    let src_p1 = Src::one();
    let src_p7 = !(!src_z0 << (src_nbits - 1));
    let src_p8 = src_p7 + src_p1;
    let src_pf = src_p7 + src_p8;

    let dst_z00 = Dst::zero();
    let dst_p01 = Dst::one();
    let dst_p07 = !(!dst_z00 << (src_nbits - 1));
    let dst_p08 = dst_p07 + dst_p01;
    let dst_p0f = dst_p07 + dst_p08;

    assert_eq!(cast(src_z0), dst_z00);
    assert_eq!(cast(src_p1), dst_p01);
    assert_eq!(cast(src_p7), dst_p07);
    assert_eq!(cast(src_p8), dst_p08);
    assert_eq!(cast(src_pf), dst_p0f);

    assert_eq!(checked_cast(src_z0), Some(dst_z00));
    assert_eq!(checked_cast(src_p1), Some(dst_p01));
    assert_eq!(checked_cast(src_p7), Some(dst_p07));
    assert_eq!(checked_cast(src_p8), Some(dst_p08));
    assert_eq!(checked_cast(src_pf), Some(dst_p0f));

    assert_eq!(saturating_cast(src_z0), dst_z00);
    assert_eq!(saturating_cast(src_p1), dst_p01);
    assert_eq!(saturating_cast(src_p7), dst_p07);
    assert_eq!(saturating_cast(src_p8), dst_p08);
    assert_eq!(saturating_cast(src_pf), dst_p0f);

    assert_eq!(wrapping_cast(src_z0), dst_z00);
    assert_eq!(wrapping_cast(src_p1), dst_p01);
    assert_eq!(wrapping_cast(src_p7), dst_p07);
    assert_eq!(wrapping_cast(src_p8), dst_p08);
    assert_eq!(wrapping_cast(src_pf), dst_p0f);

    assert_eq!(overflowing_cast(src_z0), (dst_z00, false));
    assert_eq!(overflowing_cast(src_p1), (dst_p01, false));
    assert_eq!(overflowing_cast(src_p7), (dst_p07, false));
    assert_eq!(overflowing_cast(src_p8), (dst_p08, false));
    assert_eq!(overflowing_cast(src_pf), (dst_p0f, false));

    assert_eq!(unwrapped_cast(src_z0), dst_z00);
    assert_eq!(unwrapped_cast(src_p1), dst_p01);
    assert_eq!(unwrapped_cast(src_p7), dst_p07);
    assert_eq!(unwrapped_cast(src_p8), dst_p08);
    assert_eq!(unwrapped_cast(src_pf), dst_p0f);
}

fn unsigned_to_smaller_wrapping_unsigned<Src: Int, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits > dst_nbits);

    let src_z00 = Src::zero();
    let src_p01 = Src::one();
    let src_p07 = !(!src_z00 << (dst_nbits - 1));
    let src_p08 = src_p07 + src_p01;
    let src_p0f = src_p07 + src_p08;
    let src_p10 = src_p01 << dst_nbits;

    let dst_z0 = Wrapping(wrapping_cast(src_z00));
    let dst_p1 = Wrapping(wrapping_cast(src_p01));
    let dst_p7 = Wrapping(wrapping_cast(src_p07));
    let dst_p8 = Wrapping(wrapping_cast(src_p08));
    let dst_pf = Wrapping(wrapping_cast(src_p0f));

    assert_eq!(cast(src_z00), dst_z0);
    assert_eq!(cast(src_p01), dst_p1);
    assert_eq!(cast(src_p07), dst_p7);
    assert_eq!(cast(src_p08), dst_p8);
    assert_eq!(cast(src_p0f), dst_pf);
    assert_eq!(cast(src_p10), dst_z0);

    assert_eq!(checked_cast(src_z00), Some(dst_z0));
    assert_eq!(checked_cast(src_p01), Some(dst_p1));
    assert_eq!(checked_cast(src_p07), Some(dst_p7));
    assert_eq!(checked_cast(src_p08), Some(dst_p8));
    assert_eq!(checked_cast(src_p0f), Some(dst_pf));
    assert_eq!(checked_cast(src_p10), Some(dst_z0));

    assert_eq!(unwrapped_cast(src_z00), dst_z0);
    assert_eq!(unwrapped_cast(src_p01), dst_p1);
    assert_eq!(unwrapped_cast(src_p07), dst_p7);
    assert_eq!(unwrapped_cast(src_p08), dst_p8);
    assert_eq!(unwrapped_cast(src_p0f), dst_pf);
    assert_eq!(unwrapped_cast(src_p10), dst_z0);
}

fn unsigned_to_larger_same_wrapping_unsigned<Src: Int, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;
    assert!(src_nbits <= dst_nbits);

    let src_z0 = Src::zero();
    let src_p1 = Src::one();
    let src_p7 = !(!src_z0 << (src_nbits - 1));
    let src_p8 = src_p7 + src_p1;
    let src_pf = src_p7 + src_p8;

    let dst_z00 = Wrapping(wrapping_cast(src_z0));
    let dst_p01 = Wrapping(wrapping_cast(src_p1));
    let dst_p07 = Wrapping(wrapping_cast(src_p7));
    let dst_p08 = Wrapping(wrapping_cast(src_p8));
    let dst_p0f = Wrapping(wrapping_cast(src_pf));

    assert_eq!(cast(src_z0), dst_z00);
    assert_eq!(cast(src_p1), dst_p01);
    assert_eq!(cast(src_p7), dst_p07);
    assert_eq!(cast(src_p8), dst_p08);
    assert_eq!(cast(src_pf), dst_p0f);

    assert_eq!(checked_cast(src_z0), Some(dst_z00));
    assert_eq!(checked_cast(src_p1), Some(dst_p01));
    assert_eq!(checked_cast(src_p7), Some(dst_p07));
    assert_eq!(checked_cast(src_p8), Some(dst_p08));
    assert_eq!(checked_cast(src_pf), Some(dst_p0f));

    assert_eq!(unwrapped_cast(src_z0), dst_z00);
    assert_eq!(unwrapped_cast(src_p1), dst_p01);
    assert_eq!(unwrapped_cast(src_p7), dst_p07);
    assert_eq!(unwrapped_cast(src_p8), dst_p08);
    assert_eq!(unwrapped_cast(src_pf), dst_p0f);
}

fn unsigned_to_smaller_unsigned<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    unsigned_to_smaller_nonwrapping_unsigned::<Src, Dst>();
    unsigned_to_smaller_wrapping_unsigned::<Src, Dst>();
}

fn unsigned_to_larger_same_unsigned<Src: Int, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    unsigned_to_larger_same_nonwrapping_unsigned::<Src, Dst>();
    unsigned_to_larger_same_wrapping_unsigned::<Src, Dst>();
}

#[test]
fn unsigned_to_unsigned() {
    unsigned_to_larger_same_unsigned::<u8, u8>();
    unsigned_to_larger_same_unsigned::<u8, u16>();
    unsigned_to_larger_same_unsigned::<u8, u32>();
    unsigned_to_larger_same_unsigned::<u8, u64>();
    unsigned_to_larger_same_unsigned::<u8, u128>();
    unsigned_to_larger_same_unsigned::<u8, usize>();

    unsigned_to_smaller_unsigned::<u16, u8>();
    unsigned_to_larger_same_unsigned::<u16, u16>();
    unsigned_to_larger_same_unsigned::<u16, u32>();
    unsigned_to_larger_same_unsigned::<u16, u64>();
    unsigned_to_larger_same_unsigned::<u16, u128>();
    unsigned_to_larger_same_unsigned::<u16, usize>();

    unsigned_to_smaller_unsigned::<u32, u8>();
    unsigned_to_smaller_unsigned::<u32, u16>();
    unsigned_to_larger_same_unsigned::<u32, u32>();
    unsigned_to_larger_same_unsigned::<u32, u64>();
    unsigned_to_larger_same_unsigned::<u32, u128>();
    if cfg!(target_pointer_width = "16") {
        unsigned_to_smaller_unsigned::<u32, usize>();
    } else {
        unsigned_to_larger_same_unsigned::<u32, usize>();
    }

    unsigned_to_smaller_unsigned::<u64, u8>();
    unsigned_to_smaller_unsigned::<u64, u16>();
    unsigned_to_smaller_unsigned::<u64, u32>();
    unsigned_to_larger_same_unsigned::<u64, u64>();
    unsigned_to_larger_same_unsigned::<u64, u128>();
    if cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32") {
        unsigned_to_smaller_unsigned::<u64, usize>();
    } else {
        unsigned_to_larger_same_unsigned::<u64, usize>();
    }

    unsigned_to_smaller_unsigned::<u128, u8>();
    unsigned_to_smaller_unsigned::<u128, u16>();
    unsigned_to_smaller_unsigned::<u128, u32>();
    unsigned_to_smaller_unsigned::<u128, u64>();
    unsigned_to_larger_same_unsigned::<u128, u128>();
    if cfg!(target_pointer_width = "16")
        || cfg!(target_pointer_width = "32")
        || cfg!(target_pointer_width = "64")
    {
        unsigned_to_smaller_unsigned::<u128, usize>();
    } else {
        unsigned_to_larger_same_unsigned::<u128, usize>();
    }

    unsigned_to_smaller_unsigned::<usize, u8>();
    if cfg!(target_pointer_width = "16") {
        unsigned_to_larger_same_unsigned::<usize, u16>();
        unsigned_to_larger_same_unsigned::<usize, u32>();
        unsigned_to_larger_same_unsigned::<usize, u64>();
    } else if cfg!(target_pointer_width = "32") {
        unsigned_to_smaller_unsigned::<usize, u16>();
        unsigned_to_larger_same_unsigned::<usize, u32>();
        unsigned_to_larger_same_unsigned::<usize, u64>();
    } else if cfg!(target_pointer_width = "64") {
        unsigned_to_smaller_unsigned::<usize, u16>();
        unsigned_to_smaller_unsigned::<usize, u32>();
        unsigned_to_larger_same_unsigned::<usize, u64>();
    } else if cfg!(target_pointer_width = "128") {
        unsigned_to_smaller_unsigned::<usize, u16>();
        unsigned_to_smaller_unsigned::<usize, u32>();
        unsigned_to_smaller_unsigned::<usize, u64>();
    }
    unsigned_to_larger_same_unsigned::<usize, u128>();
    unsigned_to_larger_same_unsigned::<usize, usize>();
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "overflow")]
fn large_int_as_panic() {
    let _ = cast::<u8, i8>(128);
}

#[cfg(not(debug_assertions))]
#[test]
fn large_int_as_wrap() {
    assert_eq!(cast::<u8, i8>(128), -128);
    assert_eq!(cast::<i8, u8>(-127), 129);
}

#[test]
#[should_panic(expected = "overflow")]
fn large_int_unwrapped_as_panic() {
    let _ = unwrapped_cast::<u8, i8>(128);
}
