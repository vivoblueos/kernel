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
    cast, checked_cast, overflowing_cast, saturating_cast,
    tests::{Float, Int},
    unwrapped_cast, wrapping_cast, Cast, CheckedCast, OverflowingCast, Round, SaturatingCast,
    UnwrappedCast, WrappingCast,
};
use core::{f32, f64, mem, num::Wrapping};

fn float_to_nonwrapping_signed<Src: Float, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_prec = Src::prec();
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;

    let src_0 = Src::int_shl(0, 0);
    let src_1 = Src::int_shl(1, 0);
    let src_1_5 = Src::int_shl(3, -1);
    let src_8 = Src::int_shl(1, (dst_nbits - 1) as i8);
    let src_1ish = if src_prec > dst_nbits {
        src_1
    } else {
        Src::int_shl(1, (dst_nbits - src_prec) as i8)
    };
    let src_7ish = src_8 - src_1ish;
    let src_6 = Src::int_shl(6, (dst_nbits - 4) as i8);
    let src_9ish = src_8 + src_1ish;
    let src_c = Src::int_shl(12, (dst_nbits - 4) as i8);
    let src_fish = src_8 + src_7ish;
    let src_max = Src::max();
    let src_inf = Src::inf();
    let src_nan = Src::nan();

    let dst_z0 = Dst::zero();
    let dst_p1 = Dst::one();
    let dst_m1 = !dst_z0;
    let (dst_p1ish, dst_m1ish) = if src_prec > dst_nbits {
        (dst_p1, dst_m1)
    } else {
        (
            dst_p1 << (dst_nbits - src_prec),
            dst_m1 << (dst_nbits - src_prec),
        )
    };
    let dst_p4 = dst_p1 << (dst_nbits - 2);
    let dst_p6 = dst_p4 + (dst_p4 >> 1);
    let dst_p7ish = dst_p4 + (dst_p4 - dst_p1ish);
    let dst_m4 = dst_z0 - dst_p4;
    let dst_m6 = dst_z0 - dst_p6;
    let dst_m8 = dst_m4 + dst_m4;
    let dst_m7ish = dst_m8 + dst_p1ish;
    let dst_p7 = !dst_m8;
    let (dst_wmax, dst_wmax_neg) = if src_nbits == 32 && dst_nbits == 128 {
        let max = !dst_z0 << (dst_nbits - src_prec);
        (max, !max + dst_p1)
    } else {
        (dst_z0, dst_z0)
    };

    assert_eq!(cast(-src_8), dst_m8);
    assert_eq!(cast(-src_7ish), dst_m7ish);
    assert_eq!(cast(-src_6), dst_m6);
    assert_eq!(cast(-src_1_5), dst_m1);
    assert_eq!(cast(-src_1), dst_m1);
    assert_eq!(cast(-src_0), dst_z0);
    assert_eq!(cast(src_0), dst_z0);
    assert_eq!(cast(src_1), dst_p1);
    assert_eq!(cast(src_1_5), dst_p1);
    assert_eq!(cast(src_6), dst_p6);
    assert_eq!(cast(src_7ish), dst_p7ish);

    assert_eq!(checked_cast(-src_nan), None);
    assert_eq!(checked_cast(-src_inf), None);
    assert_eq!(checked_cast(-src_max), None);
    assert_eq!(checked_cast(-src_fish), None);
    assert_eq!(checked_cast(-src_c), None);
    assert_eq!(checked_cast(-src_9ish), None);
    assert_eq!(checked_cast(-src_8), Some(dst_m8));
    assert_eq!(checked_cast(-src_7ish), Some(dst_m7ish));
    assert_eq!(checked_cast(-src_6), Some(dst_m6));
    assert_eq!(checked_cast(-src_1_5), Some(dst_m1));
    assert_eq!(checked_cast(-src_1), Some(dst_m1));
    assert_eq!(checked_cast(-src_0), Some(dst_z0));
    assert_eq!(checked_cast(src_0), Some(dst_z0));
    assert_eq!(checked_cast(src_1), Some(dst_p1));
    assert_eq!(checked_cast(src_1_5), Some(dst_p1));
    assert_eq!(checked_cast(src_6), Some(dst_p6));
    assert_eq!(checked_cast(src_7ish), Some(dst_p7ish));
    assert_eq!(checked_cast(src_8), None);
    assert_eq!(checked_cast(src_9ish), None);
    assert_eq!(checked_cast(src_c), None);
    assert_eq!(checked_cast(src_fish), None);
    assert_eq!(checked_cast(src_max), None);
    assert_eq!(checked_cast(src_inf), None);
    assert_eq!(checked_cast(src_nan), None);

    assert_eq!(saturating_cast(-src_inf), dst_m8);
    assert_eq!(saturating_cast(-src_max), dst_m8);
    assert_eq!(saturating_cast(-src_fish), dst_m8);
    assert_eq!(saturating_cast(-src_c), dst_m8);
    assert_eq!(saturating_cast(-src_9ish), dst_m8);
    assert_eq!(saturating_cast(-src_8), dst_m8);
    assert_eq!(saturating_cast(-src_7ish), dst_m7ish);
    assert_eq!(saturating_cast(-src_6), dst_m6);
    assert_eq!(saturating_cast(-src_1_5), dst_m1);
    assert_eq!(saturating_cast(-src_1), dst_m1);
    assert_eq!(saturating_cast(-src_0), dst_z0);
    assert_eq!(saturating_cast(src_0), dst_z0);
    assert_eq!(saturating_cast(src_1), dst_p1);
    assert_eq!(saturating_cast(src_1_5), dst_p1);
    assert_eq!(saturating_cast(src_6), dst_p6);
    assert_eq!(saturating_cast(src_7ish), dst_p7ish);
    assert_eq!(saturating_cast(src_8), dst_p7);
    assert_eq!(saturating_cast(src_9ish), dst_p7);
    assert_eq!(saturating_cast(src_c), dst_p7);
    assert_eq!(saturating_cast(src_fish), dst_p7);
    assert_eq!(saturating_cast(src_max), dst_p7);
    assert_eq!(saturating_cast(src_inf), dst_p7);

    assert_eq!(wrapping_cast(-src_max), dst_wmax_neg);
    assert_eq!(wrapping_cast(-src_fish), dst_p1ish);
    assert_eq!(wrapping_cast(-src_c), dst_p4);
    assert_eq!(wrapping_cast(-src_9ish), dst_p7ish);
    assert_eq!(wrapping_cast(-src_8), dst_m8);
    assert_eq!(wrapping_cast(-src_7ish), dst_m7ish);
    assert_eq!(wrapping_cast(-src_6), dst_m6);
    assert_eq!(wrapping_cast(-src_1_5), dst_m1);
    assert_eq!(wrapping_cast(-src_1), dst_m1);
    assert_eq!(wrapping_cast(-src_0), dst_z0);
    assert_eq!(wrapping_cast(src_0), dst_z0);
    assert_eq!(wrapping_cast(src_1), dst_p1);
    assert_eq!(wrapping_cast(src_1_5), dst_p1);
    assert_eq!(wrapping_cast(src_6), dst_p6);
    assert_eq!(wrapping_cast(src_7ish), dst_p7ish);
    assert_eq!(wrapping_cast(src_8), dst_m8);
    assert_eq!(wrapping_cast(src_9ish), dst_m7ish);
    assert_eq!(wrapping_cast(src_c), dst_m4);
    assert_eq!(wrapping_cast(src_fish), dst_m1ish);
    assert_eq!(wrapping_cast(src_max), dst_wmax);

    assert_eq!(overflowing_cast(-src_max), (dst_wmax_neg, true));
    assert_eq!(overflowing_cast(-src_fish), (dst_p1ish, true));
    assert_eq!(overflowing_cast(-src_c), (dst_p4, true));
    assert_eq!(overflowing_cast(-src_9ish), (dst_p7ish, true));
    assert_eq!(overflowing_cast(-src_8), (dst_m8, false));
    assert_eq!(overflowing_cast(-src_7ish), (dst_m7ish, false));
    assert_eq!(overflowing_cast(-src_6), (dst_m6, false));
    assert_eq!(overflowing_cast(-src_1_5), (dst_m1, false));
    assert_eq!(overflowing_cast(-src_1), (dst_m1, false));
    assert_eq!(overflowing_cast(-src_0), (dst_z0, false));
    assert_eq!(overflowing_cast(src_0), (dst_z0, false));
    assert_eq!(overflowing_cast(src_1), (dst_p1, false));
    assert_eq!(overflowing_cast(src_1_5), (dst_p1, false));
    assert_eq!(overflowing_cast(src_6), (dst_p6, false));
    assert_eq!(overflowing_cast(src_7ish), (dst_p7ish, false));
    assert_eq!(overflowing_cast(src_8), (dst_m8, true));
    assert_eq!(overflowing_cast(src_9ish), (dst_m7ish, true));
    assert_eq!(overflowing_cast(src_c), (dst_m4, true));
    assert_eq!(overflowing_cast(src_fish), (dst_m1ish, true));
    assert_eq!(overflowing_cast(src_max), (dst_wmax, true));

    assert_eq!(unwrapped_cast(-src_8), dst_m8);
    assert_eq!(unwrapped_cast(-src_7ish), dst_m7ish);
    assert_eq!(unwrapped_cast(-src_6), dst_m6);
    assert_eq!(unwrapped_cast(-src_1_5), dst_m1);
    assert_eq!(unwrapped_cast(-src_1), dst_m1);
    assert_eq!(unwrapped_cast(-src_0), dst_z0);
    assert_eq!(unwrapped_cast(src_0), dst_z0);
    assert_eq!(unwrapped_cast(src_1), dst_p1);
    assert_eq!(unwrapped_cast(src_1_5), dst_p1);
    assert_eq!(unwrapped_cast(src_6), dst_p6);
    assert_eq!(unwrapped_cast(src_7ish), dst_p7ish);
}

fn float_to_wrapping_signed<Src: Float, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_prec = Src::prec();
    let dst_nbits = mem::size_of::<Dst>() * 8;

    let src_0 = Src::int_shl(0, 0);
    let src_1 = Src::int_shl(1, 0);
    let src_1_5 = Src::int_shl(3, -1);
    let src_8 = Src::int_shl(1, (dst_nbits - 1) as i8);
    let src_1ish = if src_prec > dst_nbits {
        src_1
    } else {
        Src::int_shl(1, (dst_nbits - src_prec) as i8)
    };
    let src_7ish = src_8 - src_1ish;
    let src_6 = Src::int_shl(6, (dst_nbits - 4) as i8);
    let src_9ish = src_8 + src_1ish;
    let src_c = Src::int_shl(12, (dst_nbits - 4) as i8);
    let src_fish = src_8 + src_7ish;
    let src_max = Src::max();
    let src_inf = Src::inf();
    let src_nan = Src::nan();

    let dst_z0 = Wrapping(wrapping_cast(src_0));
    let dst_p1 = Wrapping(wrapping_cast(src_1));
    let dst_m1 = Wrapping(wrapping_cast(-src_1));
    let dst_p1ish = Wrapping(wrapping_cast(-src_fish));
    let dst_m1ish = Wrapping(wrapping_cast(src_fish));
    let dst_p4 = Wrapping(wrapping_cast(-src_c));
    let dst_p6 = Wrapping(wrapping_cast(src_6));
    let dst_p7ish = Wrapping(wrapping_cast(src_7ish));
    let dst_m4 = Wrapping(wrapping_cast(src_c));
    let dst_m6 = Wrapping(wrapping_cast(-src_6));
    let dst_m8 = Wrapping(wrapping_cast(-src_8));
    let dst_m7ish = Wrapping(wrapping_cast(-src_7ish));
    let dst_wmax = Wrapping(wrapping_cast(src_max));
    let dst_wmax_neg = Wrapping(wrapping_cast(-src_max));

    assert_eq!(cast(-src_max), dst_wmax_neg);
    assert_eq!(cast(-src_fish), dst_p1ish);
    assert_eq!(cast(-src_c), dst_p4);
    assert_eq!(cast(-src_9ish), dst_p7ish);
    assert_eq!(cast(-src_8), dst_m8);
    assert_eq!(cast(-src_7ish), dst_m7ish);
    assert_eq!(cast(-src_6), dst_m6);
    assert_eq!(cast(-src_1_5), dst_m1);
    assert_eq!(cast(-src_1), dst_m1);
    assert_eq!(cast(-src_0), dst_z0);
    assert_eq!(cast(src_0), dst_z0);
    assert_eq!(cast(src_1), dst_p1);
    assert_eq!(cast(src_1_5), dst_p1);
    assert_eq!(cast(src_6), dst_p6);
    assert_eq!(cast(src_7ish), dst_p7ish);
    assert_eq!(cast(src_8), dst_m8);
    assert_eq!(cast(src_9ish), dst_m7ish);
    assert_eq!(cast(src_c), dst_m4);
    assert_eq!(cast(src_fish), dst_m1ish);
    assert_eq!(cast(src_max), dst_wmax);

    assert_eq!(checked_cast(-src_nan), None);
    assert_eq!(checked_cast(-src_inf), None);
    assert_eq!(checked_cast(-src_max), Some(dst_wmax_neg));
    assert_eq!(checked_cast(-src_fish), Some(dst_p1ish));
    assert_eq!(checked_cast(-src_c), Some(dst_p4));
    assert_eq!(checked_cast(-src_9ish), Some(dst_p7ish));
    assert_eq!(checked_cast(-src_8), Some(dst_m8));
    assert_eq!(checked_cast(-src_7ish), Some(dst_m7ish));
    assert_eq!(checked_cast(-src_6), Some(dst_m6));
    assert_eq!(checked_cast(-src_1_5), Some(dst_m1));
    assert_eq!(checked_cast(-src_1), Some(dst_m1));
    assert_eq!(checked_cast(-src_0), Some(dst_z0));
    assert_eq!(checked_cast(src_0), Some(dst_z0));
    assert_eq!(checked_cast(src_1), Some(dst_p1));
    assert_eq!(checked_cast(src_1_5), Some(dst_p1));
    assert_eq!(checked_cast(src_6), Some(dst_p6));
    assert_eq!(checked_cast(src_7ish), Some(dst_p7ish));
    assert_eq!(checked_cast(src_8), Some(dst_m8));
    assert_eq!(checked_cast(src_9ish), Some(dst_m7ish));
    assert_eq!(checked_cast(src_c), Some(dst_m4));
    assert_eq!(checked_cast(src_fish), Some(dst_m1ish));
    assert_eq!(checked_cast(src_max), Some(dst_wmax));
    assert_eq!(checked_cast(src_inf), None);
    assert_eq!(checked_cast(src_nan), None);

    assert_eq!(unwrapped_cast(-src_max), dst_wmax_neg);
    assert_eq!(unwrapped_cast(-src_fish), dst_p1ish);
    assert_eq!(unwrapped_cast(-src_c), dst_p4);
    assert_eq!(unwrapped_cast(-src_9ish), dst_p7ish);
    assert_eq!(unwrapped_cast(-src_8), dst_m8);
    assert_eq!(unwrapped_cast(-src_7ish), dst_m7ish);
    assert_eq!(unwrapped_cast(-src_6), dst_m6);
    assert_eq!(unwrapped_cast(-src_1_5), dst_m1);
    assert_eq!(unwrapped_cast(-src_1), dst_m1);
    assert_eq!(unwrapped_cast(-src_0), dst_z0);
    assert_eq!(unwrapped_cast(src_0), dst_z0);
    assert_eq!(unwrapped_cast(src_1), dst_p1);
    assert_eq!(unwrapped_cast(src_1_5), dst_p1);
    assert_eq!(unwrapped_cast(src_6), dst_p6);
    assert_eq!(unwrapped_cast(src_7ish), dst_p7ish);
    assert_eq!(unwrapped_cast(src_8), dst_m8);
    assert_eq!(unwrapped_cast(src_9ish), dst_m7ish);
    assert_eq!(unwrapped_cast(src_c), dst_m4);
    assert_eq!(unwrapped_cast(src_fish), dst_m1ish);
    assert_eq!(unwrapped_cast(src_max), dst_wmax);
}

fn round_to_nonwrapping_signed<Src: Float, Dst: Int>()
where
    Round<Src>: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_prec = Src::prec();
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;

    let src_0 = Src::int_shl(0, 0);
    let src_1 = Src::int_shl(1, 0);
    let src_1_5 = Src::int_shl(3, -1);
    let src_8 = Src::int_shl(1, (dst_nbits - 1) as i8);
    let src_1ish = if src_prec > dst_nbits {
        src_1
    } else {
        Src::int_shl(1, (dst_nbits - src_prec) as i8)
    };
    let src_7ish = src_8 - src_1ish;
    let src_6 = Src::int_shl(6, (dst_nbits - 4) as i8);
    let src_9ish = src_8 + src_1ish;
    let src_c = Src::int_shl(12, (dst_nbits - 4) as i8);
    let src_fish = src_8 + src_7ish;
    let src_max = Src::max();
    let src_inf = Src::inf();
    let src_nan = Src::nan();

    let dst_z0 = Dst::zero();
    let dst_p1 = Dst::one();
    let dst_p2 = dst_p1 + dst_p1;
    let dst_m1 = !dst_z0;
    let dst_m2 = dst_m1 + dst_m1;
    let (dst_p1ish, dst_m1ish) = if src_prec > dst_nbits {
        (dst_p1, dst_m1)
    } else {
        (
            dst_p1 << (dst_nbits - src_prec),
            dst_m1 << (dst_nbits - src_prec),
        )
    };
    let dst_p4 = dst_p1 << (dst_nbits - 2);
    let dst_p6 = dst_p4 + (dst_p4 >> 1);
    let dst_p7ish = dst_p4 + (dst_p4 - dst_p1ish);
    let dst_m4 = dst_z0 - dst_p4;
    let dst_m6 = dst_z0 - dst_p6;
    let dst_m8 = dst_m4 + dst_m4;
    let dst_m7ish = dst_m8 + dst_p1ish;
    let dst_p7 = !dst_m8;
    let (dst_wmax, dst_wmax_neg) = if src_nbits == 32 && dst_nbits == 128 {
        let max = !dst_z0 << (dst_nbits - src_prec);
        (max, !max + dst_p1)
    } else {
        (dst_z0, dst_z0)
    };

    assert_eq!(cast(Round(-src_8)), dst_m8);
    assert_eq!(cast(Round(-src_7ish)), dst_m7ish);
    assert_eq!(cast(Round(-src_6)), dst_m6);
    assert_eq!(cast(Round(-src_1_5)), dst_m2);
    assert_eq!(cast(Round(-src_1)), dst_m1);
    assert_eq!(cast(Round(-src_0)), dst_z0);
    assert_eq!(cast(Round(src_0)), dst_z0);
    assert_eq!(cast(Round(src_1)), dst_p1);
    assert_eq!(cast(Round(src_1_5)), dst_p2);
    assert_eq!(cast(Round(src_6)), dst_p6);
    assert_eq!(cast(Round(src_7ish)), dst_p7ish);

    assert_eq!(checked_cast(Round(-src_nan)), None);
    assert_eq!(checked_cast(Round(-src_inf)), None);
    assert_eq!(checked_cast(Round(-src_max)), None);
    assert_eq!(checked_cast(Round(-src_fish)), None);
    assert_eq!(checked_cast(Round(-src_c)), None);
    assert_eq!(checked_cast(Round(-src_9ish)), None);
    assert_eq!(checked_cast(Round(-src_8)), Some(dst_m8));
    assert_eq!(checked_cast(Round(-src_7ish)), Some(dst_m7ish));
    assert_eq!(checked_cast(Round(-src_6)), Some(dst_m6));
    assert_eq!(checked_cast(Round(-src_1_5)), Some(dst_m2));
    assert_eq!(checked_cast(Round(-src_1)), Some(dst_m1));
    assert_eq!(checked_cast(Round(-src_0)), Some(dst_z0));
    assert_eq!(checked_cast(Round(src_0)), Some(dst_z0));
    assert_eq!(checked_cast(Round(src_1)), Some(dst_p1));
    assert_eq!(checked_cast(Round(src_1_5)), Some(dst_p2));
    assert_eq!(checked_cast(Round(src_6)), Some(dst_p6));
    assert_eq!(checked_cast(Round(src_7ish)), Some(dst_p7ish));
    assert_eq!(checked_cast(Round(src_8)), None);
    assert_eq!(checked_cast(Round(src_9ish)), None);
    assert_eq!(checked_cast(Round(src_c)), None);
    assert_eq!(checked_cast(Round(src_fish)), None);
    assert_eq!(checked_cast(Round(src_max)), None);
    assert_eq!(checked_cast(Round(src_inf)), None);
    assert_eq!(checked_cast(Round(src_nan)), None);

    assert_eq!(saturating_cast(Round(-src_inf)), dst_m8);
    assert_eq!(saturating_cast(Round(-src_max)), dst_m8);
    assert_eq!(saturating_cast(Round(-src_fish)), dst_m8);
    assert_eq!(saturating_cast(Round(-src_c)), dst_m8);
    assert_eq!(saturating_cast(Round(-src_9ish)), dst_m8);
    assert_eq!(saturating_cast(Round(-src_8)), dst_m8);
    assert_eq!(saturating_cast(Round(-src_7ish)), dst_m7ish);
    assert_eq!(saturating_cast(Round(-src_6)), dst_m6);
    assert_eq!(saturating_cast(Round(-src_1_5)), dst_m2);
    assert_eq!(saturating_cast(Round(-src_1)), dst_m1);
    assert_eq!(saturating_cast(Round(-src_0)), dst_z0);
    assert_eq!(saturating_cast(Round(src_0)), dst_z0);
    assert_eq!(saturating_cast(Round(src_1)), dst_p1);
    assert_eq!(saturating_cast(Round(src_1_5)), dst_p2);
    assert_eq!(saturating_cast(Round(src_6)), dst_p6);
    assert_eq!(saturating_cast(Round(src_7ish)), dst_p7ish);
    assert_eq!(saturating_cast(Round(src_8)), dst_p7);
    assert_eq!(saturating_cast(Round(src_9ish)), dst_p7);
    assert_eq!(saturating_cast(Round(src_c)), dst_p7);
    assert_eq!(saturating_cast(Round(src_fish)), dst_p7);
    assert_eq!(saturating_cast(Round(src_max)), dst_p7);
    assert_eq!(saturating_cast(Round(src_inf)), dst_p7);

    assert_eq!(wrapping_cast(Round(-src_max)), dst_wmax_neg);
    assert_eq!(wrapping_cast(Round(-src_fish)), dst_p1ish);
    assert_eq!(wrapping_cast(Round(-src_c)), dst_p4);
    assert_eq!(wrapping_cast(Round(-src_9ish)), dst_p7ish);
    assert_eq!(wrapping_cast(Round(-src_8)), dst_m8);
    assert_eq!(wrapping_cast(Round(-src_7ish)), dst_m7ish);
    assert_eq!(wrapping_cast(Round(-src_6)), dst_m6);
    assert_eq!(wrapping_cast(Round(-src_1_5)), dst_m2);
    assert_eq!(wrapping_cast(Round(-src_1)), dst_m1);
    assert_eq!(wrapping_cast(Round(-src_0)), dst_z0);
    assert_eq!(wrapping_cast(Round(src_0)), dst_z0);
    assert_eq!(wrapping_cast(Round(src_1)), dst_p1);
    assert_eq!(wrapping_cast(Round(src_1_5)), dst_p2);
    assert_eq!(wrapping_cast(Round(src_6)), dst_p6);
    assert_eq!(wrapping_cast(Round(src_7ish)), dst_p7ish);
    assert_eq!(wrapping_cast(Round(src_8)), dst_m8);
    assert_eq!(wrapping_cast(Round(src_9ish)), dst_m7ish);
    assert_eq!(wrapping_cast(Round(src_c)), dst_m4);
    assert_eq!(wrapping_cast(Round(src_fish)), dst_m1ish);
    assert_eq!(wrapping_cast(Round(src_max)), dst_wmax);

    assert_eq!(overflowing_cast(Round(-src_max)), (dst_wmax_neg, true));
    assert_eq!(overflowing_cast(Round(-src_fish)), (dst_p1ish, true));
    assert_eq!(overflowing_cast(Round(-src_c)), (dst_p4, true));
    assert_eq!(overflowing_cast(Round(-src_9ish)), (dst_p7ish, true));
    assert_eq!(overflowing_cast(Round(-src_8)), (dst_m8, false));
    assert_eq!(overflowing_cast(Round(-src_7ish)), (dst_m7ish, false));
    assert_eq!(overflowing_cast(Round(-src_6)), (dst_m6, false));
    assert_eq!(overflowing_cast(Round(-src_1_5)), (dst_m2, false));
    assert_eq!(overflowing_cast(Round(-src_1)), (dst_m1, false));
    assert_eq!(overflowing_cast(Round(-src_0)), (dst_z0, false));
    assert_eq!(overflowing_cast(Round(src_0)), (dst_z0, false));
    assert_eq!(overflowing_cast(Round(src_1)), (dst_p1, false));
    assert_eq!(overflowing_cast(Round(src_1_5)), (dst_p2, false));
    assert_eq!(overflowing_cast(Round(src_6)), (dst_p6, false));
    assert_eq!(overflowing_cast(Round(src_7ish)), (dst_p7ish, false));
    assert_eq!(overflowing_cast(Round(src_8)), (dst_m8, true));
    assert_eq!(overflowing_cast(Round(src_9ish)), (dst_m7ish, true));
    assert_eq!(overflowing_cast(Round(src_c)), (dst_m4, true));
    assert_eq!(overflowing_cast(Round(src_fish)), (dst_m1ish, true));
    assert_eq!(overflowing_cast(Round(src_max)), (dst_wmax, true));

    assert_eq!(unwrapped_cast(Round(-src_8)), dst_m8);
    assert_eq!(unwrapped_cast(Round(-src_7ish)), dst_m7ish);
    assert_eq!(unwrapped_cast(Round(-src_6)), dst_m6);
    assert_eq!(unwrapped_cast(Round(-src_1_5)), dst_m2);
    assert_eq!(unwrapped_cast(Round(-src_1)), dst_m1);
    assert_eq!(unwrapped_cast(Round(-src_0)), dst_z0);
    assert_eq!(unwrapped_cast(Round(src_0)), dst_z0);
    assert_eq!(unwrapped_cast(Round(src_1)), dst_p1);
    assert_eq!(unwrapped_cast(Round(src_1_5)), dst_p2);
    assert_eq!(unwrapped_cast(Round(src_6)), dst_p6);
    assert_eq!(unwrapped_cast(Round(src_7ish)), dst_p7ish);
}

fn round_to_wrapping_signed<Src: Float, Dst: Int>()
where
    Round<Src>: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_prec = Src::prec();
    let dst_nbits = mem::size_of::<Dst>() * 8;

    let src_0 = Src::int_shl(0, 0);
    let src_1 = Src::int_shl(1, 0);
    let src_1_5 = Src::int_shl(3, -1);
    let src_8 = Src::int_shl(1, (dst_nbits - 1) as i8);
    let src_1ish = if src_prec > dst_nbits {
        src_1
    } else {
        Src::int_shl(1, (dst_nbits - src_prec) as i8)
    };
    let src_7ish = src_8 - src_1ish;
    let src_6 = Src::int_shl(6, (dst_nbits - 4) as i8);
    let src_9ish = src_8 + src_1ish;
    let src_c = Src::int_shl(12, (dst_nbits - 4) as i8);
    let src_fish = src_8 + src_7ish;
    let src_max = Src::max();
    let src_inf = Src::inf();
    let src_nan = Src::nan();

    let dst_z0 = Wrapping(wrapping_cast(Round(src_0)));
    let dst_p1 = Wrapping(wrapping_cast(Round(src_1)));
    let dst_p2 = Wrapping(wrapping_cast(Round(src_1_5)));
    let dst_m1 = Wrapping(wrapping_cast(Round(-src_1)));
    let dst_m2 = Wrapping(wrapping_cast(Round(-src_1_5)));
    let dst_p1ish = Wrapping(wrapping_cast(Round(-src_fish)));
    let dst_m1ish = Wrapping(wrapping_cast(Round(src_fish)));
    let dst_p4 = Wrapping(wrapping_cast(Round(-src_c)));
    let dst_p6 = Wrapping(wrapping_cast(Round(src_6)));
    let dst_p7ish = Wrapping(wrapping_cast(Round(src_7ish)));
    let dst_m4 = Wrapping(wrapping_cast(Round(src_c)));
    let dst_m6 = Wrapping(wrapping_cast(Round(-src_6)));
    let dst_m8 = Wrapping(wrapping_cast(Round(-src_8)));
    let dst_m7ish = Wrapping(wrapping_cast(Round(-src_7ish)));
    let dst_wmax = Wrapping(wrapping_cast(Round(src_max)));
    let dst_wmax_neg = Wrapping(wrapping_cast(Round(-src_max)));

    assert_eq!(cast(Round(-src_max)), dst_wmax_neg);
    assert_eq!(cast(Round(-src_fish)), dst_p1ish);
    assert_eq!(cast(Round(-src_c)), dst_p4);
    assert_eq!(cast(Round(-src_9ish)), dst_p7ish);
    assert_eq!(cast(Round(-src_8)), dst_m8);
    assert_eq!(cast(Round(-src_7ish)), dst_m7ish);
    assert_eq!(cast(Round(-src_6)), dst_m6);
    assert_eq!(cast(Round(-src_1_5)), dst_m2);
    assert_eq!(cast(Round(-src_1)), dst_m1);
    assert_eq!(cast(Round(-src_0)), dst_z0);
    assert_eq!(cast(Round(src_0)), dst_z0);
    assert_eq!(cast(Round(src_1)), dst_p1);
    assert_eq!(cast(Round(src_1_5)), dst_p2);
    assert_eq!(cast(Round(src_6)), dst_p6);
    assert_eq!(cast(Round(src_7ish)), dst_p7ish);
    assert_eq!(cast(Round(src_8)), dst_m8);
    assert_eq!(cast(Round(src_9ish)), dst_m7ish);
    assert_eq!(cast(Round(src_c)), dst_m4);
    assert_eq!(cast(Round(src_fish)), dst_m1ish);
    assert_eq!(cast(Round(src_max)), dst_wmax);

    assert_eq!(checked_cast(Round(-src_nan)), None);
    assert_eq!(checked_cast(Round(-src_inf)), None);
    assert_eq!(checked_cast(Round(-src_max)), Some(dst_wmax_neg));
    assert_eq!(checked_cast(Round(-src_fish)), Some(dst_p1ish));
    assert_eq!(checked_cast(Round(-src_c)), Some(dst_p4));
    assert_eq!(checked_cast(Round(-src_9ish)), Some(dst_p7ish));
    assert_eq!(checked_cast(Round(-src_8)), Some(dst_m8));
    assert_eq!(checked_cast(Round(-src_7ish)), Some(dst_m7ish));
    assert_eq!(checked_cast(Round(-src_6)), Some(dst_m6));
    assert_eq!(checked_cast(Round(-src_1_5)), Some(dst_m2));
    assert_eq!(checked_cast(Round(-src_1)), Some(dst_m1));
    assert_eq!(checked_cast(Round(-src_0)), Some(dst_z0));
    assert_eq!(checked_cast(Round(src_0)), Some(dst_z0));
    assert_eq!(checked_cast(Round(src_1)), Some(dst_p1));
    assert_eq!(checked_cast(Round(src_1_5)), Some(dst_p2));
    assert_eq!(checked_cast(Round(src_6)), Some(dst_p6));
    assert_eq!(checked_cast(Round(src_7ish)), Some(dst_p7ish));
    assert_eq!(checked_cast(Round(src_8)), Some(dst_m8));
    assert_eq!(checked_cast(Round(src_9ish)), Some(dst_m7ish));
    assert_eq!(checked_cast(Round(src_c)), Some(dst_m4));
    assert_eq!(checked_cast(Round(src_fish)), Some(dst_m1ish));
    assert_eq!(checked_cast(Round(src_max)), Some(dst_wmax));
    assert_eq!(checked_cast(Round(src_inf)), None);
    assert_eq!(checked_cast(Round(src_nan)), None);

    assert_eq!(unwrapped_cast(Round(-src_max)), dst_wmax_neg);
    assert_eq!(unwrapped_cast(Round(-src_fish)), dst_p1ish);
    assert_eq!(unwrapped_cast(Round(-src_c)), dst_p4);
    assert_eq!(unwrapped_cast(Round(-src_9ish)), dst_p7ish);
    assert_eq!(unwrapped_cast(Round(-src_8)), dst_m8);
    assert_eq!(unwrapped_cast(Round(-src_7ish)), dst_m7ish);
    assert_eq!(unwrapped_cast(Round(-src_6)), dst_m6);
    assert_eq!(unwrapped_cast(Round(-src_1_5)), dst_m2);
    assert_eq!(unwrapped_cast(Round(-src_1)), dst_m1);
    assert_eq!(unwrapped_cast(Round(-src_0)), dst_z0);
    assert_eq!(unwrapped_cast(Round(src_0)), dst_z0);
    assert_eq!(unwrapped_cast(Round(src_1)), dst_p1);
    assert_eq!(unwrapped_cast(Round(src_1_5)), dst_p2);
    assert_eq!(unwrapped_cast(Round(src_6)), dst_p6);
    assert_eq!(unwrapped_cast(Round(src_7ish)), dst_p7ish);
    assert_eq!(unwrapped_cast(Round(src_8)), dst_m8);
    assert_eq!(unwrapped_cast(Round(src_9ish)), dst_m7ish);
    assert_eq!(unwrapped_cast(Round(src_c)), dst_m4);
    assert_eq!(unwrapped_cast(Round(src_fish)), dst_m1ish);
    assert_eq!(unwrapped_cast(Round(src_max)), dst_wmax);
}

fn float_to_nonwrapping_unsigned<Src: Float, Dst: Int>()
where
    Src: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_prec = Src::prec();
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;

    let src_0 = Src::int_shl(0, 0);
    let src_1 = Src::int_shl(1, 0);
    let src_1_5 = Src::int_shl(3, -1);
    let src_8 = Src::int_shl(1, (dst_nbits - 1) as i8);
    let src_1ish = if src_prec > dst_nbits {
        src_1
    } else {
        Src::int_shl(1, (dst_nbits - src_prec) as i8)
    };
    let src_7ish = src_8 - src_1ish;
    let src_6 = Src::int_shl(6, (dst_nbits - 4) as i8);
    let src_9ish = src_8 + src_1ish;
    let src_c = Src::int_shl(12, (dst_nbits - 4) as i8);
    let src_fish = src_8 + src_7ish;
    let src_max = Src::max();
    let src_inf = Src::inf();
    let src_nan = Src::nan();

    let dst_0 = Dst::zero();
    let dst_1 = Dst::one();
    let (dst_1ish, dst_fish) = if src_prec > dst_nbits {
        (dst_1, !dst_1 + dst_1)
    } else {
        let ish = dst_1 << (dst_nbits - src_prec);
        (ish, !ish + dst_1)
    };
    let dst_4 = dst_1 << (dst_nbits - 2);
    let dst_6 = dst_4 + (dst_4 >> 1);
    let dst_7ish = dst_4 + (dst_4 - dst_1ish);
    let dst_8 = dst_1 << (dst_nbits - 1);
    let dst_7 = !dst_8;
    let dst_9ish = dst_8 + dst_1ish;
    let dst_a = dst_6 + dst_4;
    let dst_c = dst_8 + dst_4;
    let dst_f = dst_8 + dst_7;
    let (dst_wmax, dst_wmax_neg) = if src_nbits == 32 && dst_nbits == 128 {
        let max = !dst_0 << (dst_nbits - src_prec);
        (max, !max + dst_1)
    } else {
        (dst_0, dst_0)
    };

    assert_eq!(cast(-src_0), dst_0);
    assert_eq!(cast(src_0), dst_0);
    assert_eq!(cast(src_1), dst_1);
    assert_eq!(cast(src_1_5), dst_1);
    assert_eq!(cast(src_6), dst_6);
    assert_eq!(cast(src_7ish), dst_7ish);
    assert_eq!(cast(src_8), dst_8);
    assert_eq!(cast(src_9ish), dst_9ish);
    assert_eq!(cast(src_c), dst_c);
    assert_eq!(cast(src_fish), dst_fish);
    if src_nbits == 32 && dst_nbits == 128 {
        assert_eq!(cast(src_max), dst_wmax);
    }

    assert_eq!(checked_cast(-src_nan), None);
    assert_eq!(checked_cast(-src_inf), None);
    assert_eq!(checked_cast(-src_max), None);
    assert_eq!(checked_cast(-src_fish), None);
    assert_eq!(checked_cast(-src_c), None);
    assert_eq!(checked_cast(-src_9ish), None);
    assert_eq!(checked_cast(-src_8), None);
    assert_eq!(checked_cast(-src_7ish), None);
    assert_eq!(checked_cast(-src_6), None);
    assert_eq!(checked_cast(-src_1_5), None);
    assert_eq!(checked_cast(-src_1), None);
    assert_eq!(checked_cast(-src_0), Some(dst_0));
    assert_eq!(checked_cast(src_0), Some(dst_0));
    assert_eq!(checked_cast(src_1), Some(dst_1));
    assert_eq!(checked_cast(src_1_5), Some(dst_1));
    assert_eq!(checked_cast(src_6), Some(dst_6));
    assert_eq!(checked_cast(src_7ish), Some(dst_7ish));
    assert_eq!(checked_cast(src_8), Some(dst_8));
    assert_eq!(checked_cast(src_9ish), Some(dst_9ish));
    assert_eq!(checked_cast(src_c), Some(dst_c));
    assert_eq!(checked_cast(src_fish), Some(dst_fish));
    if src_nbits == 32 && dst_nbits == 128 {
        assert_eq!(checked_cast(src_max), Some(dst_wmax));
    } else {
        assert_eq!(checked_cast(src_max), None);
    }
    assert_eq!(checked_cast(src_inf), None);
    assert_eq!(checked_cast(src_nan), None);

    assert_eq!(saturating_cast(-src_inf), dst_0);
    assert_eq!(saturating_cast(-src_max), dst_0);
    assert_eq!(saturating_cast(-src_fish), dst_0);
    assert_eq!(saturating_cast(-src_c), dst_0);
    assert_eq!(saturating_cast(-src_9ish), dst_0);
    assert_eq!(saturating_cast(-src_8), dst_0);
    assert_eq!(saturating_cast(-src_7ish), dst_0);
    assert_eq!(saturating_cast(-src_6), dst_0);
    assert_eq!(saturating_cast(-src_1_5), dst_0);
    assert_eq!(saturating_cast(-src_1), dst_0);
    assert_eq!(saturating_cast(-src_0), dst_0);
    assert_eq!(saturating_cast(src_0), dst_0);
    assert_eq!(saturating_cast(src_1), dst_1);
    assert_eq!(saturating_cast(src_1_5), dst_1);
    assert_eq!(saturating_cast(src_6), dst_6);
    assert_eq!(saturating_cast(src_7ish), dst_7ish);
    assert_eq!(saturating_cast(src_8), dst_8);
    assert_eq!(saturating_cast(src_9ish), dst_9ish);
    assert_eq!(saturating_cast(src_c), dst_c);
    assert_eq!(saturating_cast(src_fish), dst_fish);
    if src_nbits == 32 && dst_nbits == 128 {
        assert_eq!(saturating_cast(src_max), dst_wmax);
    } else {
        assert_eq!(saturating_cast(src_max), dst_f);
    }
    assert_eq!(saturating_cast(src_inf), dst_f);

    assert_eq!(wrapping_cast(-src_max), dst_wmax_neg);
    assert_eq!(wrapping_cast(-src_fish), dst_1ish);
    assert_eq!(wrapping_cast(-src_c), dst_4);
    assert_eq!(wrapping_cast(-src_9ish), dst_7ish);
    assert_eq!(wrapping_cast(-src_8), dst_8);
    assert_eq!(wrapping_cast(-src_7ish), dst_9ish);
    assert_eq!(wrapping_cast(-src_6), dst_a);
    assert_eq!(wrapping_cast(-src_1_5), dst_f);
    assert_eq!(wrapping_cast(-src_1), dst_f);
    assert_eq!(wrapping_cast(-src_0), dst_0);
    assert_eq!(wrapping_cast(src_0), dst_0);
    assert_eq!(wrapping_cast(src_1), dst_1);
    assert_eq!(wrapping_cast(src_1_5), dst_1);
    assert_eq!(wrapping_cast(src_6), dst_6);
    assert_eq!(wrapping_cast(src_7ish), dst_7ish);
    assert_eq!(wrapping_cast(src_8), dst_8);
    assert_eq!(wrapping_cast(src_9ish), dst_9ish);
    assert_eq!(wrapping_cast(src_c), dst_c);
    assert_eq!(wrapping_cast(src_fish), dst_fish);
    assert_eq!(wrapping_cast(src_max), dst_wmax);

    assert_eq!(overflowing_cast(-src_max), (dst_wmax_neg, true));
    assert_eq!(overflowing_cast(-src_fish), (dst_1ish, true));
    assert_eq!(overflowing_cast(-src_c), (dst_4, true));
    assert_eq!(overflowing_cast(-src_9ish), (dst_7ish, true));
    assert_eq!(overflowing_cast(-src_8), (dst_8, true));
    assert_eq!(overflowing_cast(-src_7ish), (dst_9ish, true));
    assert_eq!(overflowing_cast(-src_6), (dst_a, true));
    assert_eq!(overflowing_cast(-src_1_5), (dst_f, true));
    assert_eq!(overflowing_cast(-src_1), (dst_f, true));
    assert_eq!(overflowing_cast(-src_0), (dst_0, false));
    assert_eq!(overflowing_cast(src_0), (dst_0, false));
    assert_eq!(overflowing_cast(src_1), (dst_1, false));
    assert_eq!(overflowing_cast(src_1_5), (dst_1, false));
    assert_eq!(overflowing_cast(src_6), (dst_6, false));
    assert_eq!(overflowing_cast(src_7ish), (dst_7ish, false));
    assert_eq!(overflowing_cast(src_8), (dst_8, false));
    assert_eq!(overflowing_cast(src_9ish), (dst_9ish, false));
    assert_eq!(overflowing_cast(src_c), (dst_c, false));
    assert_eq!(overflowing_cast(src_fish), (dst_fish, false));
    if src_nbits == 32 && dst_nbits == 128 {
        assert_eq!(overflowing_cast(src_max), (dst_wmax, false));
    } else {
        assert_eq!(overflowing_cast(src_max), (dst_wmax, true));
    }

    assert_eq!(unwrapped_cast(-src_0), dst_0);
    assert_eq!(unwrapped_cast(src_0), dst_0);
    assert_eq!(unwrapped_cast(src_1), dst_1);
    assert_eq!(unwrapped_cast(src_1_5), dst_1);
    assert_eq!(unwrapped_cast(src_6), dst_6);
    assert_eq!(unwrapped_cast(src_7ish), dst_7ish);
    assert_eq!(unwrapped_cast(src_8), dst_8);
    assert_eq!(unwrapped_cast(src_9ish), dst_9ish);
    assert_eq!(unwrapped_cast(src_c), dst_c);
    assert_eq!(unwrapped_cast(src_fish), dst_fish);
    if src_nbits == 32 && dst_nbits == 128 {
        assert_eq!(unwrapped_cast(src_max), dst_wmax);
    }
}

fn float_to_wrapping_unsigned<Src: Float, Dst: Int>()
where
    Src: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_prec = Src::prec();
    let dst_nbits = mem::size_of::<Dst>() * 8;

    let src_0 = Src::int_shl(0, 0);
    let src_1 = Src::int_shl(1, 0);
    let src_1_5 = Src::int_shl(3, -1);
    let src_8 = Src::int_shl(1, (dst_nbits - 1) as i8);
    let src_1ish = if src_prec > dst_nbits {
        src_1
    } else {
        Src::int_shl(1, (dst_nbits - src_prec) as i8)
    };
    let src_7ish = src_8 - src_1ish;
    let src_6 = Src::int_shl(6, (dst_nbits - 4) as i8);
    let src_9ish = src_8 + src_1ish;
    let src_c = Src::int_shl(12, (dst_nbits - 4) as i8);
    let src_fish = src_8 + src_7ish;
    let src_max = Src::max();
    let src_inf = Src::inf();
    let src_nan = Src::nan();

    let dst_0 = Wrapping(wrapping_cast(src_0));
    let dst_1 = Wrapping(wrapping_cast(src_1));
    let dst_1ish = Wrapping(wrapping_cast(-src_fish));
    let dst_fish = Wrapping(wrapping_cast(src_fish));
    let dst_4 = Wrapping(wrapping_cast(-src_c));
    let dst_6 = Wrapping(wrapping_cast(src_6));
    let dst_7ish = Wrapping(wrapping_cast(src_7ish));
    let dst_8 = Wrapping(wrapping_cast(src_8));
    let dst_9ish = Wrapping(wrapping_cast(src_9ish));
    let dst_a = Wrapping(wrapping_cast(-src_6));
    let dst_c = Wrapping(wrapping_cast(src_c));
    let dst_f = Wrapping(wrapping_cast(-src_1));
    let dst_wmax = Wrapping(wrapping_cast(src_max));
    let dst_wmax_neg = Wrapping(wrapping_cast(-src_max));

    assert_eq!(cast(-src_max), dst_wmax_neg);
    assert_eq!(cast(-src_fish), dst_1ish);
    assert_eq!(cast(-src_c), dst_4);
    assert_eq!(cast(-src_9ish), dst_7ish);
    assert_eq!(cast(-src_8), dst_8);
    assert_eq!(cast(-src_7ish), dst_9ish);
    assert_eq!(cast(-src_6), dst_a);
    assert_eq!(cast(-src_1_5), dst_f);
    assert_eq!(cast(-src_1), dst_f);
    assert_eq!(cast(-src_0), dst_0);
    assert_eq!(cast(src_0), dst_0);
    assert_eq!(cast(src_1), dst_1);
    assert_eq!(cast(src_1_5), dst_1);
    assert_eq!(cast(src_6), dst_6);
    assert_eq!(cast(src_7ish), dst_7ish);
    assert_eq!(cast(src_8), dst_8);
    assert_eq!(cast(src_9ish), dst_9ish);
    assert_eq!(cast(src_c), dst_c);
    assert_eq!(cast(src_fish), dst_fish);
    assert_eq!(cast(src_max), dst_wmax);

    assert_eq!(checked_cast(-src_nan), None);
    assert_eq!(checked_cast(-src_inf), None);
    assert_eq!(checked_cast(-src_max), Some(dst_wmax_neg));
    assert_eq!(checked_cast(-src_fish), Some(dst_1ish));
    assert_eq!(checked_cast(-src_c), Some(dst_4));
    assert_eq!(checked_cast(-src_9ish), Some(dst_7ish));
    assert_eq!(checked_cast(-src_8), Some(dst_8));
    assert_eq!(checked_cast(-src_7ish), Some(dst_9ish));
    assert_eq!(checked_cast(-src_6), Some(dst_a));
    assert_eq!(checked_cast(-src_1_5), Some(dst_f));
    assert_eq!(checked_cast(-src_1), Some(dst_f));
    assert_eq!(checked_cast(-src_0), Some(dst_0));
    assert_eq!(checked_cast(src_0), Some(dst_0));
    assert_eq!(checked_cast(src_1), Some(dst_1));
    assert_eq!(checked_cast(src_1_5), Some(dst_1));
    assert_eq!(checked_cast(src_6), Some(dst_6));
    assert_eq!(checked_cast(src_7ish), Some(dst_7ish));
    assert_eq!(checked_cast(src_8), Some(dst_8));
    assert_eq!(checked_cast(src_9ish), Some(dst_9ish));
    assert_eq!(checked_cast(src_c), Some(dst_c));
    assert_eq!(checked_cast(src_fish), Some(dst_fish));
    assert_eq!(checked_cast(src_max), Some(dst_wmax));
    assert_eq!(checked_cast(src_inf), None);
    assert_eq!(checked_cast(src_nan), None);

    assert_eq!(unwrapped_cast(-src_max), dst_wmax_neg);
    assert_eq!(unwrapped_cast(-src_fish), dst_1ish);
    assert_eq!(unwrapped_cast(-src_c), dst_4);
    assert_eq!(unwrapped_cast(-src_9ish), dst_7ish);
    assert_eq!(unwrapped_cast(-src_8), dst_8);
    assert_eq!(unwrapped_cast(-src_7ish), dst_9ish);
    assert_eq!(unwrapped_cast(-src_6), dst_a);
    assert_eq!(unwrapped_cast(-src_1_5), dst_f);
    assert_eq!(unwrapped_cast(-src_1), dst_f);
    assert_eq!(unwrapped_cast(-src_0), dst_0);
    assert_eq!(unwrapped_cast(src_0), dst_0);
    assert_eq!(unwrapped_cast(src_1), dst_1);
    assert_eq!(unwrapped_cast(src_1_5), dst_1);
    assert_eq!(unwrapped_cast(src_6), dst_6);
    assert_eq!(unwrapped_cast(src_7ish), dst_7ish);
    assert_eq!(unwrapped_cast(src_8), dst_8);
    assert_eq!(unwrapped_cast(src_9ish), dst_9ish);
    assert_eq!(unwrapped_cast(src_c), dst_c);
    assert_eq!(unwrapped_cast(src_fish), dst_fish);
    assert_eq!(unwrapped_cast(src_max), dst_wmax);
}

fn round_to_nonwrapping_unsigned<Src: Float, Dst: Int>()
where
    Round<Src>: Cast<Dst>
        + CheckedCast<Dst>
        + SaturatingCast<Dst>
        + WrappingCast<Dst>
        + OverflowingCast<Dst>
        + UnwrappedCast<Dst>,
{
    let src_prec = Src::prec();
    let src_nbits = mem::size_of::<Src>() * 8;
    let dst_nbits = mem::size_of::<Dst>() * 8;

    let src_0 = Src::int_shl(0, 0);
    let src_1 = Src::int_shl(1, 0);
    let src_1_5 = Src::int_shl(3, -1);
    let src_8 = Src::int_shl(1, (dst_nbits - 1) as i8);
    let src_1ish = if src_prec > dst_nbits {
        src_1
    } else {
        Src::int_shl(1, (dst_nbits - src_prec) as i8)
    };
    let src_7ish = src_8 - src_1ish;
    let src_6 = Src::int_shl(6, (dst_nbits - 4) as i8);
    let src_9ish = src_8 + src_1ish;
    let src_c = Src::int_shl(12, (dst_nbits - 4) as i8);
    let src_fish = src_8 + src_7ish;
    let src_max = Src::max();
    let src_inf = Src::inf();
    let src_nan = Src::nan();

    let dst_0 = Dst::zero();
    let dst_1 = Dst::one();
    let dst_2 = dst_1 + dst_1;
    let (dst_1ish, dst_fish) = if src_prec > dst_nbits {
        (dst_1, !dst_1 + dst_1)
    } else {
        let ish = dst_1 << (dst_nbits - src_prec);
        (ish, !ish + dst_1)
    };
    let dst_4 = dst_1 << (dst_nbits - 2);
    let dst_6 = dst_4 + (dst_4 >> 1);
    let dst_7ish = dst_4 + (dst_4 - dst_1ish);
    let dst_8 = dst_1 << (dst_nbits - 1);
    let dst_7 = !dst_8;
    let dst_9ish = dst_8 + dst_1ish;
    let dst_a = dst_6 + dst_4;
    let dst_c = dst_8 + dst_4;
    let dst_e = dst_7 + dst_7;
    let dst_f = dst_8 + dst_7;
    let (dst_wmax, dst_wmax_neg) = if src_nbits == 32 && dst_nbits == 128 {
        let max = !dst_0 << (dst_nbits - src_prec);
        (max, !max + dst_1)
    } else {
        (dst_0, dst_0)
    };

    assert_eq!(cast(Round(-src_0)), dst_0);
    assert_eq!(cast(Round(src_0)), dst_0);
    assert_eq!(cast(Round(src_1)), dst_1);
    assert_eq!(cast(Round(src_1_5)), dst_2);
    assert_eq!(cast(Round(src_6)), dst_6);
    assert_eq!(cast(Round(src_7ish)), dst_7ish);
    assert_eq!(cast(Round(src_8)), dst_8);
    assert_eq!(cast(Round(src_9ish)), dst_9ish);
    assert_eq!(cast(Round(src_c)), dst_c);
    assert_eq!(cast(Round(src_fish)), dst_fish);
    if src_nbits == 32 && dst_nbits == 128 {
        assert_eq!(cast(Round(src_max)), dst_wmax);
    }

    assert_eq!(checked_cast(Round(-src_nan)), None);
    assert_eq!(checked_cast(Round(-src_inf)), None);
    assert_eq!(checked_cast(Round(-src_max)), None);
    assert_eq!(checked_cast(Round(-src_fish)), None);
    assert_eq!(checked_cast(Round(-src_c)), None);
    assert_eq!(checked_cast(Round(-src_9ish)), None);
    assert_eq!(checked_cast(Round(-src_8)), None);
    assert_eq!(checked_cast(Round(-src_7ish)), None);
    assert_eq!(checked_cast(Round(-src_6)), None);
    assert_eq!(checked_cast(Round(-src_1_5)), None);
    assert_eq!(checked_cast(Round(-src_1)), None);
    assert_eq!(checked_cast(Round(-src_0)), Some(dst_0));
    assert_eq!(checked_cast(Round(src_0)), Some(dst_0));
    assert_eq!(checked_cast(Round(src_1)), Some(dst_1));
    assert_eq!(checked_cast(Round(src_1_5)), Some(dst_2));
    assert_eq!(checked_cast(Round(src_6)), Some(dst_6));
    assert_eq!(checked_cast(Round(src_7ish)), Some(dst_7ish));
    assert_eq!(checked_cast(Round(src_8)), Some(dst_8));
    assert_eq!(checked_cast(Round(src_9ish)), Some(dst_9ish));
    assert_eq!(checked_cast(Round(src_c)), Some(dst_c));
    assert_eq!(checked_cast(Round(src_fish)), Some(dst_fish));
    if src_nbits == 32 && dst_nbits == 128 {
        assert_eq!(checked_cast(Round(src_max)), Some(dst_wmax));
    } else {
        assert_eq!(checked_cast(Round(src_max)), None);
    }
    assert_eq!(checked_cast(Round(src_inf)), None);
    assert_eq!(checked_cast(Round(src_nan)), None);

    assert_eq!(saturating_cast(Round(-src_inf)), dst_0);
    assert_eq!(saturating_cast(Round(-src_max)), dst_0);
    assert_eq!(saturating_cast(Round(-src_fish)), dst_0);
    assert_eq!(saturating_cast(Round(-src_c)), dst_0);
    assert_eq!(saturating_cast(Round(-src_9ish)), dst_0);
    assert_eq!(saturating_cast(Round(-src_8)), dst_0);
    assert_eq!(saturating_cast(Round(-src_7ish)), dst_0);
    assert_eq!(saturating_cast(Round(-src_6)), dst_0);
    assert_eq!(saturating_cast(Round(-src_1_5)), dst_0);
    assert_eq!(saturating_cast(Round(-src_1)), dst_0);
    assert_eq!(saturating_cast(Round(-src_0)), dst_0);
    assert_eq!(saturating_cast(Round(src_0)), dst_0);
    assert_eq!(saturating_cast(Round(src_1)), dst_1);
    assert_eq!(saturating_cast(Round(src_1_5)), dst_2);
    assert_eq!(saturating_cast(Round(src_6)), dst_6);
    assert_eq!(saturating_cast(Round(src_7ish)), dst_7ish);
    assert_eq!(saturating_cast(Round(src_8)), dst_8);
    assert_eq!(saturating_cast(Round(src_9ish)), dst_9ish);
    assert_eq!(saturating_cast(Round(src_c)), dst_c);
    assert_eq!(saturating_cast(Round(src_fish)), dst_fish);
    if src_nbits == 32 && dst_nbits == 128 {
        assert_eq!(saturating_cast(Round(src_max)), dst_wmax);
    } else {
        assert_eq!(saturating_cast(Round(src_max)), dst_f);
    }
    assert_eq!(saturating_cast(Round(src_inf)), dst_f);

    assert_eq!(wrapping_cast(Round(-src_max)), dst_wmax_neg);
    assert_eq!(wrapping_cast(Round(-src_fish)), dst_1ish);
    assert_eq!(wrapping_cast(Round(-src_c)), dst_4);
    assert_eq!(wrapping_cast(Round(-src_9ish)), dst_7ish);
    assert_eq!(wrapping_cast(Round(-src_8)), dst_8);
    assert_eq!(wrapping_cast(Round(-src_7ish)), dst_9ish);
    assert_eq!(wrapping_cast(Round(-src_6)), dst_a);
    assert_eq!(wrapping_cast(Round(-src_1_5)), dst_e);
    assert_eq!(wrapping_cast(Round(-src_1)), dst_f);
    assert_eq!(wrapping_cast(Round(-src_0)), dst_0);
    assert_eq!(wrapping_cast(Round(src_0)), dst_0);
    assert_eq!(wrapping_cast(Round(src_1)), dst_1);
    assert_eq!(wrapping_cast(Round(src_1_5)), dst_2);
    assert_eq!(wrapping_cast(Round(src_6)), dst_6);
    assert_eq!(wrapping_cast(Round(src_7ish)), dst_7ish);
    assert_eq!(wrapping_cast(Round(src_8)), dst_8);
    assert_eq!(wrapping_cast(Round(src_9ish)), dst_9ish);
    assert_eq!(wrapping_cast(Round(src_c)), dst_c);
    assert_eq!(wrapping_cast(Round(src_fish)), dst_fish);
    assert_eq!(wrapping_cast(Round(src_max)), dst_wmax);

    assert_eq!(overflowing_cast(Round(-src_max)), (dst_wmax_neg, true));
    assert_eq!(overflowing_cast(Round(-src_fish)), (dst_1ish, true));
    assert_eq!(overflowing_cast(Round(-src_c)), (dst_4, true));
    assert_eq!(overflowing_cast(Round(-src_9ish)), (dst_7ish, true));
    assert_eq!(overflowing_cast(Round(-src_8)), (dst_8, true));
    assert_eq!(overflowing_cast(Round(-src_7ish)), (dst_9ish, true));
    assert_eq!(overflowing_cast(Round(-src_6)), (dst_a, true));
    assert_eq!(overflowing_cast(Round(-src_1_5)), (dst_e, true));
    assert_eq!(overflowing_cast(Round(-src_1)), (dst_f, true));
    assert_eq!(overflowing_cast(Round(-src_0)), (dst_0, false));
    assert_eq!(overflowing_cast(Round(src_0)), (dst_0, false));
    assert_eq!(overflowing_cast(Round(src_1)), (dst_1, false));
    assert_eq!(overflowing_cast(Round(src_1_5)), (dst_2, false));
    assert_eq!(overflowing_cast(Round(src_6)), (dst_6, false));
    assert_eq!(overflowing_cast(Round(src_7ish)), (dst_7ish, false));
    assert_eq!(overflowing_cast(Round(src_8)), (dst_8, false));
    assert_eq!(overflowing_cast(Round(src_9ish)), (dst_9ish, false));
    assert_eq!(overflowing_cast(Round(src_c)), (dst_c, false));
    assert_eq!(overflowing_cast(Round(src_fish)), (dst_fish, false));
    if src_nbits == 32 && dst_nbits == 128 {
        assert_eq!(overflowing_cast(Round(src_max)), (dst_wmax, false));
    } else {
        assert_eq!(overflowing_cast(Round(src_max)), (dst_wmax, true));
    }

    assert_eq!(unwrapped_cast(Round(-src_0)), dst_0);
    assert_eq!(unwrapped_cast(Round(src_0)), dst_0);
    assert_eq!(unwrapped_cast(Round(src_1)), dst_1);
    assert_eq!(unwrapped_cast(Round(src_1_5)), dst_2);
    assert_eq!(unwrapped_cast(Round(src_6)), dst_6);
    assert_eq!(unwrapped_cast(Round(src_7ish)), dst_7ish);
    assert_eq!(unwrapped_cast(Round(src_8)), dst_8);
    assert_eq!(unwrapped_cast(Round(src_9ish)), dst_9ish);
    assert_eq!(unwrapped_cast(Round(src_c)), dst_c);
    assert_eq!(unwrapped_cast(Round(src_fish)), dst_fish);
    if src_nbits == 32 && dst_nbits == 128 {
        assert_eq!(unwrapped_cast(Round(src_max)), dst_wmax);
    }
}

fn round_to_wrapping_unsigned<Src: Float, Dst: Int>()
where
    Round<Src>: WrappingCast<Dst>
        + Cast<Wrapping<Dst>>
        + CheckedCast<Wrapping<Dst>>
        + UnwrappedCast<Wrapping<Dst>>,
    Wrapping<Dst>: Int,
{
    let src_prec = Src::prec();
    let dst_nbits = mem::size_of::<Dst>() * 8;

    let src_0 = Src::int_shl(0, 0);
    let src_1 = Src::int_shl(1, 0);
    let src_1_5 = Src::int_shl(3, -1);
    let src_8 = Src::int_shl(1, (dst_nbits - 1) as i8);
    let src_1ish = if src_prec > dst_nbits {
        src_1
    } else {
        Src::int_shl(1, (dst_nbits - src_prec) as i8)
    };
    let src_7ish = src_8 - src_1ish;
    let src_6 = Src::int_shl(6, (dst_nbits - 4) as i8);
    let src_9ish = src_8 + src_1ish;
    let src_c = Src::int_shl(12, (dst_nbits - 4) as i8);
    let src_fish = src_8 + src_7ish;
    let src_max = Src::max();
    let src_inf = Src::inf();
    let src_nan = Src::nan();

    let dst_0 = Wrapping(wrapping_cast(Round(src_0)));
    let dst_1 = Wrapping(wrapping_cast(Round(src_1)));
    let dst_2 = Wrapping(wrapping_cast(Round(src_1_5)));
    let dst_1ish = Wrapping(wrapping_cast(Round(-src_fish)));
    let dst_fish = Wrapping(wrapping_cast(Round(src_fish)));
    let dst_4 = Wrapping(wrapping_cast(Round(-src_c)));
    let dst_6 = Wrapping(wrapping_cast(Round(src_6)));
    let dst_7ish = Wrapping(wrapping_cast(Round(src_7ish)));
    let dst_8 = Wrapping(wrapping_cast(Round(src_8)));
    let dst_9ish = Wrapping(wrapping_cast(Round(src_9ish)));
    let dst_a = Wrapping(wrapping_cast(Round(-src_6)));
    let dst_c = Wrapping(wrapping_cast(Round(src_c)));
    let dst_e = Wrapping(wrapping_cast(Round(-src_1_5)));
    let dst_f = Wrapping(wrapping_cast(Round(-src_1)));
    let dst_wmax = Wrapping(wrapping_cast(Round(src_max)));
    let dst_wmax_neg = Wrapping(wrapping_cast(Round(-src_max)));

    assert_eq!(cast(Round(-src_max)), dst_wmax_neg);
    assert_eq!(cast(Round(-src_fish)), dst_1ish);
    assert_eq!(cast(Round(-src_c)), dst_4);
    assert_eq!(cast(Round(-src_9ish)), dst_7ish);
    assert_eq!(cast(Round(-src_8)), dst_8);
    assert_eq!(cast(Round(-src_7ish)), dst_9ish);
    assert_eq!(cast(Round(-src_6)), dst_a);
    assert_eq!(cast(Round(-src_1_5)), dst_e);
    assert_eq!(cast(Round(-src_1)), dst_f);
    assert_eq!(cast(Round(-src_0)), dst_0);
    assert_eq!(cast(Round(src_0)), dst_0);
    assert_eq!(cast(Round(src_1)), dst_1);
    assert_eq!(cast(Round(src_1_5)), dst_2);
    assert_eq!(cast(Round(src_6)), dst_6);
    assert_eq!(cast(Round(src_7ish)), dst_7ish);
    assert_eq!(cast(Round(src_8)), dst_8);
    assert_eq!(cast(Round(src_9ish)), dst_9ish);
    assert_eq!(cast(Round(src_c)), dst_c);
    assert_eq!(cast(Round(src_fish)), dst_fish);
    assert_eq!(cast(Round(src_max)), dst_wmax);

    assert_eq!(checked_cast(Round(-src_nan)), None);
    assert_eq!(checked_cast(Round(-src_inf)), None);
    assert_eq!(checked_cast(Round(-src_max)), Some(dst_wmax_neg));
    assert_eq!(checked_cast(Round(-src_fish)), Some(dst_1ish));
    assert_eq!(checked_cast(Round(-src_c)), Some(dst_4));
    assert_eq!(checked_cast(Round(-src_9ish)), Some(dst_7ish));
    assert_eq!(checked_cast(Round(-src_8)), Some(dst_8));
    assert_eq!(checked_cast(Round(-src_7ish)), Some(dst_9ish));
    assert_eq!(checked_cast(Round(-src_6)), Some(dst_a));
    assert_eq!(checked_cast(Round(-src_1_5)), Some(dst_e));
    assert_eq!(checked_cast(Round(-src_1)), Some(dst_f));
    assert_eq!(checked_cast(Round(-src_0)), Some(dst_0));
    assert_eq!(checked_cast(Round(src_0)), Some(dst_0));
    assert_eq!(checked_cast(Round(src_1)), Some(dst_1));
    assert_eq!(checked_cast(Round(src_1_5)), Some(dst_2));
    assert_eq!(checked_cast(Round(src_6)), Some(dst_6));
    assert_eq!(checked_cast(Round(src_7ish)), Some(dst_7ish));
    assert_eq!(checked_cast(Round(src_8)), Some(dst_8));
    assert_eq!(checked_cast(Round(src_9ish)), Some(dst_9ish));
    assert_eq!(checked_cast(Round(src_c)), Some(dst_c));
    assert_eq!(checked_cast(Round(src_fish)), Some(dst_fish));
    assert_eq!(checked_cast(Round(src_max)), Some(dst_wmax));
    assert_eq!(checked_cast(Round(src_inf)), None);
    assert_eq!(checked_cast(Round(src_nan)), None);

    assert_eq!(unwrapped_cast(Round(-src_max)), dst_wmax_neg);
    assert_eq!(unwrapped_cast(Round(-src_fish)), dst_1ish);
    assert_eq!(unwrapped_cast(Round(-src_c)), dst_4);
    assert_eq!(unwrapped_cast(Round(-src_9ish)), dst_7ish);
    assert_eq!(unwrapped_cast(Round(-src_8)), dst_8);
    assert_eq!(unwrapped_cast(Round(-src_7ish)), dst_9ish);
    assert_eq!(unwrapped_cast(Round(-src_6)), dst_a);
    assert_eq!(unwrapped_cast(Round(-src_1_5)), dst_e);
    assert_eq!(unwrapped_cast(Round(-src_1)), dst_f);
    assert_eq!(unwrapped_cast(Round(-src_0)), dst_0);
    assert_eq!(unwrapped_cast(Round(src_0)), dst_0);
    assert_eq!(unwrapped_cast(Round(src_1)), dst_1);
    assert_eq!(unwrapped_cast(Round(src_1_5)), dst_2);
    assert_eq!(unwrapped_cast(Round(src_6)), dst_6);
    assert_eq!(unwrapped_cast(Round(src_7ish)), dst_7ish);
    assert_eq!(unwrapped_cast(Round(src_8)), dst_8);
    assert_eq!(unwrapped_cast(Round(src_9ish)), dst_9ish);
    assert_eq!(unwrapped_cast(Round(src_c)), dst_c);
    assert_eq!(unwrapped_cast(Round(src_fish)), dst_fish);
    assert_eq!(unwrapped_cast(Round(src_max)), dst_wmax);
}

fn float_to_signed<Src: Float, Dst: Int>()
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
    Round<Src>: Cast<Dst>
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
    float_to_nonwrapping_signed::<Src, Dst>();
    float_to_wrapping_signed::<Src, Dst>();
    round_to_nonwrapping_signed::<Src, Dst>();
    round_to_wrapping_signed::<Src, Dst>();
}

fn float_to_unsigned<Src: Float, Dst: Int>()
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
    Round<Src>: Cast<Dst>
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
    float_to_nonwrapping_unsigned::<Src, Dst>();
    float_to_wrapping_unsigned::<Src, Dst>();
    round_to_nonwrapping_unsigned::<Src, Dst>();
    round_to_wrapping_unsigned::<Src, Dst>();
}

#[test]
fn float_to_int() {
    float_to_signed::<f32, i8>();
    float_to_signed::<f32, i16>();
    float_to_signed::<f32, i32>();
    float_to_signed::<f32, i64>();
    float_to_signed::<f32, i128>();
    float_to_signed::<f32, isize>();

    float_to_unsigned::<f32, u8>();
    float_to_unsigned::<f32, u16>();
    float_to_unsigned::<f32, u32>();
    float_to_unsigned::<f32, u64>();
    float_to_unsigned::<f32, u128>();
    float_to_unsigned::<f32, usize>();

    float_to_signed::<f64, i8>();
    float_to_signed::<f64, i16>();
    float_to_signed::<f64, i32>();
    float_to_signed::<f64, i64>();
    float_to_signed::<f64, i128>();
    float_to_signed::<f64, isize>();

    float_to_unsigned::<f64, u8>();
    float_to_unsigned::<f64, u16>();
    float_to_unsigned::<f64, u32>();
    float_to_unsigned::<f64, u64>();
    float_to_unsigned::<f64, u128>();
    float_to_unsigned::<f64, usize>();
}

#[test]
fn rounding() {
    assert_eq!(cast::<Round<f64>, i8>(Round(-0.5 + f64::EPSILON / 4.0)), 0);
    assert_eq!(cast::<Round<f64>, i8>(Round(-0.5)), 0);
    assert_eq!(cast::<Round<f64>, i8>(Round(-0.5 - f64::EPSILON / 2.0)), -1);

    assert_eq!(cast::<Round<f64>, i8>(Round(-1.0 + f64::EPSILON / 2.0)), -1);
    assert_eq!(cast::<Round<f64>, i8>(Round(-1.0)), -1);
    assert_eq!(cast::<Round<f64>, i8>(Round(-1.0 - f64::EPSILON)), -1);

    assert_eq!(cast::<Round<f64>, i8>(Round(-1.5 + f64::EPSILON)), -1);
    assert_eq!(cast::<Round<f64>, i8>(Round(-1.5)), -2);
    assert_eq!(cast::<Round<f64>, i8>(Round(-1.5 - f64::EPSILON)), -2);

    assert_eq!(cast::<Round<f64>, i8>(Round(2.0 - f64::EPSILON)), 2);
    assert_eq!(cast::<Round<f64>, i8>(Round(2.0)), 2);
    assert_eq!(cast::<Round<f64>, i8>(Round(2.0 + f64::EPSILON * 2.0)), 2);

    assert_eq!(cast::<Round<f64>, i8>(Round(2.5 - f64::EPSILON * 2.0)), 2);
    assert_eq!(cast::<Round<f64>, i8>(Round(2.5)), 2);
    assert_eq!(cast::<Round<f64>, i8>(Round(2.5 + f64::EPSILON * 2.0)), 3);

    assert_eq!(cast::<Round<f64>, i8>(Round(3.5 - f64::EPSILON * 2.0)), 3);
    assert_eq!(cast::<Round<f64>, i8>(Round(3.5)), 4);
    assert_eq!(cast::<Round<f64>, i8>(Round(3.5 + f64::EPSILON * 2.0)), 4);

    assert_eq!(cast::<Round<f64>, i128>(Round(0.5 - f64::EPSILON / 4.0)), 0);
    assert_eq!(cast::<Round<f64>, i128>(Round(0.5)), 0);
    assert_eq!(cast::<Round<f64>, i128>(Round(0.5 + f64::EPSILON / 2.0)), 1);

    assert_eq!(cast::<Round<f64>, i128>(Round(1.0 - f64::EPSILON / 2.0)), 1);
    assert_eq!(cast::<Round<f64>, i128>(Round(1.0)), 1);
    assert_eq!(cast::<Round<f64>, i128>(Round(1.0 + f64::EPSILON)), 1);

    assert_eq!(cast::<Round<f64>, i128>(Round(1.5 - f64::EPSILON)), 1);
    assert_eq!(cast::<Round<f64>, i128>(Round(1.5)), 2);
    assert_eq!(cast::<Round<f64>, i128>(Round(1.5 + f64::EPSILON)), 2);

    assert_eq!(cast::<Round<f64>, i128>(Round(-2.0 + f64::EPSILON)), -2);
    assert_eq!(cast::<Round<f64>, i128>(Round(-2.0)), -2);
    assert_eq!(
        cast::<Round<f64>, i128>(Round(-2.0 - f64::EPSILON * 2.0)),
        -2
    );

    assert_eq!(
        cast::<Round<f64>, i128>(Round(-2.5 + f64::EPSILON * 2.0)),
        -2
    );
    assert_eq!(cast::<Round<f64>, i128>(Round(-2.5)), -2);
    assert_eq!(
        cast::<Round<f64>, i128>(Round(-2.5 - f64::EPSILON * 2.0)),
        -3
    );

    assert_eq!(
        cast::<Round<f64>, i128>(Round(-3.5 + f64::EPSILON * 2.0)),
        -3
    );
    assert_eq!(cast::<Round<f64>, i128>(Round(-3.5)), -4);
    assert_eq!(
        cast::<Round<f64>, i128>(Round(-3.5 - f64::EPSILON * 2.0)),
        -4
    );
}

#[test]
#[should_panic(expected = "NaN")]
fn nan_saturating_as_panic() {
    let _ = saturating_cast::<f32, i32>(f32::NAN);
}

#[test]
#[should_panic(expected = "NaN")]
fn nan_overflowing_as_panic() {
    let _ = overflowing_cast::<f32, i32>(f32::NAN);
}

#[test]
#[should_panic(expected = "NaN")]
fn nan_unwrapped_as_panic() {
    let _ = unwrapped_cast::<f32, i32>(f32::NAN);
}

#[test]
#[should_panic(expected = "infinite")]
fn infinite_overflowing_as_panic() {
    let _ = overflowing_cast::<f32, i32>(f32::INFINITY);
}

#[test]
#[should_panic(expected = "infinite")]
fn infinite_unwrapped_as_panic() {
    let _ = unwrapped_cast::<f32, i32>(f32::INFINITY);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "overflow")]
fn large_float_as_panic() {
    let _ = cast::<f32, i8>(128.0);
}

#[cfg(not(debug_assertions))]
#[test]
fn large_float_as_wrap() {
    assert_eq!(cast::<f32, i8>(128.0), -128);
    assert_eq!(cast::<f32, u8>(-127.0), 129);
}

#[test]
#[should_panic(expected = "overflow")]
fn large_float_unwrapped_as_panic() {
    let _ = unwrapped_cast::<f32, i8>(128.0);
}

#[test]
fn display() {
    use std::format;
    let f = 1e-50 / 3.0;
    let r = Round(f);
    assert_eq!(format!("{}", f), format!("{}", r));
    assert_eq!(format!("{:?}", f), format!("{:?}", r));
    assert_eq!(format!("{:e}", f), format!("{:e}", r));
    assert_eq!(format!("{:E}", f), format!("{:E}", r));
}
