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

use crate::{cast, checked_cast, unwrapped_cast};
use core::{f32, f64};

macro_rules! slice_to_float {
    ($vals: expr) => {
        for &val in $vals {
            if val != val {
                assert!(cast::<_, f32>(val).is_nan());
                assert!(checked_cast::<_, f32>(val).unwrap().is_nan());
                assert!(unwrapped_cast::<_, f32>(val).is_nan());
                assert!(cast::<_, f64>(val).is_nan());
                assert!(checked_cast::<_, f64>(val).unwrap().is_nan());
                assert!(unwrapped_cast::<_, f64>(val).is_nan());
            } else {
                assert_eq!(cast::<_, f32>(val), val as f32);
                assert_eq!(checked_cast::<_, f32>(val), Some(val as f32));
                assert_eq!(unwrapped_cast::<_, f32>(val), val as f32);
                assert_eq!(cast::<_, f64>(val), val as f64);
                assert_eq!(checked_cast::<_, f64>(val), Some(val as f64));
                assert_eq!(unwrapped_cast::<_, f64>(val), val as f64);
            }
        }
    };
}

#[test]
fn to_float() {
    let small_i = &[
        i8::min_value(),
        i8::min_value() + 1,
        -1,
        0,
        1,
        i8::max_value() - 1,
        i8::max_value(),
    ];
    let small_u = &[0, 1, u8::max_value() - 1, u8::max_value()];
    let small_f = &[
        0.0,
        f32::MIN_POSITIVE,
        1.0,
        1.5,
        2.0,
        f32::MAX,
        f32::INFINITY,
        f32::NAN,
    ];
    let big_i = &[
        i128::min_value(),
        i128::min_value() + 1,
        -1,
        0,
        1,
        i128::max_value() - 1,
        i128::max_value(),
    ];
    let big_u = &[0, 1, u128::max_value() - 1, u128::max_value()];
    let big_f = &[
        0.0,
        f64::MIN_POSITIVE,
        1.0,
        1.5,
        2.0,
        f64::MAX,
        f64::INFINITY,
        f64::NAN,
    ];

    slice_to_float!(small_i);
    slice_to_float!(small_u);
    slice_to_float!(small_f);
    slice_to_float!(big_i);
    slice_to_float!(big_u);
    slice_to_float!(big_f);
}

#[test]
fn specific_to_float() {
    // 0XFFFF_FE80 in 24 bits of precision becomes 0xFFFF_FE00
    assert_eq!(
        cast::<_, f32>(0xFFFF_FE80u32),
        (24f32.exp2() - 2.0) * 8f32.exp2()
    );
    // 0XFFFF_FE80..=0xFFFF_FF7F in 24 bits of precision become 0xFFFF_FF00
    assert_eq!(
        cast::<_, f32>(0xFFFF_FE81u32),
        (24f32.exp2() - 1.0) * 8f32.exp2()
    );
    assert_eq!(
        cast::<_, f32>(0xFFFF_FF00u32),
        (24f32.exp2() - 1.0) * 8f32.exp2()
    );
    assert_eq!(
        cast::<_, f32>(0xFFFF_FF7Fu32),
        (24f32.exp2() - 1.0) * 8f32.exp2()
    );
    // 0xFFFF_FF80 in 24 bits of precision becoms 0x1_0000_0000
    assert_eq!(cast::<_, f32>(0xFFFF_FF80u32), 24f32.exp2() * 8f32.exp2());
    assert_eq!(cast::<_, f32>(0xFFFF_FFFFu32), 24f32.exp2() * 8f32.exp2());

    // Same as above, but source is 128-bit instead of 32-bit.
    //   * (24f32.exp2() - 1.0) * 104f32.exp2() == f32::MAX
    //   * 24f32.exp2() * 104f32.exp2() > f32::MAX, overflows to f32::INFINITY
    assert_eq!(
        cast::<_, f32>(0xFFFF_FE80_0000_0000_0000_0000_0000_0000u128),
        (24f32.exp2() - 2.0) * 104f32.exp2()
    );
    assert_eq!(
        cast::<_, f32>(0xFFFF_FE80_0000_0000_0000_0000_0000_0001u128),
        f32::MAX
    );
    assert_eq!(
        cast::<_, f32>(0xFFFF_FF00_0000_0000_0000_0000_0000_0000u128),
        f32::MAX
    );
    assert_eq!(
        cast::<_, f32>(0xFFFF_FF7F_FFFF_FFFF_FFFF_FFFF_FFFF_FFFFu128),
        f32::MAX
    );
    assert_eq!(
        cast::<_, f32>(0xFFFF_FF80_0000_0000_0000_0000_0000_0000u128),
        f32::INFINITY
    );
    assert_eq!(
        cast::<_, f32>(0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFFu128),
        f32::INFINITY
    );

    assert_eq!(cast::<_, f32>(f64::MAX), f32::INFINITY);
    assert_eq!(cast::<_, f32>(-f64::MAX), f32::NEG_INFINITY);
    assert_eq!(cast::<_, f32>(-f64::MAX), f32::NEG_INFINITY);
    assert_eq!(cast::<_, f32>(f64::from(f32::MAX) + 1.0), f32::MAX);
}
