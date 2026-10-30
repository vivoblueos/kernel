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
    cast, checked_cast, overflowing_cast, saturating_cast, wrapping_cast, Cast, CheckedCast,
    OverflowingCast, Round, SaturatingCast, UnwrappedCast, WrappingCast,
};
use core::{mem, num::Wrapping};

macro_rules! bool_to_int {
    ($Dst:ty) => {
        impl Cast<$Dst> for bool {
            #[inline]
            fn cast(self) -> $Dst {
                self as $Dst
            }
        }

        impl CheckedCast<$Dst> for bool {
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                Some(self as $Dst)
            }
        }

        impl SaturatingCast<$Dst> for bool {
            #[inline]
            fn saturating_cast(self) -> $Dst {
                self as $Dst
            }
        }

        impl WrappingCast<$Dst> for bool {
            #[inline]
            fn wrapping_cast(self) -> $Dst {
                self as $Dst
            }
        }

        impl OverflowingCast<$Dst> for bool {
            #[inline]
            fn overflowing_cast(self) -> ($Dst, bool) {
                (self as $Dst, false)
            }
        }

        impl UnwrappedCast<$Dst> for bool {
            #[inline]
            fn unwrapped_cast(self) -> $Dst {
                self as $Dst
            }
        }
    };
}

macro_rules! common {
    ($Src:ty => $Dst:ty) => {
        impl Cast<$Dst> for $Src {
            #[inline]
            #[cfg_attr(track_caller, track_caller)]
            fn cast(self) -> $Dst {
                let (wrapped, overflow) = overflowing_cast(self);
                debug_assert!(!overflow, "{} overflows", self);
                let _ = overflow;
                wrapped
            }
        }

        impl CheckedCast<$Dst> for $Src {
            #[inline]
            fn checked_cast(self) -> Option<$Dst> {
                match overflowing_cast(self) {
                    (value, false) => Some(value),
                    (_, true) => None,
                }
            }
        }

        impl SaturatingCast<$Dst> for $Src {
            #[inline]
            fn saturating_cast(self) -> $Dst {
                match overflowing_cast(self) {
                    (value, false) => value,
                    (_, true) => {
                        if self > 0 {
                            <$Dst>::max_value()
                        } else {
                            <$Dst>::min_value()
                        }
                    }
                }
            }
        }

        impl WrappingCast<$Dst> for $Src {
            #[inline]
            fn wrapping_cast(self) -> $Dst {
                overflowing_cast(self).0
            }
        }

        impl UnwrappedCast<$Dst> for $Src {
            #[inline]
            fn unwrapped_cast(self) -> $Dst {
                match overflowing_cast(self) {
                    (value, false) => value,
                    (_, true) => panic!("overflow"),
                }
            }
        }
    };
}

macro_rules! same_signedness {
    ($($Src:ty),* => $Dst:ty) => { $(
        common! { $Src => $Dst }

        impl OverflowingCast<$Dst> for $Src {
            #[inline]
            fn overflowing_cast(self) -> ($Dst, bool) {
                let wrapped = self as $Dst;
                let overflow = self != wrapped as $Src;
                (wrapped, overflow)
            }
        }
    )* };
}

macro_rules! signed_to_unsigned {
    ($($Src:ty),* => $Dst:ty) => { $(
        common! { $Src => $Dst }

        impl OverflowingCast<$Dst> for $Src {
            #[inline]
            fn overflowing_cast(self) -> ($Dst, bool) {
                let wrapped = self as $Dst;
                let overflow = self < 0 || self != wrapped as $Src;
                (wrapped, overflow)
            }
        }
    )* };
}

macro_rules! unsigned_to_signed {
    ($($Src:ty),* => $Dst:ty) => { $(
        common! { $Src => $Dst }

        impl OverflowingCast<$Dst> for $Src {
            #[inline]
            fn overflowing_cast(self) -> ($Dst, bool) {
                let wrapped = self as $Dst;
                let overflow = wrapped < 0 || self != wrapped as $Src;
                (wrapped, overflow)
            }
        }
    )* };
}

macro_rules! wrapping_int {
    ($($Src:ty),* => $Dst:ty) => { $(
        impl Cast<Wrapping<$Dst>> for $Src {
            #[inline]
            fn cast(self) -> Wrapping<$Dst> {
                Wrapping(wrapping_cast(self))
            }
        }

        impl CheckedCast<Wrapping<$Dst>> for $Src {
            #[inline]
            fn checked_cast(self) -> Option<Wrapping<$Dst>> {
                Some(cast(self))
            }
        }

        impl UnwrappedCast<Wrapping<$Dst>> for $Src {
            #[inline]
            fn unwrapped_cast(self) -> Wrapping<$Dst> {
                cast(self)
            }
        }
    )* };
}

macro_rules! float_to_int {
    ($Src:ty, $ViaU:ty, $ViaI:ty => $($Dst:ty)*) => { $(
        impl Cast<$Dst> for $Src {
            #[inline]
            #[cfg_attr(track_caller, track_caller)]
            fn cast(self) -> $Dst {
                let (wrapped, overflow) = overflowing_cast(self);
                debug_assert!(!overflow, "{} overflows", self);
                let _ = overflow;
                wrapped
            }
        }

        impl CheckedCast<$Dst> for $Src {
            fn checked_cast(self) -> Option<$Dst> {
                let f: Float<$ViaU> = self.into();
                match f.kind {
                    FloatKind::Nan | FloatKind::Infinite | FloatKind::Overflowing(_, true) => None,
                    FloatKind::Overflowing(abs, false) => {
                        if f.neg {
                            let i = abs as $ViaI;
                            if i == <$ViaI>::min_value() {
                                checked_cast(i)
                            } else if i < 0 {
                                None
                            } else {
                                checked_cast(-i)
                            }
                        } else {
                            checked_cast(abs)
                        }
                    }
                }
            }
        }

        impl SaturatingCast<$Dst> for $Src {
            #[cfg_attr(track_caller, track_caller)]
            fn saturating_cast(self) -> $Dst {
                let f: Float<$ViaU> = self.into();
                let saturated = if f.neg {
                    <$Dst>::min_value()
                } else {
                    <$Dst>::max_value()
                };
                match f.kind {
                    FloatKind::Nan => panic!("NaN"),
                    FloatKind::Infinite | FloatKind::Overflowing(_, true) => saturated,
                    FloatKind::Overflowing(abs, false) => {
                        if f.neg {
                            let i = abs as $ViaI;
                            if i == <$ViaI>::min_value() {
                                saturating_cast(i)
                            } else if i < 0 {
                                saturated
                            } else {
                                saturating_cast(-i)
                            }
                        } else {
                            saturating_cast(abs)
                        }
                    }
                }
            }
        }

        impl WrappingCast<$Dst> for $Src {
            #[inline]
            #[cfg_attr(track_caller, track_caller)]
            fn wrapping_cast(self) -> $Dst {
                overflowing_cast(self).0
            }
        }

        impl OverflowingCast<$Dst> for $Src {
            #[cfg_attr(track_caller, track_caller)]
            fn overflowing_cast(self) -> ($Dst, bool) {
                let f: Float<$ViaU> = self.into();
                match f.kind {
                    FloatKind::Nan => panic!("NaN"),
                    FloatKind::Infinite => panic!("infinite"),
                    FloatKind::Overflowing(abs, overflow) => {
                        if f.neg {
                            let i = abs as $ViaI;
                            let (wrapped, overflow2) = if i == <$ViaI>::min_value() {
                                overflowing_cast(i)
                            } else if i < 0 {
                                (wrapping_cast::<_, $Dst>(abs).wrapping_neg(), true)
                            } else {
                                overflowing_cast(-i)
                            };
                            (wrapped, overflow | overflow2)
                        } else {
                            let (wrapped, overflow2) = overflowing_cast(abs);
                            (wrapped, overflow | overflow2)
                        }
                    }
                }
            }
        }

        impl UnwrappedCast<$Dst> for $Src {
            #[inline]
            fn unwrapped_cast(self) -> $Dst {
                match overflowing_cast(self) {
                    (val, false) => val,
                    (_, true) => panic!("overflow"),
                }
            }
        }

        impl Cast<Wrapping<$Dst>> for $Src {
            #[inline]
            #[cfg_attr(track_caller, track_caller)]
            fn cast(self) -> Wrapping<$Dst> {
                Wrapping(wrapping_cast(self))
            }
        }

        impl CheckedCast<Wrapping<$Dst>> for $Src {
            fn checked_cast(self) -> Option<Wrapping<$Dst>> {
                let f: Float<$ViaU> = self.into();
                match f.kind {
                    FloatKind::Nan | FloatKind::Infinite => None,
                    FloatKind::Overflowing(abs, _) => {
                        let wrapped = if f.neg {
                            let i = abs as $ViaI;
                            if i == <$ViaI>::min_value() {
                                wrapping_cast(i)
                            } else if i < 0 {
                                wrapping_cast::<_, $Dst>(abs).wrapping_neg()
                            } else {
                                wrapping_cast(-i)
                            }
                        } else {
                            wrapping_cast(abs)
                        };
                        Some(Wrapping(wrapped))
                    }
                }
            }
        }

        impl UnwrappedCast<Wrapping<$Dst>> for $Src {
            #[inline]
            fn unwrapped_cast(self) -> Wrapping<$Dst> {
                cast(self)
            }
        }
    )* };
}

float_to_int! { f32, u32, i32 => i8 i16 i32 }
float_to_int! { f32, u64, i64 => i64 }
float_to_int! { f32, u128, i128 => i128 }
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32"))]
float_to_int! { f32, u32, i32 => isize }
#[cfg(target_pointer_width = "64")]
float_to_int! { f32, u64, i64 => isize }
float_to_int! { f32, u32, i32 => u8 u16 u32 }
float_to_int! { f32, u64, i64 => u64 }
float_to_int! { f32, u128, i128 => u128 }
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32"))]
float_to_int! { f32, u32, i32 => usize }
#[cfg(target_pointer_width = "64")]
float_to_int! { f32, u64, i64 => usize }

float_to_int! { f64, u64, i64 => i8 i16 i32 i64 }
float_to_int! { f64, u128, i128 => i128 }
float_to_int! { f64, u64, i64 => isize }
float_to_int! { f64, u64, i64 => u8 u16 u32 u64 }
float_to_int! { f64, u128, i128 => u128 }
float_to_int! { f64, u64, i64 => usize }

float_to_int! { Round<f32>, u32, i32 => i8 i16 i32 }
float_to_int! { Round<f32>, u64, i64 => i64 }
float_to_int! { Round<f32>, u128, i128 => i128 }
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32"))]
float_to_int! { Round<f32>, u32, i32 => isize }
#[cfg(target_pointer_width = "64")]
float_to_int! { Round<f32>, u64, i64 => isize }
float_to_int! { Round<f32>, u32, i32 => u8 u16 u32 }
float_to_int! { Round<f32>, u64, i64 => u64 }
float_to_int! { Round<f32>, u128, i128 => u128 }
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32"))]
float_to_int! { Round<f32>, u32, i32 => usize }
#[cfg(target_pointer_width = "64")]
float_to_int! { Round<f32>, u64, i64 => usize }

float_to_int! { Round<f64>, u64, i64 => i8 i16 i32 i64 }
float_to_int! { Round<f64>, u128, i128 => i128 }
float_to_int! { Round<f64>, u64, i64 => isize }
float_to_int! { Round<f64>, u64, i64 => u8 u16 u32 u64 }
float_to_int! { Round<f64>, u128, i128 => u128 }
float_to_int! { Round<f64>, u64, i64 => usize }

macro_rules! signed {
    ($($Dst:ty),*) => { $(
        bool_to_int! { $Dst }
        same_signedness! { i8, i16, i32, i64, i128, isize => $Dst }
        unsigned_to_signed! { u8, u16, u32, u64, u128, usize => $Dst }
        wrapping_int! {
            bool, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize => $Dst
        }
    )* };
}

macro_rules! unsigned {
    ($($Dst:ty),*) => { $(
        bool_to_int! { $Dst }
        signed_to_unsigned! { i8, i16, i32, i64, i128, isize => $Dst }
        same_signedness! { u8, u16, u32, u64, u128, usize => $Dst }
        wrapping_int! {
            bool, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize => $Dst
        }
    )* };
}

signed! { i8, i16, i32, i64, i128, isize }
unsigned! { u8, u16, u32, u64, u128, usize }

enum FloatKind<Uns> {
    Nan,
    Infinite,
    Overflowing(Uns, bool),
}
struct Float<Uns> {
    neg: bool,
    kind: FloatKind<Uns>,
}

macro_rules! from_for_float {
    ($Src:ty, $Uns:ty, $PREC:expr => $($Dst:ty),*) => { $(
        impl From<$Src> for Float<$Dst> {
            fn from(src: $Src) -> Self {
                const SRC_NBITS: i32 = mem::size_of::<$Src>() as i32 * 8;
                const DST_NBITS: i32 = mem::size_of::<$Dst>() as i32 * 8;
                const MANT_NBITS: i32 = $PREC - 1;
                const EXP_NBITS: i32 = SRC_NBITS - MANT_NBITS - 1;
                const EXP_BIAS: i32 = (1 << (EXP_NBITS - 1)) - 1;
                const SIGN_MASK: $Uns = !(!0 >> 1);
                const MANT_MASK: $Uns = !(!0 << MANT_NBITS);
                const EXP_MASK: $Uns = !(SIGN_MASK | MANT_MASK);

                let u = src.to_bits();
                let neg = (u & SIGN_MASK) != 0;
                let biased_exp = u & EXP_MASK;
                if biased_exp == EXP_MASK {
                    let kind = if (u & MANT_MASK) == 0 {
                        FloatKind::Infinite
                    } else {
                        FloatKind::Nan
                    };
                    return Float { neg, kind };
                }
                let shift = (biased_exp >> MANT_NBITS) as i32 - (EXP_BIAS + MANT_NBITS);

                // Check if the magnitude is smaller than one. Do not return
                // early if shift == -MANT_NBITS, as there is implicit one.
                if shift < -MANT_NBITS {
                    let kind = FloatKind::Overflowing(0, false);
                    return Float { neg, kind };
                }

                // Check if the least significant bit will be in a $Dst.
                if shift >= DST_NBITS {
                    let kind = FloatKind::Overflowing(0, true);
                    return Float { neg, kind };
                }

                let mut significand: $Dst = (u & MANT_MASK).into();
                // Add implicit one.
                significand |= 1 << MANT_NBITS;
                let kind = if shift < 0 {
                    FloatKind::Overflowing(significand >> -shift, false)
                } else {
                    let wrapped = significand << shift;
                    let overflow = (wrapped >> shift) != significand;
                    FloatKind::Overflowing(wrapped, overflow)
                };
                Float { neg, kind }
            }
        }

        impl From<Round<$Src>> for Float<$Dst> {
            fn from(src: Round<$Src>) -> Self {
                const SRC_NBITS: i32 = mem::size_of::<$Src>() as i32 * 8;
                const DST_NBITS: i32 = mem::size_of::<$Dst>() as i32 * 8;
                const MANT_NBITS: i32 = $PREC - 1;
                const EXP_NBITS: i32 = SRC_NBITS - MANT_NBITS - 1;
                const EXP_BIAS: i32 = (1 << (EXP_NBITS - 1)) - 1;
                const SIGN_MASK: $Uns = !(!0 >> 1);
                const MANT_MASK: $Uns = !(!0 << MANT_NBITS);
                const EXP_MASK: $Uns = !(SIGN_MASK | MANT_MASK);

                let src = src.0;
                let u = src.to_bits();
                let neg = (u & SIGN_MASK) != 0;
                let biased_exp = u & EXP_MASK;
                if biased_exp == EXP_MASK {
                    let kind = if (u & MANT_MASK) == 0 {
                        FloatKind::Infinite
                    } else {
                        FloatKind::Nan
                    };
                    return Float { neg, kind };
                }
                let shift = (biased_exp >> MANT_NBITS) as i32 - (EXP_BIAS + MANT_NBITS);

                // If shift = -MANT_BITS, then 1 ≤ x < 2.
                // If shift = -MANT_BITS - 1, then 0.5 ≤ x < 1, which can be rounded up.
                // If shift < -MANT_BITS - 1, then x < 0.5, which is rounded down.
                ////                    || (shift == -MANT_NBITS - 1 && ((u & MANT_MASK) != 0 || x))
                if shift < -MANT_NBITS - 1 {
                    let kind = FloatKind::Overflowing(0, false);
                    return Float { neg, kind };
                }

                // Check if the least significant bit will be in a $Dst.
                if shift >= DST_NBITS {
                    let kind = FloatKind::Overflowing(0, true);
                    return Float { neg, kind };
                }

                let mut significand: $Dst = (u & MANT_MASK).into();
                // Add implicit one.
                significand |= 1 << MANT_NBITS;
                let kind = if shift < 0 {
                    let right = -shift;
                    let round_bit = 1 << (right - 1);
                    if (significand & round_bit) != 0 && (significand & (3 * round_bit - 1)) != 0 {
                        significand += round_bit;
                    }
                    FloatKind::Overflowing(significand >> right, false)
                } else {
                    let wrapped = significand << shift;
                    let overflow = (wrapped >> shift) != significand;
                    FloatKind::Overflowing(wrapped, overflow)
                };
                Float { neg, kind }
            }
        }
    )* };
}

from_for_float! { f32, u32, 24 => u32, u64, u128 }
from_for_float! { f64, u64, 53 => u64, u128 }
