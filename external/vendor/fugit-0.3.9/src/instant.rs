use crate::duration::Duration;
use crate::helpers::{self, Helpers};
use core::cmp::Ordering;
use core::ops;

/// Represents an instant in time.
///
/// The generic `T` can either be `u32` or `u64`, and the const generics represent the ratio of the
/// ticks contained within the instant: `instant in seconds = NOM / DENOM * ticks`
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[cfg_attr(
    feature = "postcard_max_size",
    derive(postcard::experimental::max_size::MaxSize)
)]
#[derive(Clone, Copy, Debug)]
pub struct Instant<T, const NOM: u32, const DENOM: u32> {
    ticks: T,
}

macro_rules! impl_instant_for_integer {
    ($i:ty) => {
        impl<const NOM: u32, const DENOM: u32> Instant<$i, NOM, DENOM> {
            /// Create an `Instant` from a ticks value.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let _i = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            /// ```
            #[inline]
            pub const fn from_ticks(ticks: $i) -> Self {
                helpers::greater_than_0::<NOM>();
                helpers::greater_than_0::<DENOM>();

                Instant { ticks }
            }

            /// Extract the ticks from an `Instant`.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(234);")]
            ///
            /// assert_eq!(i.ticks(), 234);
            /// ```
            #[inline]
            pub const fn ticks(&self) -> $i {
                self.ticks
            }

            /// Const comparison of `Instant`s.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i1 = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            #[doc = concat!("let i2 = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(2);")]
            ///
            /// assert_eq!(i1.const_cmp(i2), core::cmp::Ordering::Less);
            /// ```
            ///
            /// This function takes into account that ticks might wrap around. If the absolute
            /// values of `self` and `other` differ by more than half the possible range, it is
            /// assumed that an overflow occured and the result is reversed:
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i1 = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(", stringify!($i),"::MAX);")]
            #[doc = concat!("let i2 = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            ///
            /// assert_eq!(i1.const_cmp(i2), core::cmp::Ordering::Less);
            /// ```
            #[inline]
            pub const fn const_cmp(self, other: Self) -> Ordering {
                if self.ticks == other.ticks {
                    Ordering::Equal
                } else {
                    let v = self.ticks.wrapping_sub(other.ticks);

                    // not using `v.cmp(<$i>::MAX / 2).reverse()` due to `cmp` being non-const
                    if v > <$i>::MAX / 2 {
                        Ordering::Less
                    } else if v < <$i>::MAX / 2 {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }
                }
            }

            /// Duration between since the start of the `Instant`. This assumes an instant which
            /// won't wrap within the execution of the program.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(11);")]
            ///
            /// assert_eq!(i.duration_since_epoch().ticks(), 11);
            /// ```
            #[inline]
            pub const fn duration_since_epoch(self) -> Duration<$i, NOM, DENOM> {
                Duration::<$i, NOM, DENOM>::from_ticks(self.ticks())
            }

            /// Duration between `Instant`s.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i1 = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            #[doc = concat!("let i2 = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(2);")]
            ///
            /// assert_eq!(i1.checked_duration_since(i2), None);
            /// assert_eq!(i2.checked_duration_since(i1).unwrap().ticks(), 1);
            /// ```
            #[inline]
            pub const fn checked_duration_since(
                self,
                other: Self,
            ) -> Option<Duration<$i, NOM, DENOM>> {
                match self.const_cmp(other) {
                    Ordering::Greater | Ordering::Equal => {
                        Some(Duration::<$i, NOM, DENOM>::from_ticks(
                            self.ticks.wrapping_sub(other.ticks),
                        ))
                    }
                    Ordering::Less => None,
                }
            }

            /// Subtract a `Duration` from an `Instant` while checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            #[doc = concat!("let d = Duration::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            ///
            /// assert_eq!(i.checked_sub_duration(d).unwrap().ticks(), 0);
            /// ```
            pub const fn checked_sub_duration<const O_NOM: u32, const O_DENOM: u32>(
                self,
                other: Duration<$i, O_NOM, O_DENOM>,
            ) -> Option<Self> {
                if Helpers::<NOM, DENOM, O_NOM, O_DENOM>::SAME_BASE {
                    Some(Instant::<$i, NOM, DENOM>::from_ticks(
                        self.ticks.wrapping_sub(other.ticks()),
                    ))
                } else {
                    if let Some(lh) = other
                        .ticks()
                        .checked_mul(Helpers::<NOM, DENOM, O_NOM, O_DENOM>::LD_TIMES_RN as $i)
                    {
                        let ticks = lh / Helpers::<NOM, DENOM, O_NOM, O_DENOM>::RD_TIMES_LN as $i;

                        Some(Instant::<$i, NOM, DENOM>::from_ticks(
                            self.ticks.wrapping_sub(ticks),
                        ))
                    } else {
                        None
                    }
                }
            }

            /// Add a `Duration` to an `Instant` while checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let i = Instant::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            #[doc = concat!("let d = Duration::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            ///
            /// assert_eq!(i.checked_add_duration(d).unwrap().ticks(), 2);
            /// ```
            pub const fn checked_add_duration<const O_NOM: u32, const O_DENOM: u32>(
                self,
                other: Duration<$i, O_NOM, O_DENOM>,
            ) -> Option<Self> {
                if Helpers::<NOM, DENOM, O_NOM, O_DENOM>::SAME_BASE {
                    Some(Instant::<$i, NOM, DENOM>::from_ticks(
                        self.ticks.wrapping_add(other.ticks()),
                    ))
                } else {
                    if let Some(lh) = other
                        .ticks()
                        .checked_mul(Helpers::<NOM, DENOM, O_NOM, O_DENOM>::LD_TIMES_RN as $i)
                    {
                        let ticks = lh / Helpers::<NOM, DENOM, O_NOM, O_DENOM>::RD_TIMES_LN as $i;

                        Some(Instant::<$i, NOM, DENOM>::from_ticks(
                            self.ticks.wrapping_add(ticks),
                        ))
                    } else {
                        None
                    }
                }
            }
        }

        impl<const NOM: u32, const DENOM: u32> PartialOrd for Instant<$i, NOM, DENOM> {
            /// This implementation deviates from the definition of
            /// [PartialOrd::partial_cmp](core::cmp::PartialOrd::partial_cmp):
            ///
            /// It takes into account that ticks might wrap around. If the absolute
            /// values of `self` and `other` differ by more than half the possible range, it is
            /// assumed that an overflow occured and the result is reversed.
            ///
            /// That breaks the transitivity invariant: a < b and b < c no longer implies a < c.
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.const_cmp(*other))
            }
        }

        impl<const NOM: u32, const DENOM: u32> Ord for Instant<$i, NOM, DENOM> {
            /// This implementation deviates from the definition of
            /// [Ord::cmp](core::cmp::Ord::cmp):
            ///
            /// It takes into account that ticks might wrap around. If the absolute
            /// values of `self` and `other` differ by more than half the possible range, it is
            /// assumed that an overflow occured and the result is reversed.
            ///
            /// That breaks the transitivity invariant: a < b and b < c no longer implies a < c.
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                self.const_cmp(*other)
            }
        }

        impl<const NOM: u32, const DENOM: u32> PartialEq for Instant<$i, NOM, DENOM> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                self.ticks.eq(&other.ticks)
            }
        }

        impl<const NOM: u32, const DENOM: u32> Eq for Instant<$i, NOM, DENOM> {}

        // Instant - Instant = Duration
        // We have limited this to use same numerator and denominator in both left and right hand sides,
        // this allows for the extension traits to work. For usage with different fraction, use
        // `checked_duration_since`.
        impl<const NOM: u32, const DENOM: u32> ops::Sub<Instant<$i, NOM, DENOM>>
            for Instant<$i, NOM, DENOM>
        {
            type Output = Duration<$i, NOM, DENOM>;

            #[inline]
            fn sub(self, other: Self) -> Self::Output {
                if let Some(v) = self.checked_duration_since(other) {
                    v
                } else {
                    panic!("Sub failed! Other > self");
                }
            }
        }

        // Instant - Duration = Instant
        // We have limited this to use same numerator and denominator in both left and right hand sides,
        // this allows for the extension traits to work. For usage with different fraction, use
        // `checked_sub_duration`.
        impl<const NOM: u32, const DENOM: u32> ops::Sub<Duration<$i, NOM, DENOM>>
            for Instant<$i, NOM, DENOM>
        {
            type Output = Instant<$i, NOM, DENOM>;

            #[inline]
            fn sub(self, other: Duration<$i, NOM, DENOM>) -> Self::Output {
                if let Some(v) = self.checked_sub_duration(other) {
                    v
                } else {
                    panic!("Sub failed! Overflow");
                }
            }
        }

        // Instant -= Duration
        // We have limited this to use same numerator and denominator in both left and right hand sides,
        // this allows for the extension traits to work. For usage with different fraction, use
        // `checked_sub_duration`.
        impl<const NOM: u32, const DENOM: u32> ops::SubAssign<Duration<$i, NOM, DENOM>>
            for Instant<$i, NOM, DENOM>
        {
            #[inline]
            fn sub_assign(&mut self, other: Duration<$i, NOM, DENOM>) {
                *self = *self - other;
            }
        }

        // Instant + Duration = Instant
        // We have limited this to use same numerator and denominator in both left and right hand sides,
        // this allows for the extension traits to work. For usage with different fraction, use
        // `checked_add_duration`.
        impl<const NOM: u32, const DENOM: u32> ops::Add<Duration<$i, NOM, DENOM>>
            for Instant<$i, NOM, DENOM>
        {
            type Output = Instant<$i, NOM, DENOM>;

            #[inline]
            fn add(self, other: Duration<$i, NOM, DENOM>) -> Self::Output {
                if let Some(v) = self.checked_add_duration(other) {
                    v
                } else {
                    panic!("Add failed! Overflow");
                }
            }
        }

        // Instant += Duration
        // We have limited this to use same numerator and denominator in both left and right hand sides,
        // this allows for the extension traits to work. For usage with different fraction, use
        // `checked_add_duration`.
        impl<const NOM: u32, const DENOM: u32> ops::AddAssign<Duration<$i, NOM, DENOM>>
            for Instant<$i, NOM, DENOM>
        {
            #[inline]
            fn add_assign(&mut self, other: Duration<$i, NOM, DENOM>) {
                *self = *self + other;
            }
        }

        #[cfg(feature = "defmt")]
        impl<const NOM: u32, const DENOM: u32> defmt::Format for Instant<$i, NOM, DENOM> {
            fn format(&self, f: defmt::Formatter) {
                if NOM == 3_600 && DENOM == 1 {
                    defmt::write!(f, "{} h", self.ticks)
                } else if NOM == 60 && DENOM == 1 {
                    defmt::write!(f, "{} min", self.ticks)
                } else if NOM == 1 && DENOM == 1 {
                    defmt::write!(f, "{} s", self.ticks)
                } else if NOM == 1 && DENOM == 1_000 {
                    defmt::write!(f, "{} ms", self.ticks)
                } else if NOM == 1 && DENOM == 1_000_000 {
                    defmt::write!(f, "{} us", self.ticks)
                } else if NOM == 1 && DENOM == 1_000_000_000 {
                    defmt::write!(f, "{} ns", self.ticks)
                } else {
                    defmt::write!(f, "{} ticks @ ({}/{})", self.ticks, NOM, DENOM)
                }
            }
        }

        impl<const NOM: u32, const DENOM: u32> core::fmt::Display for Instant<$i, NOM, DENOM> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                if NOM == 3_600 && DENOM == 1 {
                    write!(f, "{} h", self.ticks)
                } else if NOM == 60 && DENOM == 1 {
                    write!(f, "{} min", self.ticks)
                } else if NOM == 1 && DENOM == 1 {
                    write!(f, "{} s", self.ticks)
                } else if NOM == 1 && DENOM == 1_000 {
                    write!(f, "{} ms", self.ticks)
                } else if NOM == 1 && DENOM == 1_000_000 {
                    write!(f, "{} us", self.ticks)
                } else if NOM == 1 && DENOM == 1_000_000_000 {
                    write!(f, "{} ns", self.ticks)
                } else {
                    write!(f, "{} ticks @ ({}/{})", self.ticks, NOM, DENOM)
                }
            }
        }
    };
}

impl_instant_for_integer!(u32);
impl_instant_for_integer!(u64);

//
// Operations between u32 Duration and u64 Instant
//

// Instant - Duration = Instant
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_sub_duration`.
impl<const NOM: u32, const DENOM: u32> ops::Sub<Duration<u32, NOM, DENOM>>
    for Instant<u64, NOM, DENOM>
{
    type Output = Instant<u64, NOM, DENOM>;

    #[inline]
    fn sub(self, other: Duration<u32, NOM, DENOM>) -> Self::Output {
        if let Some(v) = self.checked_sub_duration(other.into()) {
            v
        } else {
            panic!("Sub failed! Overflow");
        }
    }
}

// Instant -= Duration
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_sub_duration`.
impl<const NOM: u32, const DENOM: u32> ops::SubAssign<Duration<u32, NOM, DENOM>>
    for Instant<u64, NOM, DENOM>
{
    #[inline]
    fn sub_assign(&mut self, other: Duration<u32, NOM, DENOM>) {
        *self = *self - other;
    }
}

// Instant + Duration = Instant
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_add_duration`.
impl<const NOM: u32, const DENOM: u32> ops::Add<Duration<u32, NOM, DENOM>>
    for Instant<u64, NOM, DENOM>
{
    type Output = Instant<u64, NOM, DENOM>;

    #[inline]
    fn add(self, other: Duration<u32, NOM, DENOM>) -> Self::Output {
        if let Some(v) = self.checked_add_duration(other.into()) {
            v
        } else {
            panic!("Add failed! Overflow");
        }
    }
}

// Instant += Duration
// We have limited this to use same numerator and denominator in both left and right hand sides,
// this allows for the extension traits to work. For usage with different fraction, use
// `checked_add_duration`.
impl<const NOM: u32, const DENOM: u32> ops::AddAssign<Duration<u32, NOM, DENOM>>
    for Instant<u64, NOM, DENOM>
{
    #[inline]
    fn add_assign(&mut self, other: Duration<u32, NOM, DENOM>) {
        *self = *self + other;
    }
}

// impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
//     ops::Add<Duration<u32, R_NOM, R_DENOM>> for Duration<u64, L_NOM, L_DENOM>
// {
//     type Output = Duration<u64, L_NOM, L_DENOM>;
//
//     #[inline]
//     fn add(self, other: Duration<u32, R_NOM, R_DENOM>) -> Self::Output {
//         self.add(Duration::<u64, L_NOM, L_DENOM>::from_ticks(
//             other.ticks() as u64
//         ))
//     }
// }
