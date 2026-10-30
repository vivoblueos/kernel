use crate::helpers::{self, Helpers};
use crate::Duration;
use core::cmp::Ordering;
use core::convert;
use core::ops;

/// Represents a frequency.
///
/// The generic `T` can either be `u32` or `u64`, and the const generics represent the ratio of the
/// raw contained within the rate: `rate in Hz = NOM / DENOM * raw`
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[cfg_attr(
    feature = "postcard_max_size",
    derive(postcard::experimental::max_size::MaxSize)
)]
#[derive(Clone, Copy, Debug)]
pub struct Rate<T, const NOM: u32, const DENOM: u32> {
    pub(crate) raw: T,
}

macro_rules! impl_rate_for_integer {
    ($i:ty) => {
        impl<const NOM: u32, const DENOM: u32> Rate<$i, NOM, DENOM> {
            /// Create a `Rate` from a raw value.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let _d = Rate::<", stringify!($i), ", 1, 1_000>::from_raw(1);")]
            /// ```
            #[inline]
            pub const fn from_raw(raw: $i) -> Self {
                helpers::greater_than_0::<NOM>();
                helpers::greater_than_0::<DENOM>();

                Rate { raw }
            }

            /// Extract the raw value from a `Rate`.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let d = Rate::<", stringify!($i), ", 1, 1_000>::from_raw(234);")]
            ///
            /// assert_eq!(d.raw(), 234);
            /// ```
            #[inline]
            pub const fn raw(&self) -> $i {
                self.raw
            }

            /// Add two rates while checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let r1 = Rate::<", stringify!($i), ", 1, 1_000>::from_raw(1);")]
            #[doc = concat!("let r2 = Rate::<", stringify!($i), ", 1, 1_000>::from_raw(2);")]
            #[doc = concat!("let r3 = Rate::<", stringify!($i), ", 1, 1_000>::from_raw(", stringify!($i), "::MAX);")]
            ///
            /// assert_eq!(r1.checked_add(r2).unwrap().raw(), 3);
            /// assert_eq!(r1.checked_add(r3), None);
            /// ```
            pub const fn checked_add<const O_NOM: u32, const O_DENOM: u32>(
                self,
                other: Rate<$i, O_NOM, O_DENOM>,
            ) -> Option<Self> {
                if Helpers::<NOM, DENOM, O_NOM, O_DENOM>::SAME_BASE {
                    if let Some(raw) = self.raw.checked_add(other.raw) {
                        Some(Rate::<$i, NOM, DENOM>::from_raw(raw))
                    } else {
                        None
                    }
                } else {
                    if let Some(lh) = other
                        .raw
                        .checked_mul(Helpers::<NOM, DENOM, O_NOM, O_DENOM>::LD_TIMES_RN as $i)
                    {
                        let raw = lh / Helpers::<NOM, DENOM, O_NOM, O_DENOM>::RD_TIMES_LN as $i;

                        if let Some(raw) = self.raw.checked_add(raw) {
                            Some(Rate::<$i, NOM, DENOM>::from_raw(raw))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
            }

            /// Subtract two rates while checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let r1 = Rate::<", stringify!($i), ", 1, 1_000>::from_raw(1);")]
            #[doc = concat!("let r2 = Rate::<", stringify!($i), ", 1, 1_000>::from_raw(2);")]
            #[doc = concat!("let r3 = Rate::<", stringify!($i), ", 1, 1_000>::from_raw(", stringify!($i), "::MAX);")]
            ///
            /// assert_eq!(r2.checked_sub(r1).unwrap().raw(), 1);
            /// assert_eq!(r1.checked_sub(r3), None);
            /// ```
            pub const fn checked_sub<const O_NOM: u32, const O_DENOM: u32>(
                self,
                other: Rate<$i, O_NOM, O_DENOM>,
            ) -> Option<Self> {
                if Helpers::<NOM, DENOM, O_NOM, O_DENOM>::SAME_BASE {
                    if let Some(raw) = self.raw.checked_sub(other.raw) {
                        Some(Rate::<$i, NOM, DENOM>::from_raw(raw))
                    } else {
                        None
                    }
                } else {
                    if let Some(lh) = other
                        .raw
                        .checked_mul(Helpers::<NOM, DENOM, O_NOM, O_DENOM>::LD_TIMES_RN as $i)
                    {
                        let raw = lh / Helpers::<NOM, DENOM, O_NOM, O_DENOM>::RD_TIMES_LN as $i;

                        if let Some(raw) = self.raw.checked_sub(raw) {
                            Some(Rate::<$i, NOM, DENOM>::from_raw(raw))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
            }

            #[doc = concat!("Const `cmp` for ", stringify!($i))]
            #[inline(always)]
            const fn _const_cmp(a: $i, b: $i) -> Ordering {
                if a < b {
                    Ordering::Less
                } else if a > b {
                    Ordering::Greater
                } else {
                    Ordering::Equal
                }
            }

            /// Const partial comparison.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let r1 = Rate::<", stringify!($i), ", 1, 1_00>::from_raw(1);")]
            #[doc = concat!("let r2 = Rate::<", stringify!($i), ", 1, 1_000>::from_raw(1);")]
            ///
            /// assert_eq!(r1.const_partial_cmp(r2), Some(core::cmp::Ordering::Greater));
            /// ```
            #[inline]
            pub const fn const_partial_cmp<const R_NOM: u32, const R_DENOM: u32>(
                self,
                other: Rate<$i, R_NOM, R_DENOM>
            ) -> Option<Ordering> {
                if Helpers::<NOM, DENOM, R_NOM, R_DENOM>::SAME_BASE {
                    // If we are in the same base, comparison in trivial
                    Some(Self::_const_cmp(self.raw, other.raw))
                } else {
                    let lh = self
                        .raw
                        .checked_mul(Helpers::<NOM, DENOM, R_NOM, R_DENOM>::RD_TIMES_LN as $i);
                    let rh = other
                        .raw
                        .checked_mul(Helpers::<NOM, DENOM, R_NOM, R_DENOM>::LD_TIMES_RN as $i);

                    if let (Some(lh), Some(rh)) = (lh, rh) {
                        Some(Self::_const_cmp(lh, rh))
                    } else {
                        None
                    }
                }
            }

            /// Const equality check.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let r1 = Rate::<", stringify!($i), ", 1, 1_00>::from_raw(1);")]
            #[doc = concat!("let r2 = Rate::<", stringify!($i), ", 1, 1_000>::from_raw(10);")]
            ///
            /// assert!(r1.const_eq(r2));
            /// ```
            #[inline]
            pub const fn const_eq<const R_NOM: u32, const R_DENOM: u32>(
                self,
                other: Rate<$i, R_NOM, R_DENOM>
            ) -> bool {
                if Helpers::<NOM, DENOM, R_NOM, R_DENOM>::SAME_BASE {
                    // If we are in the same base, comparison in trivial
                    self.raw == other.raw
                } else {
                    let lh = self
                        .raw
                        .checked_mul(Helpers::<NOM, DENOM, R_NOM, R_DENOM>::RD_TIMES_LN as $i);
                    let rh = other
                        .raw
                        .checked_mul(Helpers::<NOM, DENOM, R_NOM, R_DENOM>::LD_TIMES_RN as $i);

                    if let (Some(lh), Some(rh)) = (lh, rh) {
                        lh == rh
                    } else {
                        false
                    }
                }
            }

            /// Const try from, checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let r1 = Rate::<", stringify!($i), ", 1, 1_00>::from_raw(1);")]
            #[doc = concat!("let r2 = Rate::<", stringify!($i), ", 1, 1_000>::const_try_from(r1);")]
            ///
            /// assert_eq!(r2.unwrap().raw(), 10);
            /// ```
            pub const fn const_try_from<const I_NOM: u32, const I_DENOM: u32>(
                rate: Rate<$i, I_NOM, I_DENOM>,
            ) -> Option<Self> {
                if Helpers::<I_NOM, I_DENOM, NOM, DENOM>::SAME_BASE {
                    Some(Self::from_raw(rate.raw))
                } else {
                    if let Some(lh) = (rate.raw as u64)
                        .checked_mul(Helpers::<I_NOM, I_DENOM, NOM, DENOM>::RD_TIMES_LN)
                    {
                        let raw = lh / Helpers::<I_NOM, I_DENOM, NOM, DENOM>::LD_TIMES_RN;

                        if raw <= <$i>::MAX as u64 {
                            Some(Self::from_raw(raw as $i))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
            }

            /// Const try into, checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let r1 = Rate::<", stringify!($i), ", 1, 1_00>::from_raw(1);")]
            #[doc = concat!("let r2: Option<Rate::<", stringify!($i), ", 1, 1_000>> = r1.const_try_into();")]
            ///
            /// assert_eq!(r2.unwrap().raw(), 10);
            /// ```
            #[inline]
            pub const fn const_try_into<const O_NOM: u32, const O_DENOM: u32>(
                self,
            ) -> Option<Rate<$i, O_NOM, O_DENOM>> {
                Rate::<$i, O_NOM, O_DENOM>::const_try_from(self)
            }

            /// Const try into duration, checking for divide-by-zero.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let r1 = Rate::<", stringify!($i), ", 1, 1>::from_raw(1);")]
            #[doc = concat!("let d1: Option<Duration::<", stringify!($i), ", 1, 1_000>> = r1.try_into_duration();")]
            ///
            /// assert_eq!(d1.unwrap().ticks(), 1_000);
            /// ```
            pub const fn try_into_duration<const O_NOM: u32, const O_DENOM: u32>(
                self,
            ) -> Option<Duration<$i, O_NOM, O_DENOM>> {
                Duration::<$i, O_NOM, O_DENOM>::try_from_rate(self)
            }

            /// Convert from rate to duration.
            pub const fn into_duration<const O_NOM: u32, const O_DENOM: u32>(
                self,
            ) -> Duration<$i, O_NOM, O_DENOM> {
                if let Some(v) = self.try_into_duration() {
                    v
                } else {
                    panic!("Into duration failed, divide-by-zero!");
                }
            }

            /// Const try from duration, checking for divide-by-zero.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let d1 = Duration::<", stringify!($i), ", 1, 1_000>::from_ticks(2);")]
            #[doc = concat!("let r1 = Rate::<", stringify!($i), ", 1, 1>::try_from_duration(d1);")]
            ///
            /// assert_eq!(r1.unwrap().raw(), 500);
            /// ```
            #[inline]
            pub const fn try_from_duration<const I_NOM: u32, const I_DENOM: u32>(
                duration: Duration<$i, I_NOM, I_DENOM>,
            ) -> Option<Self> {
                if duration.ticks > 0 {
                    Some(Self::from_raw(
                        Helpers::<I_NOM, I_DENOM, NOM, DENOM>::RATE_TO_DURATION_NUMERATOR as $i
                        / duration.ticks
                    ))
                } else {
                    None
                }
            }

            /// Convert from duration to rate.
            #[inline]
            pub const fn from_duration<const I_NOM: u32, const I_DENOM: u32>(
                duration: Duration<$i, I_NOM, I_DENOM>,
            ) -> Self {
                if let Some(v) = Self::try_from_duration(duration) {
                    v
                } else {
                    panic!("From duration failed, divide-by-zero!");
                }
            }

            /// Convert between bases for a rate.
            ///
            /// Unfortunately not a `From` impl due to collision with the std lib.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let r1 = Rate::<", stringify!($i), ", 1, 100>::from_raw(1);")]
            #[doc = concat!("let r2: Rate::<", stringify!($i), ", 1, 1_000> = r1.convert();")]
            ///
            /// assert_eq!(r2.raw(), 10);
            /// ```
            ///
            /// Can be used in const contexts. Compilation will fail if the conversion causes overflow
            ///
            /// ```compile_fail
            /// # use fugit::*;
            #[doc = concat!("const RAW: ", stringify!($i), "= ", stringify!($i), "::MAX - 10;")]
            #[doc = concat!("const R1: Rate::<", stringify!($i), ", 1, 100> = Rate::<", stringify!($i), ", 1, 100>::from_raw(RAW);")]
            /// // Fails conversion due to overflow
            #[doc = concat!("const R2: Rate::<", stringify!($i), ", 1, 200> = R1.convert();")]
            /// ```
            pub const fn convert<const O_NOM: u32, const O_DENOM: u32>(
                self,
            ) -> Rate<$i, O_NOM, O_DENOM> {
                if let Some(v) = self.const_try_into() {
                    v
                } else {
                    panic!("Convert failed!");
                }
            }

            /// Convert the Rate to an interger number of Hz.
            #[inline]
            #[allow(non_snake_case)]
            pub const fn to_Hz(&self) -> $i {
                    (Helpers::<1, 1, NOM, DENOM>::LD_TIMES_RN as $i * self.raw)
                        / Helpers::<1, 1, NOM, DENOM>::RD_TIMES_LN as $i
            }

            /// Convert the Rate to an interger number of kHz.
            #[inline]
            #[allow(non_snake_case)]
            pub const fn to_kHz(&self) -> $i {
                    (Helpers::<1_000, 1, NOM, DENOM>::LD_TIMES_RN as $i * self.raw)
                        / Helpers::<1_000, 1, NOM, DENOM>::RD_TIMES_LN as $i
            }

            /// Convert the Rate to an interger number of MHz.
            #[inline]
            #[allow(non_snake_case)]
            pub const fn to_MHz(&self) -> $i {
                    (Helpers::<1_000_000, 1, NOM, DENOM>::LD_TIMES_RN as $i * self.raw)
                        / Helpers::<1_000_000, 1, NOM, DENOM>::RD_TIMES_LN as $i
            }

            /// Shorthand for creating a rate which represents hertz.
            #[inline]
            #[allow(non_snake_case)]
            pub const fn Hz(val: $i) -> Self {
                Self::from_raw(
                    (Helpers::<1, 1, NOM, DENOM>::RD_TIMES_LN as $i * val)
                        / Helpers::<1, 1, NOM, DENOM>::LD_TIMES_RN as $i,
                )
            }

            /// Shorthand for creating a rate which represents kilohertz.
            #[inline]
            #[allow(non_snake_case)]
            pub const fn kHz(val: $i) -> Self {
                Self::from_raw(
                    (Helpers::<1_000, 1, NOM, DENOM>::RD_TIMES_LN as $i * val)
                        / Helpers::<1_000, 1, NOM, DENOM>::LD_TIMES_RN as $i,
                )
            }

            /// Shorthand for creating a rate which represents megahertz.
            #[inline]
            #[allow(non_snake_case)]
            pub const fn MHz(val: $i) -> Self {
                Self::from_raw(
                    (Helpers::<1_000_000, 1, NOM, DENOM>::RD_TIMES_LN as $i * val)
                        / Helpers::<1_000_000, 1, NOM, DENOM>::LD_TIMES_RN as $i,
                )
            }

            /// Shorthand for creating a rate which represents nanoseconds.
            #[inline]
            pub const fn nanos(val: $i) -> Self {
                Self::from_duration(crate::Duration::<$i, 1, 1_000_000_000>::from_ticks(val))
            }

            /// Shorthand for creating a rate which represents microseconds.
            #[inline]
            pub const fn micros(val: $i) -> Self {
                Self::from_duration(crate::Duration::<$i, 1, 1_000_000>::from_ticks(val))
            }

            /// Shorthand for creating a rate which represents milliseconds.
            #[inline]
            pub const fn millis(val: $i) -> Self {
                Self::from_duration(crate::Duration::<$i, 1, 1_000>::from_ticks(val))
            }
        }

        impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
            PartialOrd<Rate<$i, R_NOM, R_DENOM>> for Rate<$i, L_NOM, L_DENOM>
        {
            #[inline]
            fn partial_cmp(&self, other: &Rate<$i, R_NOM, R_DENOM>) -> Option<Ordering> {
                self.const_partial_cmp(*other)
            }
        }

        impl<const NOM: u32, const DENOM: u32> Ord for Rate<$i, NOM, DENOM> {
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                Self::_const_cmp(self.raw, other.raw)
            }
        }

        impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
            PartialEq<Rate<$i, R_NOM, R_DENOM>> for Rate<$i, L_NOM, L_DENOM>
        {
            #[inline]
            fn eq(&self, other: &Rate<$i, R_NOM, R_DENOM>) -> bool {
                self.const_eq(*other)
            }
        }

        impl<const NOM: u32, const DENOM: u32> Eq for Rate<$i, NOM, DENOM> {}

        // Rate - Rate = Rate (only same base until const_generics_defaults is
        // stabilized)
        impl<const NOM: u32, const DENOM: u32> ops::Sub<Rate<$i, NOM, DENOM>>
            for Rate<$i, NOM, DENOM>
        {
            type Output = Rate<$i, NOM, DENOM>;

            #[inline]
            fn sub(self, other: Rate<$i, NOM, DENOM>) -> Self::Output {
                if let Some(v) = self.checked_sub(other) {
                    v
                } else {
                    panic!("Sub failed!");
                }
            }
        }

        // Rate + Rate = Rate (only same base until const_generics_defaults is
        // stabilized)
        impl<const NOM: u32, const DENOM: u32> ops::Add<Rate<$i, NOM, DENOM>>
            for Rate<$i, NOM, DENOM>
        {
            type Output = Rate<$i, NOM, DENOM>;

            #[inline]
            fn add(self, other: Rate<$i, NOM, DENOM>) -> Self::Output {
                if let Some(v) = self.checked_add(other) {
                    v
                } else {
                    panic!("Add failed!");
                }
            }
        }

        // Rate += Rate
        impl<const NOM: u32, const DENOM: u32> ops::AddAssign<Rate<$i, NOM, DENOM>>
            for Rate<$i, NOM, DENOM>
        {
            #[inline]
            fn add_assign(&mut self, other: Self) {
                *self = *self + other;
            }
        }

        // integer * Rate = Rate
        impl<const NOM: u32, const DENOM: u32> ops::Mul<Rate<$i, NOM, DENOM>> for u32 {
            type Output = Rate<$i, NOM, DENOM>;

            #[inline]
            fn mul(self, mut other: Rate<$i, NOM, DENOM>) -> Self::Output {
                other.raw *= self as $i;
                other
            }
        }

        // Rate * integer = Rate
        impl<const NOM: u32, const DENOM: u32> ops::Mul<u32> for Rate<$i, NOM, DENOM> {
            type Output = Rate<$i, NOM, DENOM>;

            #[inline]
            fn mul(mut self, other: u32) -> Self::Output {
                self.raw *= other as $i;
                self
            }
        }

        // Rate *= integer
        impl<const NOM: u32, const DENOM: u32> ops::MulAssign<u32>
            for Rate<$i, NOM, DENOM>
        {
            #[inline]
            fn mul_assign(&mut self, other: u32) {
                *self = *self * other;
            }
        }

        // Rate / integer = Rate
        impl<const NOM: u32, const DENOM: u32> ops::Div<u32> for Rate<$i, NOM, DENOM> {
            type Output = Rate<$i, NOM, DENOM>;

            #[inline]
            fn div(mut self, other: u32) -> Self::Output {
                self.raw /= other as $i;
                self
            }
        }

        // Rate / Rate = integer
        impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32> ops::Div<Rate<$i, R_NOM, R_DENOM>>
            for Rate<$i, L_NOM, L_DENOM>
        {
            type Output = $i;

            #[inline]
            fn div(self, other: Rate<$i, R_NOM, R_DENOM>) -> Self::Output {
                let conv: Rate<$i, R_NOM, R_DENOM> = self.convert();
                conv.raw / other.raw
            }
        }

        // Rate /= integer
        impl<const NOM: u32, const DENOM: u32> ops::DivAssign<u32>
            for Rate<$i, NOM, DENOM>
        {
            #[inline]
            fn div_assign(&mut self, other: u32) {
                *self = *self / other;
            }
        }

        #[cfg(feature = "defmt")]
        impl<const NOM: u32, const DENOM: u32> defmt::Format for Rate<$i, NOM, DENOM>
        {
            fn format(&self, f: defmt::Formatter) {
                if NOM == 1 && DENOM == 1 {
                    defmt::write!(f, "{} Hz", self.raw)
                } else if NOM == 1_000 && DENOM == 1 {
                    defmt::write!(f, "{} kHz", self.raw)
                } else if NOM == 1_000_000 && DENOM == 1 {
                    defmt::write!(f, "{} MHz", self.raw)
                } else if NOM == 1_000_000_000 && DENOM == 1 {
                    defmt::write!(f, "{} GHz", self.raw)
                } else {
                    defmt::write!(f, "{} raw @ ({}/{})", self.raw, NOM, DENOM)
                }
            }
        }

        impl<const NOM: u32, const DENOM: u32> core::fmt::Display for Rate<$i, NOM, DENOM> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                if NOM == 1 && DENOM == 1 {
                    write!(f, "{} Hz", self.raw)
                } else if NOM == 1_000 && DENOM == 1 {
                    write!(f, "{} kHz", self.raw)
                } else if NOM == 1_000_000 && DENOM == 1 {
                    write!(f, "{} MHz", self.raw)
                } else if NOM == 1_000_000_000 && DENOM == 1 {
                    write!(f, "{} GHz", self.raw)
                } else {
                    write!(f, "{} raw @ ({}/{})", self.raw, NOM, DENOM)
                }
            }
        }
    };
}

impl_rate_for_integer!(u32);
impl_rate_for_integer!(u64);

//
// Operations between u32 and u64 Rate
//

impl<const NOM: u32, const DENOM: u32> From<Rate<u32, NOM, DENOM>> for Rate<u64, NOM, DENOM> {
    #[inline]
    fn from(val: Rate<u32, NOM, DENOM>) -> Rate<u64, NOM, DENOM> {
        Rate::<u64, NOM, DENOM>::from_raw(val.raw() as u64)
    }
}

impl<const NOM: u32, const DENOM: u32> convert::TryFrom<Rate<u64, NOM, DENOM>>
    for Rate<u32, NOM, DENOM>
{
    type Error = ();

    #[inline]
    fn try_from(val: Rate<u64, NOM, DENOM>) -> Result<Rate<u32, NOM, DENOM>, ()> {
        Ok(Rate::<u32, NOM, DENOM>::from_raw(
            val.raw().try_into().map_err(|_| ())?,
        ))
    }
}

// Rate - Rate = Rate (to make shorthands work, until const_generics_defaults is
// stabilized)
impl<const NOM: u32, const DENOM: u32> ops::Sub<Rate<u32, NOM, DENOM>> for Rate<u64, NOM, DENOM> {
    type Output = Rate<u64, NOM, DENOM>;

    #[inline]
    fn sub(self, other: Rate<u32, NOM, DENOM>) -> Self::Output {
        if let Some(v) = self.checked_sub(Rate::<u64, NOM, DENOM>::from_raw(other.raw() as u64)) {
            v
        } else {
            panic!("Sub failed!");
        }
    }
}

// Rate -= Rate (to make shorthands work, until const_generics_defaults is stabilized)
impl<const NOM: u32, const DENOM: u32> ops::SubAssign<Rate<u32, NOM, DENOM>>
    for Rate<u64, NOM, DENOM>
{
    #[inline]
    fn sub_assign(&mut self, other: Rate<u32, NOM, DENOM>) {
        *self = *self - other;
    }
}

// Rate + Rate = Rate (to make shorthands work, until const_generics_defaults is
// stabilized)
impl<const NOM: u32, const DENOM: u32> ops::Add<Rate<u32, NOM, DENOM>> for Rate<u64, NOM, DENOM> {
    type Output = Rate<u64, NOM, DENOM>;

    #[inline]
    fn add(self, other: Rate<u32, NOM, DENOM>) -> Self::Output {
        if let Some(v) = self.checked_add(Rate::<u64, NOM, DENOM>::from_raw(other.raw() as u64)) {
            v
        } else {
            panic!("Add failed!");
        }
    }
}

// Rate += Rate (to make shorthands work, until const_generics_defaults is stabilized)
impl<const NOM: u32, const DENOM: u32> ops::AddAssign<Rate<u32, NOM, DENOM>>
    for Rate<u64, NOM, DENOM>
{
    #[inline]
    fn add_assign(&mut self, other: Rate<u32, NOM, DENOM>) {
        *self = *self + other;
    }
}

impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
    PartialOrd<Rate<u32, R_NOM, R_DENOM>> for Rate<u64, L_NOM, L_DENOM>
{
    #[inline]
    fn partial_cmp(&self, other: &Rate<u32, R_NOM, R_DENOM>) -> Option<Ordering> {
        self.partial_cmp(&Rate::<u64, R_NOM, R_DENOM>::from_raw(other.raw() as u64))
    }
}

impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
    PartialEq<Rate<u32, R_NOM, R_DENOM>> for Rate<u64, L_NOM, L_DENOM>
{
    #[inline]
    fn eq(&self, other: &Rate<u32, R_NOM, R_DENOM>) -> bool {
        self.eq(&Rate::<u64, R_NOM, R_DENOM>::from_raw(other.raw() as u64))
    }
}

impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
    PartialOrd<Rate<u64, R_NOM, R_DENOM>> for Rate<u32, L_NOM, L_DENOM>
{
    #[inline]
    fn partial_cmp(&self, other: &Rate<u64, R_NOM, R_DENOM>) -> Option<Ordering> {
        Rate::<u64, L_NOM, L_DENOM>::from_raw(self.raw as u64).partial_cmp(other)
    }
}

impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
    PartialEq<Rate<u64, R_NOM, R_DENOM>> for Rate<u32, L_NOM, L_DENOM>
{
    #[inline]
    fn eq(&self, other: &Rate<u64, R_NOM, R_DENOM>) -> bool {
        Rate::<u64, L_NOM, L_DENOM>::from_raw(self.raw as u64).eq(other)
    }
}

/// Extension trait for simple short-hands for u32 Rate
pub trait ExtU32 {
    /// Shorthand for creating a rate which represents hertz.
    #[allow(non_snake_case)]
    fn Hz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM>;

    /// Shorthand for creating a rate which represents kilohertz.
    #[allow(non_snake_case)]
    fn kHz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM>;

    /// Shorthand for creating a rate which represents megahertz.
    #[allow(non_snake_case)]
    fn MHz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM>;
}

impl ExtU32 for u32 {
    #[inline]
    #[allow(non_snake_case)]
    fn Hz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM> {
        Rate::<u32, NOM, DENOM>::Hz(self)
    }

    #[inline]
    #[allow(non_snake_case)]
    fn kHz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM> {
        Rate::<u32, NOM, DENOM>::kHz(self)
    }

    #[inline]
    #[allow(non_snake_case)]
    fn MHz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM> {
        Rate::<u32, NOM, DENOM>::MHz(self)
    }
}

/// Extension trait for simple short-hands for u64 Rate
pub trait ExtU64 {
    /// Shorthand for creating a rate which represents hertz.
    #[allow(non_snake_case)]
    fn Hz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM>;

    /// Shorthand for creating a rate which represents kilohertz.
    #[allow(non_snake_case)]
    fn kHz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM>;

    /// Shorthand for creating a rate which represents megahertz.
    #[allow(non_snake_case)]
    fn MHz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM>;
}

impl ExtU64 for u64 {
    #[inline]
    #[allow(non_snake_case)]
    fn Hz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM> {
        Rate::<u64, NOM, DENOM>::Hz(self)
    }

    #[inline]
    #[allow(non_snake_case)]
    fn kHz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM> {
        Rate::<u64, NOM, DENOM>::kHz(self)
    }

    #[inline]
    #[allow(non_snake_case)]
    fn MHz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM> {
        Rate::<u64, NOM, DENOM>::MHz(self)
    }
}
