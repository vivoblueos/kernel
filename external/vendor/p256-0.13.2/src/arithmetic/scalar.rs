//! Scalar field arithmetic modulo n = 115792089210356248762697446949407573529996955224135760342422259061068512044369

#[cfg_attr(target_pointer_width = "32", path = "scalar/scalar32.rs")]
#[cfg_attr(target_pointer_width = "64", path = "scalar/scalar64.rs")]
mod scalar_impl;

use self::scalar_impl::barrett_reduce;
use crate::{FieldBytes, NistP256, SecretKey, ORDER_HEX};
use core::{
    fmt::{self, Debug},
    iter::{Product, Sum},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Shr, ShrAssign, Sub, SubAssign},
};
use elliptic_curve::{
    bigint::{prelude::*, Limb, U256},
    group::ff::{self, Field, PrimeField},
    ops::{Invert, Reduce, ReduceNonZero},
    rand_core::RngCore,
    scalar::{FromUintUnchecked, IsHigh},
    subtle::{
        Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess,
        CtOption,
    },
    zeroize::DefaultIsZeroes,
    Curve, ScalarPrimitive,
};

#[cfg(feature = "bits")]
use {crate::ScalarBits, elliptic_curve::group::ff::PrimeFieldBits};

#[cfg(feature = "serde")]
use serdect::serde::{de, ser, Deserialize, Serialize};

/// Constant representing the modulus
/// n = FFFFFFFF 00000000 FFFFFFFF FFFFFFFF BCE6FAAD A7179E84 F3B9CAC2 FC632551
pub(crate) const MODULUS: U256 = NistP256::ORDER;

/// `MODULUS / 2`
const FRAC_MODULUS_2: Scalar = Scalar(MODULUS.shr_vartime(1));

/// MU = floor(2^512 / n)
///    = 115792089264276142090721624801893421302707618245269942344307673200490803338238
///    = 0x100000000fffffffffffffffeffffffff43190552df1a6c21012ffd85eedf9bfe
pub const MU: [u64; 5] = [
    0x012f_fd85_eedf_9bfe,
    0x4319_0552_df1a_6c21,
    0xffff_fffe_ffff_ffff,
    0x0000_0000_ffff_ffff,
    0x0000_0000_0000_0001,
];

/// Scalars are elements in the finite field modulo n.
///
/// # Trait impls
///
/// Much of the important functionality of scalars is provided by traits from
/// the [`ff`](https://docs.rs/ff/) crate, which is re-exported as
/// `p256::elliptic_curve::ff`:
///
/// - [`Field`](https://docs.rs/ff/latest/ff/trait.Field.html) -
///   represents elements of finite fields and provides:
///   - [`Field::random`](https://docs.rs/ff/latest/ff/trait.Field.html#tymethod.random) -
///     generate a random scalar
///   - `double`, `square`, and `invert` operations
///   - Bounds for [`Add`], [`Sub`], [`Mul`], and [`Neg`] (as well as `*Assign` equivalents)
///   - Bounds for [`ConditionallySelectable`] from the `subtle` crate
/// - [`PrimeField`](https://docs.rs/ff/latest/ff/trait.PrimeField.html) -
///   represents elements of prime fields and provides:
///   - `from_repr`/`to_repr` for converting field elements from/to big integers.
///   - `multiplicative_generator` and `root_of_unity` constants.
/// - [`PrimeFieldBits`](https://docs.rs/ff/latest/ff/trait.PrimeFieldBits.html) -
///   operations over field elements represented as bits (requires `bits` feature)
///
/// Please see the documentation for the relevant traits for more information.
///
/// # `serde` support
///
/// When the `serde` feature of this crate is enabled, the `Serialize` and
/// `Deserialize` traits are impl'd for this type.
///
/// The serialization is a fixed-width big endian encoding. When used with
/// textual formats, the binary data is encoded as hexadecimal.
#[derive(Clone, Copy, Default)]
pub struct Scalar(pub(crate) U256);

impl Scalar {
    /// Zero scalar.
    pub const ZERO: Self = Self(U256::ZERO);

    /// Multiplicative identity.
    pub const ONE: Self = Self(U256::ONE);

    /// Returns the SEC1 encoding of this scalar.
    pub fn to_bytes(&self) -> FieldBytes {
        self.0.to_be_byte_array()
    }

    /// Returns self + rhs mod n
    pub const fn add(&self, rhs: &Self) -> Self {
        Self(self.0.add_mod(&rhs.0, &NistP256::ORDER))
    }

    /// Returns 2*self.
    pub const fn double(&self) -> Self {
        self.add(self)
    }

    /// Returns self - rhs mod n.
    pub const fn sub(&self, rhs: &Self) -> Self {
        Self(self.0.sub_mod(&rhs.0, &NistP256::ORDER))
    }

    /// Returns self * rhs mod n
    pub const fn multiply(&self, rhs: &Self) -> Self {
        let (lo, hi) = self.0.mul_wide(&rhs.0);
        Self(barrett_reduce(lo, hi))
    }

    /// Returns self * self mod p
    pub const fn square(&self) -> Self {
        // Schoolbook multiplication.
        self.multiply(self)
    }

    /// Right shifts the scalar.
    ///
    /// Note: not constant-time with respect to the `shift` parameter.
    pub const fn shr_vartime(&self, shift: usize) -> Scalar {
        Self(self.0.shr_vartime(shift))
    }

    /// Returns the multiplicative inverse of self, if self is non-zero
    pub fn invert(&self) -> CtOption<Self> {
        CtOption::new(self.invert_unchecked(), !self.is_zero())
    }

    /// Returns the multiplicative inverse of self.
    ///
    /// Does not check that self is non-zero.
    const fn invert_unchecked(&self) -> Self {
        // We need to find b such that b * a ≡ 1 mod p. As we are in a prime
        // field, we can apply Fermat's Little Theorem:
        //
        //    a^p         ≡ a mod p
        //    a^(p-1)     ≡ 1 mod p
        //    a^(p-2) * a ≡ 1 mod p
        //
        // Thus inversion can be implemented with a single exponentiation.
        //
        // This is `n - 2`, so the top right two digits are `4f` instead of `51`.
        self.pow_vartime(&[
            0xf3b9_cac2_fc63_254f,
            0xbce6_faad_a717_9e84,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_0000_0000,
        ])
    }

    /// Exponentiates `self` by `exp`, where `exp` is a little-endian order integer
    /// exponent.
    pub const fn pow_vartime(&self, exp: &[u64]) -> Self {
        let mut res = Self::ONE;

        let mut i = exp.len();
        while i > 0 {
            i -= 1;

            let mut j = 64;
            while j > 0 {
                j -= 1;
                res = res.square();

                if ((exp[i] >> j) & 1) == 1 {
                    res = res.multiply(self);
                }
            }
        }

        res
    }

    /// Is integer representing equivalence class odd?
    pub fn is_odd(&self) -> Choice {
        self.0.is_odd()
    }

    /// Is integer representing equivalence class even?
    pub fn is_even(&self) -> Choice {
        !self.is_odd()
    }
}

impl AsRef<Scalar> for Scalar {
    fn as_ref(&self) -> &Scalar {
        self
    }
}

impl Field for Scalar {
    const ZERO: Self = Self::ZERO;
    const ONE: Self = Self::ONE;

    fn random(mut rng: impl RngCore) -> Self {
        let mut bytes = FieldBytes::default();

        // Generate a uniformly random scalar using rejection sampling,
        // which produces a uniformly random distribution of scalars.
        //
        // This method is not constant time, but should be secure so long as
        // rejected RNG outputs are unrelated to future ones (which is a
        // necessary property of a `CryptoRng`).
        //
        // With an unbiased RNG, the probability of failing to complete after 4
        // iterations is vanishingly small.
        loop {
            rng.fill_bytes(&mut bytes);
            if let Some(scalar) = Scalar::from_repr(bytes).into() {
                return scalar;
            }
        }
    }

    #[must_use]
    fn square(&self) -> Self {
        Scalar::square(self)
    }

    #[must_use]
    fn double(&self) -> Self {
        self.add(self)
    }

    fn invert(&self) -> CtOption<Self> {
        Scalar::invert(self)
    }

    /// Tonelli-Shank's algorithm for q mod 16 = 1
    /// <https://eprint.iacr.org/2012/685.pdf> (page 12, algorithm 5)
    #[allow(clippy::many_single_char_names)]
    fn sqrt(&self) -> CtOption<Self> {
        // Note: `pow_vartime` is constant-time with respect to `self`
        let w = self.pow_vartime(&[
            0x279dce5617e3192a,
            0xfde737d56d38bcf4,
            0x07ffffffffffffff,
            0x07fffffff8000000,
        ]);

        let mut v = Self::S;
        let mut x = *self * w;
        let mut b = x * w;
        let mut z = Self::ROOT_OF_UNITY;

        for max_v in (1..=Self::S).rev() {
            let mut k = 1;
            let mut tmp = b.square();
            let mut j_less_than_v = Choice::from(1);

            for j in 2..max_v {
                let tmp_is_one = tmp.ct_eq(&Self::ONE);
                let squared = Self::conditional_select(&tmp, &z, tmp_is_one).square();
                tmp = Self::conditional_select(&squared, &tmp, tmp_is_one);
                let new_z = Self::conditional_select(&z, &squared, tmp_is_one);
                j_less_than_v &= !j.ct_eq(&v);
                k = u32::conditional_select(&j, &k, tmp_is_one);
                z = Self::conditional_select(&z, &new_z, j_less_than_v);
            }

            let result = x * z;
            x = Self::conditional_select(&result, &x, b.ct_eq(&Self::ONE));
            z = z.square();
            b *= z;
            v = k;
        }

        CtOption::new(x, x.square().ct_eq(self))
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        ff::helpers::sqrt_ratio_generic(num, div)
    }
}

impl PrimeField for Scalar {
    type Repr = FieldBytes;

    const MODULUS: &'static str = ORDER_HEX;
    const NUM_BITS: u32 = 256;
    const CAPACITY: u32 = 255;
    const TWO_INV: Self = Self(U256::from_u8(2)).invert_unchecked();
    const MULTIPLICATIVE_GENERATOR: Self = Self(U256::from_u8(7));
    const S: u32 = 4;
    const ROOT_OF_UNITY: Self = Self(U256::from_be_hex(
        "ffc97f062a770992ba807ace842a3dfc1546cad004378daf0592d7fbb41e6602",
    ));
    const ROOT_OF_UNITY_INV: Self = Self::ROOT_OF_UNITY.invert_unchecked();
    const DELTA: Self = Self(U256::from_u64(33232930569601));

    /// Attempts to parse the given byte array as an SEC1-encoded scalar.
    ///
    /// Returns None if the byte array does not contain a big-endian integer in the range
    /// [0, p).
    fn from_repr(bytes: FieldBytes) -> CtOption<Self> {
        let inner = U256::from_be_byte_array(bytes);
        CtOption::new(Self(inner), inner.ct_lt(&NistP256::ORDER))
    }

    fn to_repr(&self) -> FieldBytes {
        self.to_bytes()
    }

    fn is_odd(&self) -> Choice {
        self.0.is_odd()
    }
}

#[cfg(feature = "bits")]
impl PrimeFieldBits for Scalar {
    #[cfg(target_pointer_width = "32")]
    type ReprBits = [u32; 8];

    #[cfg(target_pointer_width = "64")]
    type ReprBits = [u64; 4];

    fn to_le_bits(&self) -> ScalarBits {
        self.into()
    }

    fn char_le_bits() -> ScalarBits {
        NistP256::ORDER.to_words().into()
    }
}

impl DefaultIsZeroes for Scalar {}

impl Eq for Scalar {}

impl FromUintUnchecked for Scalar {
    type Uint = U256;

    fn from_uint_unchecked(uint: Self::Uint) -> Self {
        Self(uint)
    }
}

impl Invert for Scalar {
    type Output = CtOption<Self>;

    fn invert(&self) -> CtOption<Self> {
        self.invert()
    }

    /// Fast variable-time inversion using Stein's algorithm.
    ///
    /// Returns none if the scalar is zero.
    ///
    /// <https://link.springer.com/article/10.1007/s13389-016-0135-4>
    ///
    /// ⚠️ WARNING!
    ///
    /// This method should not be used with (unblinded) secret scalars, as its
    /// variable-time operation can potentially leak secrets through
    /// sidechannels.
    #[allow(non_snake_case)]
    fn invert_vartime(&self) -> CtOption<Self> {
        let mut u = *self;
        let mut v = Self(MODULUS);
        let mut A = Self::ONE;
        let mut C = Self::ZERO;

        while !bool::from(u.is_zero()) {
            // u-loop
            while bool::from(u.is_even()) {
                u >>= 1;

                let was_odd: bool = A.is_odd().into();
                A >>= 1;

                if was_odd {
                    A += FRAC_MODULUS_2;
                    A += Self::ONE;
                }
            }

            // v-loop
            while bool::from(v.is_even()) {
                v >>= 1;

                let was_odd: bool = C.is_odd().into();
                C >>= 1;

                if was_odd {
                    C += FRAC_MODULUS_2;
                    C += Self::ONE;
                }
            }

            // sub-step
            if u >= v {
                u -= &v;
                A -= &C;
            } else {
                v -= &u;
                C -= &A;
            }
        }

        CtOption::new(C, !self.is_zero())
    }
}

impl IsHigh for Scalar {
    fn is_high(&self) -> Choice {
        self.0.ct_gt(&FRAC_MODULUS_2.0)
    }
}

impl Shr<usize> for Scalar {
    type Output = Self;

    fn shr(self, rhs: usize) -> Self::Output {
        self.shr_vartime(rhs)
    }
}

impl Shr<usize> for &Scalar {
    type Output = Scalar;

    fn shr(self, rhs: usize) -> Self::Output {
        self.shr_vartime(rhs)
    }
}

impl ShrAssign<usize> for Scalar {
    fn shr_assign(&mut self, rhs: usize) {
        *self = *self >> rhs;
    }
}

impl PartialEq for Scalar {
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl PartialOrd for Scalar {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Scalar {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl From<u32> for Scalar {
    fn from(k: u32) -> Self {
        Scalar(k.into())
    }
}

impl From<u64> for Scalar {
    fn from(k: u64) -> Self {
        Scalar(k.into())
    }
}

impl From<u128> for Scalar {
    fn from(k: u128) -> Self {
        Scalar(k.into())
    }
}

impl From<Scalar> for FieldBytes {
    fn from(scalar: Scalar) -> Self {
        scalar.to_bytes()
    }
}

impl From<&Scalar> for FieldBytes {
    fn from(scalar: &Scalar) -> Self {
        scalar.to_bytes()
    }
}

impl From<ScalarPrimitive<NistP256>> for Scalar {
    fn from(scalar: ScalarPrimitive<NistP256>) -> Scalar {
        Scalar(*scalar.as_uint())
    }
}

impl From<&ScalarPrimitive<NistP256>> for Scalar {
    fn from(scalar: &ScalarPrimitive<NistP256>) -> Scalar {
        Scalar(*scalar.as_uint())
    }
}

impl From<Scalar> for ScalarPrimitive<NistP256> {
    fn from(scalar: Scalar) -> ScalarPrimitive<NistP256> {
        ScalarPrimitive::from(&scalar)
    }
}

impl From<&Scalar> for ScalarPrimitive<NistP256> {
    fn from(scalar: &Scalar) -> ScalarPrimitive<NistP256> {
        ScalarPrimitive::new(scalar.0).unwrap()
    }
}

impl From<&SecretKey> for Scalar {
    fn from(secret_key: &SecretKey) -> Scalar {
        *secret_key.to_nonzero_scalar()
    }
}

impl From<Scalar> for U256 {
    fn from(scalar: Scalar) -> U256 {
        scalar.0
    }
}

impl From<&Scalar> for U256 {
    fn from(scalar: &Scalar) -> U256 {
        scalar.0
    }
}

#[cfg(feature = "bits")]
impl From<&Scalar> for ScalarBits {
    fn from(scalar: &Scalar) -> ScalarBits {
        scalar.0.to_words().into()
    }
}

impl Add<Scalar> for Scalar {
    type Output = Scalar;

    fn add(self, other: Scalar) -> Scalar {
        Scalar::add(&self, &other)
    }
}

impl Add<&Scalar> for &Scalar {
    type Output = Scalar;

    fn add(self, other: &Scalar) -> Scalar {
        Scalar::add(self, other)
    }
}

impl Add<&Scalar> for Scalar {
    type Output = Scalar;

    fn add(self, other: &Scalar) -> Scalar {
        Scalar::add(&self, other)
    }
}

impl AddAssign<Scalar> for Scalar {
    fn add_assign(&mut self, rhs: Scalar) {
        *self = Scalar::add(self, &rhs);
    }
}

impl AddAssign<&Scalar> for Scalar {
    fn add_assign(&mut self, rhs: &Scalar) {
        *self = Scalar::add(self, rhs);
    }
}

impl Sub<Scalar> for Scalar {
    type Output = Scalar;

    fn sub(self, other: Scalar) -> Scalar {
        Scalar::sub(&self, &other)
    }
}

impl Sub<&Scalar> for &Scalar {
    type Output = Scalar;

    fn sub(self, other: &Scalar) -> Scalar {
        Scalar::sub(self, other)
    }
}

impl Sub<&Scalar> for Scalar {
    type Output = Scalar;

    fn sub(self, other: &Scalar) -> Scalar {
        Scalar::sub(&self, other)
    }
}

impl SubAssign<Scalar> for Scalar {
    fn sub_assign(&mut self, rhs: Scalar) {
        *self = Scalar::sub(self, &rhs);
    }
}

impl SubAssign<&Scalar> for Scalar {
    fn sub_assign(&mut self, rhs: &Scalar) {
        *self = Scalar::sub(self, rhs);
    }
}

impl Mul<Scalar> for Scalar {
    type Output = Scalar;

    fn mul(self, other: Scalar) -> Scalar {
        Scalar::multiply(&self, &other)
    }
}

impl Mul<&Scalar> for &Scalar {
    type Output = Scalar;

    fn mul(self, other: &Scalar) -> Scalar {
        Scalar::multiply(self, other)
    }
}

impl Mul<&Scalar> for Scalar {
    type Output = Scalar;

    fn mul(self, other: &Scalar) -> Scalar {
        Scalar::multiply(&self, other)
    }
}

impl MulAssign<Scalar> for Scalar {
    fn mul_assign(&mut self, rhs: Scalar) {
        *self = Scalar::multiply(self, &rhs);
    }
}

impl MulAssign<&Scalar> for Scalar {
    fn mul_assign(&mut self, rhs: &Scalar) {
        *self = Scalar::multiply(self, rhs);
    }
}

impl Neg for Scalar {
    type Output = Scalar;

    fn neg(self) -> Scalar {
        Scalar::ZERO - self
    }
}

impl<'a> Neg for &'a Scalar {
    type Output = Scalar;

    fn neg(self) -> Scalar {
        Scalar::ZERO - self
    }
}

impl Reduce<U256> for Scalar {
    type Bytes = FieldBytes;

    fn reduce(w: U256) -> Self {
        let (r, underflow) = w.sbb(&NistP256::ORDER, Limb::ZERO);
        let underflow = Choice::from((underflow.0 >> (Limb::BITS - 1)) as u8);
        Self(U256::conditional_select(&w, &r, !underflow))
    }

    fn reduce_bytes(bytes: &FieldBytes) -> Self {
        Self::reduce(U256::from_be_byte_array(*bytes))
    }
}

impl ReduceNonZero<U256> for Scalar {
    fn reduce_nonzero(w: U256) -> Self {
        const ORDER_MINUS_ONE: U256 = NistP256::ORDER.wrapping_sub(&U256::ONE);
        let (r, underflow) = w.sbb(&ORDER_MINUS_ONE, Limb::ZERO);
        let underflow = Choice::from((underflow.0 >> (Limb::BITS - 1)) as u8);
        Self(U256::conditional_select(&w, &r, !underflow).wrapping_add(&U256::ONE))
    }

    fn reduce_nonzero_bytes(bytes: &FieldBytes) -> Self {
        Self::reduce_nonzero(U256::from_be_byte_array(*bytes))
    }
}

impl Sum for Scalar {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(core::ops::Add::add).unwrap_or(Self::ZERO)
    }
}

impl<'a> Sum<&'a Scalar> for Scalar {
    fn sum<I: Iterator<Item = &'a Scalar>>(iter: I) -> Self {
        iter.copied().sum()
    }
}

impl Product for Scalar {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(core::ops::Mul::mul).unwrap_or(Self::ONE)
    }
}

impl<'a> Product<&'a Scalar> for Scalar {
    fn product<I: Iterator<Item = &'a Scalar>>(iter: I) -> Self {
        iter.copied().product()
    }
}

impl ConditionallySelectable for Scalar {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(U256::conditional_select(&a.0, &b.0, choice))
    }
}

impl ConstantTimeEq for Scalar {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl Debug for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Scalar(0x{:X})", &self.0)
    }
}

#[cfg(feature = "serde")]
impl Serialize for Scalar {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        ScalarPrimitive::from(self).serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Scalar {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        Ok(ScalarPrimitive::deserialize(deserializer)?.into())
    }
}

#[cfg(test)]
mod tests {
    use super::Scalar;
    use crate::{FieldBytes, SecretKey};
    use elliptic_curve::group::ff::{Field, PrimeField};
    use primeorder::{
        impl_field_identity_tests, impl_field_invert_tests, impl_field_sqrt_tests,
        impl_primefield_tests,
    };

    /// t = (modulus - 1) >> S
    const T: [u64; 4] = [
        0x4f3b9cac2fc63255,
        0xfbce6faada7179e8,
        0x0fffffffffffffff,
        0x0ffffffff0000000,
    ];

    impl_field_identity_tests!(Scalar);
    impl_field_invert_tests!(Scalar);
    impl_field_sqrt_tests!(Scalar);
    impl_primefield_tests!(Scalar, T);

    #[test]
    fn from_to_bytes_roundtrip() {
        let k: u64 = 42;
        let mut bytes = FieldBytes::default();
        bytes[24..].copy_from_slice(k.to_be_bytes().as_ref());

        let scalar = Scalar::from_repr(bytes).unwrap();
        assert_eq!(bytes, scalar.to_bytes());
    }

    /// Basic tests that multiplication works.
    #[test]
    fn multiply() {
        let one = Scalar::ONE;
        let two = one + &one;
        let three = two + &one;
        let six = three + &three;
        assert_eq!(six, two * &three);

        let minus_two = -two;
        let minus_three = -three;
        assert_eq!(two, -minus_two);

        assert_eq!(minus_three * &minus_two, minus_two * &minus_three);
        assert_eq!(six, minus_two * &minus_three);
    }

    /// Tests that a Scalar can be safely converted to a SecretKey and back
    #[test]
    fn from_ec_secret() {
        let scalar = Scalar::ONE;
        let secret = SecretKey::from_bytes(&scalar.to_bytes()).unwrap();
        let rederived_scalar = Scalar::from(&secret);
        assert_eq!(scalar.0, rederived_scalar.0);
    }

    #[test]
    #[cfg(all(feature = "bits", target_pointer_width = "32"))]
    fn scalar_into_scalarbits() {
        use crate::ScalarBits;

        let minus_one = ScalarBits::from([
            0xfc63_2550,
            0xf3b9_cac2,
            0xa717_9e84,
            0xbce6_faad,
            0xffff_ffff,
            0xffff_ffff,
            0x0000_0000,
            0xffff_ffff,
        ]);

        let scalar_bits = ScalarBits::from(&-Scalar::from(1u32));
        assert_eq!(minus_one, scalar_bits);
    }
}
