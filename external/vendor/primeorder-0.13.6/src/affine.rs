//! Affine curve points.

#![allow(clippy::op_ref)]

use crate::{PrimeCurveParams, ProjectivePoint};
use core::{
    borrow::Borrow,
    ops::{Mul, Neg},
};
use elliptic_curve::{
    ff::{Field, PrimeField},
    generic_array::ArrayLength,
    group::{prime::PrimeCurveAffine, GroupEncoding},
    point::{AffineCoordinates, DecompactPoint, DecompressPoint, Double},
    sec1::{
        self, CompressedPoint, EncodedPoint, FromEncodedPoint, ModulusSize, ToCompactEncodedPoint,
        ToEncodedPoint, UncompressedPointSize,
    },
    subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, CtOption},
    zeroize::DefaultIsZeroes,
    Error, FieldBytes, FieldBytesEncoding, FieldBytesSize, PublicKey, Result, Scalar,
};

#[cfg(feature = "serde")]
use serdect::serde::{de, ser, Deserialize, Serialize};

/// Point on a Weierstrass curve in affine coordinates.
#[derive(Clone, Copy, Debug)]
pub struct AffinePoint<C: PrimeCurveParams> {
    /// x-coordinate
    pub(crate) x: C::FieldElement,

    /// y-coordinate
    pub(crate) y: C::FieldElement,

    /// Is this point the point at infinity? 0 = no, 1 = yes
    ///
    /// This is a proxy for [`Choice`], but uses `u8` instead to permit `const`
    /// constructors for `IDENTITY` and `GENERATOR`.
    pub(crate) infinity: u8,
}

impl<C> AffinePoint<C>
where
    C: PrimeCurveParams,
{
    /// Additive identity of the group a.k.a. the point at infinity.
    pub const IDENTITY: Self = Self {
        x: C::FieldElement::ZERO,
        y: C::FieldElement::ZERO,
        infinity: 1,
    };

    /// Base point of the curve.
    pub const GENERATOR: Self = Self {
        x: C::GENERATOR.0,
        y: C::GENERATOR.1,
        infinity: 0,
    };

    /// Is this point the point at infinity?
    pub fn is_identity(&self) -> Choice {
        Choice::from(self.infinity)
    }

    /// Conditionally negate [`AffinePoint`] for use with point compaction.
    fn to_compact(self) -> Self {
        let neg_self = -self;
        let choice = C::Uint::decode_field_bytes(&self.y.to_repr())
            .ct_gt(&C::Uint::decode_field_bytes(&neg_self.y.to_repr()));

        Self {
            x: self.x,
            y: C::FieldElement::conditional_select(&self.y, &neg_self.y, choice),
            infinity: self.infinity,
        }
    }
}

impl<C> AffineCoordinates for AffinePoint<C>
where
    C: PrimeCurveParams,
{
    type FieldRepr = FieldBytes<C>;

    fn x(&self) -> FieldBytes<C> {
        self.x.to_repr()
    }

    fn y_is_odd(&self) -> Choice {
        self.y.is_odd()
    }
}

impl<C> ConditionallySelectable for AffinePoint<C>
where
    C: PrimeCurveParams,
{
    #[inline(always)]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            x: C::FieldElement::conditional_select(&a.x, &b.x, choice),
            y: C::FieldElement::conditional_select(&a.y, &b.y, choice),
            infinity: u8::conditional_select(&a.infinity, &b.infinity, choice),
        }
    }
}

impl<C> ConstantTimeEq for AffinePoint<C>
where
    C: PrimeCurveParams,
{
    fn ct_eq(&self, other: &Self) -> Choice {
        self.x.ct_eq(&other.x) & self.y.ct_eq(&other.y) & self.infinity.ct_eq(&other.infinity)
    }
}

impl<C> Default for AffinePoint<C>
where
    C: PrimeCurveParams,
{
    fn default() -> Self {
        Self::IDENTITY
    }
}

impl<C> DefaultIsZeroes for AffinePoint<C> where C: PrimeCurveParams {}

impl<C> DecompressPoint<C> for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
{
    fn decompress(x_bytes: &FieldBytes<C>, y_is_odd: Choice) -> CtOption<Self> {
        C::FieldElement::from_repr(*x_bytes).and_then(|x| {
            let alpha = x * &x * &x + &(C::EQUATION_A * &x) + &C::EQUATION_B;
            let beta = alpha.sqrt();

            beta.map(|beta| {
                let y = C::FieldElement::conditional_select(
                    &-beta,
                    &beta,
                    beta.is_odd().ct_eq(&y_is_odd),
                );

                Self { x, y, infinity: 0 }
            })
        })
    }
}

impl<C> DecompactPoint<C> for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
{
    fn decompact(x_bytes: &FieldBytes<C>) -> CtOption<Self> {
        Self::decompress(x_bytes, Choice::from(0)).map(|point| point.to_compact())
    }
}

impl<C> Eq for AffinePoint<C> where C: PrimeCurveParams {}

impl<C> FromEncodedPoint<C> for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
    FieldBytesSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
{
    /// Attempts to parse the given [`EncodedPoint`] as an SEC1-encoded
    /// [`AffinePoint`].
    ///
    /// # Returns
    ///
    /// `None` value if `encoded_point` is not on the secp384r1 curve.
    fn from_encoded_point(encoded_point: &EncodedPoint<C>) -> CtOption<Self> {
        match encoded_point.coordinates() {
            sec1::Coordinates::Identity => CtOption::new(Self::IDENTITY, 1.into()),
            sec1::Coordinates::Compact { x } => Self::decompact(x),
            sec1::Coordinates::Compressed { x, y_is_odd } => {
                Self::decompress(x, Choice::from(y_is_odd as u8))
            }
            sec1::Coordinates::Uncompressed { x, y } => {
                C::FieldElement::from_repr(*y).and_then(|y| {
                    C::FieldElement::from_repr(*x).and_then(|x| {
                        let lhs = y * &y;
                        let rhs = x * &x * &x + &(C::EQUATION_A * &x) + &C::EQUATION_B;
                        CtOption::new(Self { x, y, infinity: 0 }, lhs.ct_eq(&rhs))
                    })
                })
            }
        }
    }
}

impl<C> From<ProjectivePoint<C>> for AffinePoint<C>
where
    C: PrimeCurveParams,
{
    fn from(p: ProjectivePoint<C>) -> AffinePoint<C> {
        p.to_affine()
    }
}

impl<C> From<&ProjectivePoint<C>> for AffinePoint<C>
where
    C: PrimeCurveParams,
{
    fn from(p: &ProjectivePoint<C>) -> AffinePoint<C> {
        p.to_affine()
    }
}

impl<C> From<PublicKey<C>> for AffinePoint<C>
where
    C: PrimeCurveParams,
{
    fn from(public_key: PublicKey<C>) -> AffinePoint<C> {
        *public_key.as_affine()
    }
}

impl<C> From<&PublicKey<C>> for AffinePoint<C>
where
    C: PrimeCurveParams,
{
    fn from(public_key: &PublicKey<C>) -> AffinePoint<C> {
        AffinePoint::from(*public_key)
    }
}

impl<C> From<AffinePoint<C>> for EncodedPoint<C>
where
    C: PrimeCurveParams,
    FieldBytesSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
    <UncompressedPointSize<C> as ArrayLength<u8>>::ArrayType: Copy,
{
    fn from(affine: AffinePoint<C>) -> EncodedPoint<C> {
        affine.to_encoded_point(false)
    }
}

impl<C> GroupEncoding for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
    FieldBytesSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
    <UncompressedPointSize<C> as ArrayLength<u8>>::ArrayType: Copy,
{
    type Repr = CompressedPoint<C>;

    /// NOTE: not constant-time with respect to identity point
    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        EncodedPoint::<C>::from_bytes(bytes)
            .map(|point| CtOption::new(point, Choice::from(1)))
            .unwrap_or_else(|_| {
                // SEC1 identity encoding is technically 1-byte 0x00, but the
                // `GroupEncoding` API requires a fixed-width `Repr`
                let is_identity = bytes.ct_eq(&Self::Repr::default());
                CtOption::new(EncodedPoint::<C>::identity(), is_identity)
            })
            .and_then(|point| Self::from_encoded_point(&point))
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        // No unchecked conversion possible for compressed points
        Self::from_bytes(bytes)
    }

    fn to_bytes(&self) -> Self::Repr {
        let encoded = self.to_encoded_point(true);
        let mut result = CompressedPoint::<C>::default();
        result[..encoded.len()].copy_from_slice(encoded.as_bytes());
        result
    }
}

impl<C> PartialEq for AffinePoint<C>
where
    C: PrimeCurveParams,
{
    fn eq(&self, other: &Self) -> bool {
        self.ct_eq(other).into()
    }
}

impl<C> PrimeCurveAffine for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
    FieldBytesSize<C>: ModulusSize,
    ProjectivePoint<C>: Double,
    CompressedPoint<C>: Copy,
    <UncompressedPointSize<C> as ArrayLength<u8>>::ArrayType: Copy,
{
    type Curve = ProjectivePoint<C>;
    type Scalar = Scalar<C>;

    fn identity() -> AffinePoint<C> {
        Self::IDENTITY
    }

    fn generator() -> AffinePoint<C> {
        Self::GENERATOR
    }

    fn is_identity(&self) -> Choice {
        self.is_identity()
    }

    fn to_curve(&self) -> ProjectivePoint<C> {
        ProjectivePoint::from(*self)
    }
}

impl<C> ToCompactEncodedPoint<C> for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytesSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
    <UncompressedPointSize<C> as ArrayLength<u8>>::ArrayType: Copy,
{
    /// Serialize this value as a  SEC1 compact [`EncodedPoint`]
    fn to_compact_encoded_point(&self) -> CtOption<EncodedPoint<C>> {
        let point = self.to_compact();

        let mut bytes = CompressedPoint::<C>::default();
        bytes[0] = sec1::Tag::Compact.into();
        bytes[1..].copy_from_slice(&point.x.to_repr());

        let encoded = EncodedPoint::<C>::from_bytes(bytes);
        let is_some = point.y.ct_eq(&self.y);
        CtOption::new(encoded.unwrap_or_default(), is_some)
    }
}

impl<C> ToEncodedPoint<C> for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytesSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
    <UncompressedPointSize<C> as ArrayLength<u8>>::ArrayType: Copy,
{
    fn to_encoded_point(&self, compress: bool) -> EncodedPoint<C> {
        EncodedPoint::<C>::conditional_select(
            &EncodedPoint::<C>::from_affine_coordinates(
                &self.x.to_repr(),
                &self.y.to_repr(),
                compress,
            ),
            &EncodedPoint::<C>::identity(),
            self.is_identity(),
        )
    }
}

impl<C> TryFrom<EncodedPoint<C>> for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
    FieldBytesSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
{
    type Error = Error;

    fn try_from(point: EncodedPoint<C>) -> Result<AffinePoint<C>> {
        AffinePoint::try_from(&point)
    }
}

impl<C> TryFrom<&EncodedPoint<C>> for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
    FieldBytesSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
{
    type Error = Error;

    fn try_from(point: &EncodedPoint<C>) -> Result<AffinePoint<C>> {
        Option::from(AffinePoint::<C>::from_encoded_point(point)).ok_or(Error)
    }
}

impl<C> TryFrom<AffinePoint<C>> for PublicKey<C>
where
    C: PrimeCurveParams,
{
    type Error = Error;

    fn try_from(affine_point: AffinePoint<C>) -> Result<PublicKey<C>> {
        PublicKey::from_affine(affine_point)
    }
}

impl<C> TryFrom<&AffinePoint<C>> for PublicKey<C>
where
    C: PrimeCurveParams,
{
    type Error = Error;

    fn try_from(affine_point: &AffinePoint<C>) -> Result<PublicKey<C>> {
        PublicKey::<C>::try_from(*affine_point)
    }
}

//
// Arithmetic trait impls
//

impl<C, S> Mul<S> for AffinePoint<C>
where
    C: PrimeCurveParams,
    S: Borrow<Scalar<C>>,
    ProjectivePoint<C>: Double,
{
    type Output = ProjectivePoint<C>;

    fn mul(self, scalar: S) -> ProjectivePoint<C> {
        ProjectivePoint::<C>::from(self) * scalar
    }
}

impl<C> Neg for AffinePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = Self;

    fn neg(self) -> Self {
        AffinePoint {
            x: self.x,
            y: -self.y,
            infinity: self.infinity,
        }
    }
}

impl<C> Neg for &AffinePoint<C>
where
    C: PrimeCurveParams,
{
    type Output = AffinePoint<C>;

    fn neg(self) -> AffinePoint<C> {
        -(*self)
    }
}

//
// serde support
//

#[cfg(feature = "serde")]
impl<C> Serialize for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytesSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
    <UncompressedPointSize<C> as ArrayLength<u8>>::ArrayType: Copy,
{
    fn serialize<S>(&self, serializer: S) -> core::result::Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        self.to_encoded_point(true).serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, C> Deserialize<'de> for AffinePoint<C>
where
    C: PrimeCurveParams,
    FieldBytes<C>: Copy,
    FieldBytesSize<C>: ModulusSize,
    CompressedPoint<C>: Copy,
{
    fn deserialize<D>(deserializer: D) -> core::result::Result<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        EncodedPoint::<C>::deserialize(deserializer)?
            .try_into()
            .map_err(de::Error::custom)
    }
}
