//! Point arithmetic implementation optimised for different curve equations
//!
//! Support for formulas specialized to the short Weierstrass equation's
//! 𝒂-coefficient.

use elliptic_curve::{subtle::ConditionallySelectable, Field};

use crate::{AffinePoint, PrimeCurveParams, ProjectivePoint};

mod sealed {
    use crate::{AffinePoint, PrimeCurveParams, ProjectivePoint};

    /// Elliptic point arithmetic implementation
    ///
    /// Provides implementation of point arithmetic (point addition, point doubling) which
    /// might be optimized for the curve.
    pub trait PointArithmetic<C: PrimeCurveParams> {
        /// Returns `lhs + rhs`
        fn add(lhs: &ProjectivePoint<C>, rhs: &ProjectivePoint<C>) -> ProjectivePoint<C>;

        /// Returns `lhs + rhs`
        fn add_mixed(lhs: &ProjectivePoint<C>, rhs: &AffinePoint<C>) -> ProjectivePoint<C>;

        /// Returns `point + point`
        fn double(point: &ProjectivePoint<C>) -> ProjectivePoint<C>;
    }
}

/// Allow crate-local visibility
pub(crate) use sealed::PointArithmetic;

/// The 𝒂-coefficient of the short Weierstrass equation does not have specific
/// properties which allow for an optimized implementation.
pub struct EquationAIsGeneric {}

impl<C: PrimeCurveParams> PointArithmetic<C> for EquationAIsGeneric {
    /// Implements complete addition for any curve
    ///
    /// Implements the complete addition formula from [Renes-Costello-Batina 2015]
    /// (Algorithm 1). The comments after each line indicate which algorithm steps
    /// are being performed.
    ///
    /// [Renes-Costello-Batina 2015]: https://eprint.iacr.org/2015/1060
    fn add(lhs: &ProjectivePoint<C>, rhs: &ProjectivePoint<C>) -> ProjectivePoint<C> {
        let b3 = C::FieldElement::from(3) * C::EQUATION_B;

        let t0 = lhs.x * rhs.x; // 1
        let t1 = lhs.y * rhs.y; // 2
        let t2 = lhs.z * rhs.z; // 3
        let t3 = lhs.x + lhs.y; // 4
        let t4 = rhs.x + rhs.y; // 5
        let t3 = t3 * t4; // 6
        let t4 = t0 + t1; // 7
        let t3 = t3 - t4; // 8
        let t4 = lhs.x + lhs.z; // 9
        let t5 = rhs.x + rhs.z; // 10
        let t4 = t4 * t5; // 11
        let t5 = t0 + t2; // 12
        let t4 = t4 - t5; // 13
        let t5 = lhs.y + lhs.z; // 14
        let x3 = rhs.y + rhs.z; // 15
        let t5 = t5 * x3; // 16
        let x3 = t1 + t2; // 17
        let t5 = t5 - x3; // 18
        let z3 = C::EQUATION_A * t4; // 19
        let x3 = b3 * t2; // 20
        let z3 = x3 + z3; // 21
        let x3 = t1 - z3; // 22
        let z3 = t1 + z3; // 23
        let y3 = x3 * z3; // 24
        let t1 = t0 + t0; // 25
        let t1 = t1 + t0; // 26
        let t2 = C::EQUATION_A * t2; // 27
        let t4 = b3 * t4; // 28
        let t1 = t1 + t2; // 29
        let t2 = t0 - t2; // 30
        let t2 = C::EQUATION_A * t2; // 31
        let t4 = t4 + t2; // 32
        let t0 = t1 * t4; // 33
        let y3 = y3 + t0; // 34
        let t0 = t5 * t4; // 35
        let x3 = t3 * x3; // 36
        let x3 = x3 - t0; // 37
        let t0 = t3 * t1; // 38
        let z3 = t5 * z3; // 39
        let z3 = z3 + t0; // 40

        ProjectivePoint {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    /// Implements complete mixed addition for curves with any `a`
    ///
    /// Implements the complete mixed addition formula from [Renes-Costello-Batina 2015]
    /// (Algorithm 2). The comments after each line indicate which algorithm
    /// steps are being performed.
    ///
    /// [Renes-Costello-Batina 2015]: https://eprint.iacr.org/2015/1060
    fn add_mixed(lhs: &ProjectivePoint<C>, rhs: &AffinePoint<C>) -> ProjectivePoint<C> {
        let b3 = C::EQUATION_B * C::FieldElement::from(3);

        let t0 = lhs.x * rhs.x; // 1
        let t1 = lhs.y * rhs.y; // 2
        let t3 = rhs.x + rhs.y; // 3
        let t4 = lhs.x + lhs.y; // 4
        let t3 = t3 * t4; // 5
        let t4 = t0 + t1; // 6
        let t3 = t3 - t4; // 7
        let t4 = rhs.x * lhs.z; // 8
        let t4 = t4 + lhs.x; // 9
        let t5 = rhs.y * lhs.z; // 10
        let t5 = t5 + lhs.y; // 11
        let z3 = C::EQUATION_A * t4; // 12
        let x3 = b3 * lhs.z; // 13
        let z3 = x3 + z3; // 14
        let x3 = t1 - z3; // 15
        let z3 = t1 + z3; // 16
        let y3 = x3 * z3; // 17
        let t1 = t0 + t0; // 18
        let t1 = t1 + t0; // 19
        let t2 = C::EQUATION_A * lhs.z; // 20
        let t4 = b3 * t4; // 21
        let t1 = t1 + t2; // 22
        let t2 = t0 - t2; // 23
        let t2 = C::EQUATION_A * t2; // 24
        let t4 = t4 + t2; // 25
        let t0 = t1 * t4; // 26
        let y3 = y3 + t0; // 27
        let t0 = t5 * t4; // 28
        let x3 = t3 * x3; // 29
        let x3 = x3 - t0; // 30
        let t0 = t3 * t1; // 31
        let z3 = t5 * z3; // 32
        let z3 = z3 + t0; // 33

        let mut ret = ProjectivePoint {
            x: x3,
            y: y3,
            z: z3,
        };
        ret.conditional_assign(lhs, rhs.is_identity());
        ret
    }

    /// Implements point doubling for curves with any `a`
    ///
    /// Implements the exception-free point doubling formula from [Renes-Costello-Batina 2015]
    /// (Algorithm 3). The comments after each line indicate which algorithm
    /// steps are being performed.
    ///
    /// [Renes-Costello-Batina 2015]: https://eprint.iacr.org/2015/1060
    fn double(point: &ProjectivePoint<C>) -> ProjectivePoint<C> {
        let b3 = C::EQUATION_B * C::FieldElement::from(3);

        let t0 = point.x * point.x; // 1
        let t1 = point.y * point.y; // 2
        let t2 = point.z * point.z; // 3
        let t3 = point.x * point.y; // 4
        let t3 = t3 + t3; // 5
        let z3 = point.x * point.z; // 6
        let z3 = z3 + z3; // 7
        let x3 = C::EQUATION_A * z3; // 8
        let y3 = b3 * t2; // 9
        let y3 = x3 + y3; // 10
        let x3 = t1 - y3; // 11
        let y3 = t1 + y3; // 12
        let y3 = x3 * y3; // 13
        let x3 = t3 * x3; // 14
        let z3 = b3 * z3; // 15
        let t2 = C::EQUATION_A * t2; // 16
        let t3 = t0 - t2; // 17
        let t3 = C::EQUATION_A * t3; // 18
        let t3 = t3 + z3; // 19
        let z3 = t0 + t0; // 20
        let t0 = z3 + t0; // 21
        let t0 = t0 + t2; // 22
        let t0 = t0 * t3; // 23
        let y3 = y3 + t0; // 24
        let t2 = point.y * point.z; // 25
        let t2 = t2 + t2; // 26
        let t0 = t2 * t3; // 27
        let x3 = x3 - t0; // 28
        let z3 = t2 * t1; // 29
        let z3 = z3 + z3; // 30
        let z3 = z3 + z3; // 31

        ProjectivePoint {
            x: x3,
            y: y3,
            z: z3,
        }
    }
}

/// The 𝒂-coefficient of the short Weierstrass equation is -3.
pub struct EquationAIsMinusThree {}

impl<C: PrimeCurveParams> PointArithmetic<C> for EquationAIsMinusThree {
    /// Implements complete addition for curves with `a = -3`
    ///
    /// Implements the complete addition formula from [Renes-Costello-Batina 2015]
    /// (Algorithm 4). The comments after each line indicate which algorithm steps
    /// are being performed.
    ///
    /// [Renes-Costello-Batina 2015]: https://eprint.iacr.org/2015/1060
    fn add(lhs: &ProjectivePoint<C>, rhs: &ProjectivePoint<C>) -> ProjectivePoint<C> {
        debug_assert_eq!(
            C::EQUATION_A,
            -C::FieldElement::from(3),
            "this implementation is only valid for C::EQUATION_A = -3"
        );

        let xx = lhs.x * rhs.x; // 1
        let yy = lhs.y * rhs.y; // 2
        let zz = lhs.z * rhs.z; // 3
        let xy_pairs = ((lhs.x + lhs.y) * (rhs.x + rhs.y)) - (xx + yy); // 4, 5, 6, 7, 8
        let yz_pairs = ((lhs.y + lhs.z) * (rhs.y + rhs.z)) - (yy + zz); // 9, 10, 11, 12, 13
        let xz_pairs = ((lhs.x + lhs.z) * (rhs.x + rhs.z)) - (xx + zz); // 14, 15, 16, 17, 18

        let bzz_part = xz_pairs - (C::EQUATION_B * zz); // 19, 20
        let bzz3_part = bzz_part.double() + bzz_part; // 21, 22
        let yy_m_bzz3 = yy - bzz3_part; // 23
        let yy_p_bzz3 = yy + bzz3_part; // 24

        let zz3 = zz.double() + zz; // 26, 27
        let bxz_part = (C::EQUATION_B * xz_pairs) - (zz3 + xx); // 25, 28, 29
        let bxz3_part = bxz_part.double() + bxz_part; // 30, 31
        let xx3_m_zz3 = xx.double() + xx - zz3; // 32, 33, 34

        ProjectivePoint {
            x: (yy_p_bzz3 * xy_pairs) - (yz_pairs * bxz3_part), // 35, 39, 40
            y: (yy_p_bzz3 * yy_m_bzz3) + (xx3_m_zz3 * bxz3_part), // 36, 37, 38
            z: (yy_m_bzz3 * yz_pairs) + (xy_pairs * xx3_m_zz3), // 41, 42, 43
        }
    }

    /// Implements complete mixed addition for curves with `a = -3`
    ///
    /// Implements the complete mixed addition formula from [Renes-Costello-Batina 2015]
    /// (Algorithm 5). The comments after each line indicate which algorithm
    /// steps are being performed.
    ///
    /// [Renes-Costello-Batina 2015]: https://eprint.iacr.org/2015/1060
    fn add_mixed(lhs: &ProjectivePoint<C>, rhs: &AffinePoint<C>) -> ProjectivePoint<C> {
        debug_assert_eq!(
            C::EQUATION_A,
            -C::FieldElement::from(3),
            "this implementation is only valid for C::EQUATION_A = -3"
        );

        let xx = lhs.x * rhs.x; // 1
        let yy = lhs.y * rhs.y; // 2
        let xy_pairs = ((lhs.x + lhs.y) * (rhs.x + rhs.y)) - (xx + yy); // 3, 4, 5, 6, 7
        let yz_pairs = (rhs.y * lhs.z) + lhs.y; // 8, 9 (t4)
        let xz_pairs = (rhs.x * lhs.z) + lhs.x; // 10, 11 (y3)

        let bz_part = xz_pairs - (C::EQUATION_B * lhs.z); // 12, 13
        let bz3_part = bz_part.double() + bz_part; // 14, 15
        let yy_m_bzz3 = yy - bz3_part; // 16
        let yy_p_bzz3 = yy + bz3_part; // 17

        let z3 = lhs.z.double() + lhs.z; // 19, 20
        let bxz_part = (C::EQUATION_B * xz_pairs) - (z3 + xx); // 18, 21, 22
        let bxz3_part = bxz_part.double() + bxz_part; // 23, 24
        let xx3_m_zz3 = xx.double() + xx - z3; // 25, 26, 27

        let mut ret = ProjectivePoint {
            x: (yy_p_bzz3 * xy_pairs) - (yz_pairs * bxz3_part), // 28, 32, 33
            y: (yy_p_bzz3 * yy_m_bzz3) + (xx3_m_zz3 * bxz3_part), // 29, 30, 31
            z: (yy_m_bzz3 * yz_pairs) + (xy_pairs * xx3_m_zz3), // 34, 35, 36
        };
        ret.conditional_assign(lhs, rhs.is_identity());
        ret
    }

    /// Implements point doubling for curves with `a = -3`
    ///
    /// Implements the exception-free point doubling formula from [Renes-Costello-Batina 2015]
    /// (Algorithm 6). The comments after each line indicate which algorithm
    /// steps are being performed.
    ///
    /// [Renes-Costello-Batina 2015]: https://eprint.iacr.org/2015/1060
    fn double(point: &ProjectivePoint<C>) -> ProjectivePoint<C> {
        debug_assert_eq!(
            C::EQUATION_A,
            -C::FieldElement::from(3),
            "this implementation is only valid for C::EQUATION_A = -3"
        );

        let xx = point.x.square(); // 1
        let yy = point.y.square(); // 2
        let zz = point.z.square(); // 3
        let xy2 = (point.x * point.y).double(); // 4, 5
        let xz2 = (point.x * point.z).double(); // 6, 7

        let bzz_part = (C::EQUATION_B * zz) - xz2; // 8, 9
        let bzz3_part = bzz_part.double() + bzz_part; // 10, 11
        let yy_m_bzz3 = yy - bzz3_part; // 12
        let yy_p_bzz3 = yy + bzz3_part; // 13
        let y_frag = yy_p_bzz3 * yy_m_bzz3; // 14
        let x_frag = yy_m_bzz3 * xy2; // 15

        let zz3 = zz.double() + zz; // 16, 17
        let bxz2_part = (C::EQUATION_B * xz2) - (zz3 + xx); // 18, 19, 20
        let bxz6_part = bxz2_part.double() + bxz2_part; // 21, 22
        let xx3_m_zz3 = xx.double() + xx - zz3; // 23, 24, 25

        let y = y_frag + (xx3_m_zz3 * bxz6_part); // 26, 27
        let yz2 = (point.y * point.z).double(); // 28, 29
        let x = x_frag - (bxz6_part * yz2); // 30, 31
        let z = (yz2 * yy).double().double(); // 32, 33, 34

        ProjectivePoint { x, y, z }
    }
}
