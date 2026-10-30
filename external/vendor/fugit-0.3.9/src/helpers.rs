/// Needed due to not being allowed to call const-fn in `PartialEq` fo some reasion
/// get the error:
///
/// ```console
/// error[E0401]: can't use generic parameters from outer function
///   --> src/main.rs:25:47
///    |
/// 21 | impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
///    |                                                                    ------- const parameter from outer function
/// ...
/// 25 |         const TEST: u32 = gcd_binary_u32(L_DENOM, R_DENOM);
///    |                                                   ^^^^^^^ use of generic parameter from outer function
///
/// For more information about this error, try `rustc --explain E0401`
/// ```
pub struct Helpers<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>;

impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
    Helpers<L_NOM, L_DENOM, R_NOM, R_DENOM>
{
    /// Helper constants generated at compile time
    pub const DIVISOR: u64 =
        gcd::binary_u64(L_DENOM as u64 * R_NOM as u64, R_DENOM as u64 * L_NOM as u64);

    /// Helper constants generated at compile time
    pub const DIVISOR_2: u64 =
        gcd::binary_u64(L_NOM as u64 * R_NOM as u64, R_DENOM as u64 * L_DENOM as u64);

    /// Helper constants generated at compile time for Durations
    pub const RD_TIMES_LN: u64 = (R_DENOM as u64 * L_NOM as u64) / Self::DIVISOR;

    /// Helper constants generated at compile time
    pub const LD_TIMES_RN: u64 = (L_DENOM as u64 * R_NOM as u64) / Self::DIVISOR;

    /// Helper constants generated at compile time for Rates
    pub const LN_TIMES_RN: u64 = (L_NOM as u64 * R_NOM as u64) / Self::DIVISOR_2;

    /// Helper constants generated at compile time for Rates
    pub const RD_TIMES_LD: u64 = (R_DENOM as u64 * L_DENOM as u64) / Self::DIVISOR_2;

    /// Helper constants generated at compile time for Rates
    pub const RATE_TO_DURATION_NUMERATOR: u64 = Self::RD_TIMES_LD / Self::LN_TIMES_RN;

    /// Helper constants generated at compile time
    pub const SAME_BASE: bool = Self::LD_TIMES_RN == Self::RD_TIMES_LN;
}

#[allow(dead_code)]
#[allow(path_statements)]
pub(crate) const fn greater_than_0<const N: u32>() {
    Assert::<N, 0>::GREATER;
}

#[allow(dead_code)]
/// Const assert hack
pub struct Assert<const L: u32, const R: u32>;

#[allow(dead_code)]
impl<const L: u32, const R: u32> Assert<L, R> {
    /// Const assert hack
    pub const GREATER_EQ: () = assert!(L >= R);

    /// Const assert hack
    pub const LESS_EQ: () = assert!(L <= R);

    /// Const assert hack
    pub const NOT_EQ: () = assert!(L != R);

    /// Const assert hack
    pub const EQ: () = assert!(L == R);

    /// Const assert hack
    pub const GREATER: () = assert!(L > R);

    /// Const assert hack
    pub const LESS: () = assert!(L < R);

    /// Const assert hack
    pub const POWER_OF_TWO: () = assert!(L.is_power_of_two());
}
