#![no_std]
use core::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};

pub trait Gcd {
    /// Determine [greatest common divisor](https://en.wikipedia.org/wiki/Greatest_common_divisor)
    /// using [`gcd_binary`].
    ///
    /// [`gcd_binary`]: #method.gcd_binary
    ///
    /// # Examples
    ///
    /// ```
    /// use gcd::Gcd;
    ///
    /// assert_eq!(0, 0u8.gcd(0));
    /// assert_eq!(10, 10u8.gcd(0));
    /// assert_eq!(10, 0u8.gcd(10));
    /// assert_eq!(10, 10u8.gcd(20));
    /// assert_eq!(44, 2024u32.gcd(748));
    /// ```
    fn gcd(self, other: Self) -> Self;

    /// Determine [greatest common divisor](https://en.wikipedia.org/wiki/Greatest_common_divisor)
    /// using the [Binary GCD algorithm](https://en.wikipedia.org/wiki/Binary_GCD_algorithm).
    fn gcd_binary(self, other: Self) -> Self;

    /// Determine [greatest common divisor](https://en.wikipedia.org/wiki/Greatest_common_divisor)
    /// using the [Euclidean algorithm](https://en.wikipedia.org/wiki/Euclidean_algorithm).
    fn gcd_euclid(self, other: Self) -> Self;
}

macro_rules! gcd_impl {
    ($(($T:ty) $binary:ident $euclid:ident),*) => {$(
        #[doc = concat!("Const binary GCD implementation for `", stringify!($T), "`.")]
        pub const fn $binary(mut u: $T, mut v: $T) -> $T
        {
            if u == 0 { return v; }
            if v == 0 { return u; }

            let shift = (u | v).trailing_zeros();
            u >>= shift;
            v >>= shift;
            u >>= u.trailing_zeros();

            loop {
                v >>= v.trailing_zeros();

                #[allow(clippy::manual_swap)]
                if u > v {
                    // mem::swap(&mut u, &mut v);
                    let temp = u;
                    u = v;
                    v = temp;
                }

                v -= u; // here v >= u

                if v == 0 { break; }
            }

            u << shift
        }

        #[doc = concat!("Const euclid GCD implementation for `", stringify!($T), "`.")]
        pub const fn $euclid(a: $T, b: $T) -> $T
        {
            // variable names based off euclidean division equation: a = b · q + r
            let (mut a, mut b) = if a > b {
                (a, b)
            } else {
                (b, a)
            };

            #[allow(clippy::manual_swap)]
            while b != 0 {
                // mem::swap(&mut a, &mut b);
                let temp = a;
                a = b;
                b = temp;

                b %= a;
            }

            a
        }

        impl Gcd for $T {
            #[inline]
            fn gcd(self, other: $T) -> $T {
                self.gcd_binary(other)
            }

            #[inline]
            fn gcd_binary(self, v: $T) -> $T {
                $binary(self, v)
            }

            #[inline]
            fn gcd_euclid(self, other: $T) -> $T {
                $euclid(self, other)
            }
        }
    )*};
}

gcd_impl! {
    (u8) binary_u8 euclid_u8,
    (u16) binary_u16 euclid_u16,
    (u32) binary_u32 euclid_u32,
    (u64) binary_u64 euclid_u64,
    (u128) binary_u128 euclid_u128,
    (usize) binary_usize euclid_usize
}

macro_rules! gcd_impl_nonzero {
    ($(($T:ty) $binary_nonzero:ident/$binary:ident $euclid_nonzero:ident/$euclid:ident),*) => {$(
        #[doc = concat!("Const binary GCD implementation for `", stringify!($T), "`.")]
        pub const fn $binary_nonzero(u: $T, v: $T) -> $T
        {
            match <$T>::new($binary(u.get(), v.get())) {
                Some(x) => x,
                None => unreachable!(),
            }
        }

        #[doc = concat!("Const euclid GCD implementation for `", stringify!($T), "`.")]
        pub const fn $euclid_nonzero(a: $T, b: $T) -> $T
        {
            match <$T>::new($euclid(a.get(), b.get())) {
                Some(x) => x,
                None => unreachable!(),
            }
        }

        impl Gcd for $T {
            #[inline]
            fn gcd(self, other: $T) -> $T {
                self.gcd_binary(other)
            }

            #[inline]
            fn gcd_binary(self, v: $T) -> $T {
                $binary_nonzero(self, v)
            }

            #[inline]
            fn gcd_euclid(self, other: $T) -> $T {
                $euclid_nonzero(self, other)
            }
        }
    )*}
}

gcd_impl_nonzero! {
    (NonZeroU8) binary_nonzero_u8/binary_u8 euclid_nonzero_u8/euclid_u8,
    (NonZeroU16) binary_nonzero_u16/binary_u16 euclid_nonzero_u16/euclid_u16,
    (NonZeroU32) binary_nonzero_u32/binary_u32 euclid_nonzero_u32/euclid_u32,
    (NonZeroU64) binary_nonzero_u64/binary_u64 euclid_nonzero_u64/euclid_u64,
    (NonZeroU128) binary_nonzero_u128/binary_u128 euclid_nonzero_u128/euclid_u128,
    (NonZeroUsize) binary_nonzero_usize/binary_usize euclid_nonzero_usize/euclid_usize
}

#[cfg(test)]
mod test {
    use super::*;
    use core::fmt::Debug;

    const U8_GCD_A: [u8; 5] = [140, 1, 140, 33, 225];
    const U8_GCD_B: [u8; 5] = [136, 123, 203, 252, 153];
    const U8_GCD_R: [u8; 5] = [4, 1, 7, 3, 9];

    const U16_GCD_A: [u16; 5] = [53144, 44062, 65054, 60568, 11932];
    const U16_GCD_B: [u16; 5] = [41105, 5088, 35332, 19184, 54004];
    const U16_GCD_R: [u16; 5] = [1, 2, 22, 8, 4];

    const U32_GCD_A: [u32; 5] = [3392079986, 273672341, 1353048788, 1491301950, 3569727686];
    const U32_GCD_B: [u32; 5] = [2080089626, 3912533700, 1969135932, 1356732645, 58056677];
    const U32_GCD_R: [u32; 5] = [2, 1, 4, 15, 7];

    const U64_GCD_A: [u64; 5] = [
        190266297176832000,
        2040134905096275968,
        16611311494648745984,
        14863931409971066880,
        11777713923171739648,
    ];
    const U64_GCD_B: [u64; 5] = [
        10430732356495263744,
        5701159354248194048,
        7514969329383038976,
        7911906750992527360,
        1994469765110767616,
    ];
    const U64_GCD_R: [u64; 5] = [6144, 2048, 4096, 10240, 14336];

    const U128_GCD_A: [u128; 5] = [
        183222947567111613556380400704880115712,
        115621006611964852903362423926779019264,
        50724538437787115589243518273596686336,
        18298803717624646317403958239767298048,
        196929845599653749349770751890136498176,
    ];
    const U128_GCD_B: [u128; 5] = [
        283620717889381409474181015983148236800,
        152390035351551984363917166384150216704,
        74996138554240857099554660445327458304,
        245604784002268488089190010796573196288,
        194671916188106984823441978656659865600,
    ];
    const U128_GCD_R: [u128; 5] = [
        37778931862957161709568,
        75557863725914323419136,
        113336795588871485128704,
        151115727451828646838272,
        302231454903657293676544,
    ];

    const USIZE_GCD_A: [usize; 5] = [335286345, 3125888386, 3550412466, 924335944, 2870209473];
    const USIZE_GCD_B: [usize; 5] = [1843742025, 2080426243, 16052620, 1587387560, 24708111];
    const USIZE_GCD_R: [usize; 5] = [15, 1, 2, 8, 3];

    #[test]
    fn test_gcd_basic() {
        // some base cases
        assert_eq!(0, 0u8.gcd(0));
        assert_eq!(10, 10u8.gcd(0));
        assert_eq!(10, 0u8.gcd(10));
    }

    fn verify_gcd<T>(a: T, b: T, r: T)
    where
        T: Gcd + Copy + PartialEq + Debug,
    {
        let gcd = a.gcd(b);
        let egcd = a.gcd_euclid(b);
        let bgcd = a.gcd_binary(b);
        assert_eq!(r, gcd, "{:?}.gcd({:?})", a, b);
        assert_eq!(r, egcd, "{:?}.gcd_euclid({:?})", a, b);
        assert_eq!(r, bgcd, "{:?}.gcd_binary({:?})", a, b);
    }

    fn test_gcd_ty<T, NZ, const N: usize>(
        new: impl Fn(T) -> Option<NZ>,
        zero: T,
        a: &[T; N],
        b: &[T; N],
        r: &[T; N],
    ) where
        T: Gcd + Copy + PartialEq + Debug,
        NZ: Gcd + Copy + PartialEq + Debug,
    {
        for ind in 0..N {
            let a = new(a[ind]).unwrap();
            let b = new(b[ind]).unwrap();
            let r = new(r[ind]).unwrap();
            verify_gcd(a, b, r);
        }

        let a = a[0];
        verify_gcd(zero, a, a);
        verify_gcd(a, zero, a);
    }

    #[test]
    fn test_gcd() {
        test_gcd_ty(NonZeroU8::new, 0, &U8_GCD_A, &U8_GCD_B, &U8_GCD_R);
        test_gcd_ty(NonZeroU16::new, 0, &U16_GCD_A, &U16_GCD_B, &U16_GCD_R);
        test_gcd_ty(NonZeroU32::new, 0, &U32_GCD_A, &U32_GCD_B, &U32_GCD_R);
        test_gcd_ty(NonZeroU64::new, 0, &U64_GCD_A, &U64_GCD_B, &U64_GCD_R);
        test_gcd_ty(NonZeroU128::new, 0, &U128_GCD_A, &U128_GCD_B, &U128_GCD_R);
        test_gcd_ty(
            NonZeroUsize::new,
            0,
            &USIZE_GCD_A,
            &USIZE_GCD_B,
            &USIZE_GCD_R,
        );
    }

    const U32_GCD_R_0: u32 = binary_u32(U32_GCD_A[0], U32_GCD_B[0]);
    const U32_GCD_R_1: u32 = euclid_u32(U32_GCD_A[1], U32_GCD_B[1]);
    const U32_GCD_R_2: u32 = binary_u32(U32_GCD_A[2], U32_GCD_B[2]);
    const U32_GCD_R_3: u32 = euclid_u32(U32_GCD_A[3], U32_GCD_B[3]);
    const U32_GCD_R_4: u32 = binary_u32(U32_GCD_A[4], U32_GCD_B[4]);

    #[test]
    fn test_const_gcd() {
        assert_eq!(U32_GCD_R[0], U32_GCD_R_0);
        assert_eq!(U32_GCD_R[1], U32_GCD_R_1);
        assert_eq!(U32_GCD_R[2], U32_GCD_R_2);
        assert_eq!(U32_GCD_R[3], U32_GCD_R_3);
        assert_eq!(U32_GCD_R[4], U32_GCD_R_4);
    }
}
