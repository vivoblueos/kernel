//! Scalar arithmetic tests.

#![cfg(feature = "arithmetic")]

use elliptic_curve::ops::{Invert, Reduce};
use p256::{Scalar, U256};
use proptest::prelude::*;

prop_compose! {
    fn scalar()(bytes in any::<[u8; 32]>()) -> Scalar {
        <Scalar as Reduce<U256>>::reduce_bytes(&bytes.into())
    }
}

proptest! {
    #[test]
    fn invert_and_invert_vartime_are_equivalent(w in scalar()) {
        let inv: Option<Scalar> = w.invert().into();
        let inv_vartime: Option<Scalar> = w.invert_vartime().into();
        prop_assert_eq!(inv, inv_vartime);
    }
}
