use ghash::{
    universal_hash::{KeyInit, UniversalHash},
    GHash,
};
use hex_literal::hex;

//
// Test vectors for GHASH from RFC 8452 Appendix A
// <https://tools.ietf.org/html/rfc8452#appendix-A>
//

const H: [u8; 16] = hex!("25629347589242761d31f826ba4b757b");
const X_1: [u8; 16] = hex!("4f4f95668c83dfb6401762bb2d01a262");
const X_2: [u8; 16] = hex!("d1a24ddd2721d006bbe45f20d3c9f362");

/// GHASH(H, X_1, X_2)
const GHASH_RESULT: [u8; 16] = hex!("bd9b3997046731fb96251b91f9c99d7a");

#[test]
fn ghash_test_vector() {
    let mut ghash = GHash::new(&H.into());
    ghash.update(&[X_1.into(), X_2.into()]);

    let result = ghash.finalize();
    assert_eq!(&GHASH_RESULT[..], result.as_slice());
}
