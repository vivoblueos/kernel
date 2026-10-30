//! Elliptic Curve Digital Signature Algorithm (ECDSA)
//!
//! This module contains support for computing and verifying ECDSA signatures.
//! To use it, you will need to enable one of the two following Cargo features:
//!
//! - `ecdsa-core`: provides only the [`Signature`] type (which represents an
//!   ECDSA/P-256 signature). Does not require the `arithmetic` feature.
//!   This is useful for 3rd-party crates which wish to use the `Signature`
//!   type for interoperability purposes (particularly in conjunction with the
//!   [`signature::Signer`] trait. Example use cases for this include other
//!   software implementations of ECDSA/P-256 and wrappers for cloud KMS
//!   services or hardware devices (HSM or crypto hardware wallet).
//! - `ecdsa`: provides `ecdsa-core` features plus the [`SigningKey`] and
//!   [`VerifyingKey`] types which natively implement ECDSA/P-256 signing and
//!   verification.
//!
//! ## Signing/Verification Example
//!
//! This example requires the `ecdsa` Cargo feature is enabled:
//!
//! ```
//! # #[cfg(feature = "ecdsa")]
//! # {
//! use p256::{
//!     ecdsa::{SigningKey, Signature, signature::Signer},
//! };
//! use rand_core::OsRng; // requires 'getrandom' feature
//!
//! // Signing
//! let signing_key = SigningKey::random(&mut OsRng); // Serialize with `::to_bytes()`
//! let message = b"ECDSA proves knowledge of a secret number in the context of a single message";
//! let signature: Signature = signing_key.sign(message);
//!
//! // Verification
//! use p256::ecdsa::{VerifyingKey, signature::Verifier};
//!
//! let verifying_key = VerifyingKey::from(&signing_key); // Serialize with `::to_encoded_point()`
//! assert!(verifying_key.verify(message, &signature).is_ok());
//! # }
//! ```

pub use ecdsa_core::signature::{self, Error};

use super::NistP256;

#[cfg(feature = "ecdsa")]
use {
    crate::{AffinePoint, Scalar},
    ecdsa_core::hazmat::{SignPrimitive, VerifyPrimitive},
};

/// ECDSA/P-256 signature (fixed-size)
pub type Signature = ecdsa_core::Signature<NistP256>;

/// ECDSA/P-256 signature (ASN.1 DER encoded)
pub type DerSignature = ecdsa_core::der::Signature<NistP256>;

/// ECDSA/P-256 signing key
#[cfg(feature = "ecdsa")]
pub type SigningKey = ecdsa_core::SigningKey<NistP256>;

/// ECDSA/P-256 verification key (i.e. public key)
#[cfg(feature = "ecdsa")]
pub type VerifyingKey = ecdsa_core::VerifyingKey<NistP256>;

#[cfg(feature = "sha256")]
impl ecdsa_core::hazmat::DigestPrimitive for NistP256 {
    type Digest = sha2::Sha256;
}

#[cfg(feature = "ecdsa")]
impl SignPrimitive<NistP256> for Scalar {}

#[cfg(feature = "ecdsa")]
impl VerifyPrimitive<NistP256> for AffinePoint {}

#[cfg(all(test, feature = "ecdsa"))]
mod tests {
    use crate::{
        ecdsa::{
            signature::hazmat::{PrehashSigner, PrehashVerifier},
            signature::Signer,
            Signature, SigningKey, VerifyingKey,
        },
        test_vectors::ecdsa::ECDSA_TEST_VECTORS,
        AffinePoint, BlindedScalar, EncodedPoint, Scalar,
    };
    use ecdsa_core::hazmat::SignPrimitive;
    use elliptic_curve::{
        generic_array::GenericArray, group::ff::PrimeField, rand_core::OsRng,
        sec1::FromEncodedPoint,
    };
    use hex_literal::hex;
    use sha2::Digest;

    // Test vector from RFC 6979 Appendix 2.5 (NIST P-256 + SHA-256)
    // <https://tools.ietf.org/html/rfc6979#appendix-A.2.5>
    #[test]
    fn rfc6979() {
        let x = hex!("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721");
        let signer = SigningKey::from_bytes(&x.into()).unwrap();
        let signature: Signature = signer.sign(b"sample");
        assert_eq!(
            signature.to_bytes().as_slice(),
            &hex!(
                "efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716
                 f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8"
            )
        );
        let signature: Signature = signer.sign(b"test");
        assert_eq!(
            signature.to_bytes().as_slice(),
            &hex!(
                "f1abb023518351cd71d881567b1ea663ed3efcf6c5132b354f28d3b0b7d38367
                 019f4113742a2b14bd25926b49c649155f267e60d3814b4c0cc84250e46f0083"
            )
        );
    }

    // Test signing with PrehashSigner using SHA-384 which output is larger than P-256 field size.
    #[test]
    fn prehash_signer_signing_with_sha384() {
        let x = hex!("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721");
        let signer = SigningKey::from_bytes(&x.into()).unwrap();
        let digest = sha2::Sha384::digest(b"test");
        let signature: Signature = signer.sign_prehash(&digest).unwrap();
        assert_eq!(
            signature.to_bytes().as_slice(),
            &hex!(
                "ebde85f1539af67e70dd7a8a6afeeb332aa7f08f01ebb6ab6e04e2a62d2fef75
                 871af45800daddf55619b005a601a7a84f544260f1d2625b2ef5aa7a4f4dd76f"
            )
        );
    }

    // Test verifying with PrehashVerifier using SHA-256 which output is larger than P-256 field size.
    #[test]
    fn prehash_signer_verification_with_sha384() {
        // The following test vector adapted from the FIPS 186-4 ECDSA test vectors
        // (P-256, SHA-384, from `SigGen.txt` in `186-4ecdsatestvectors.zip`)
        // <https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/digital-signatures>
        let verifier = VerifyingKey::from_affine(
            AffinePoint::from_encoded_point(&EncodedPoint::from_affine_coordinates(
                GenericArray::from_slice(&hex!(
                    "e0e7b99bc62d8dd67883e39ed9fa0657789c5ff556cc1fd8dd1e2a55e9e3f243"
                )),
                GenericArray::from_slice(&hex!(
                    "63fbfd0232b95578075c903a4dbf85ad58f8350516e1ec89b0ee1f5e1362da69"
                )),
                false,
            ))
            .unwrap(),
        )
        .unwrap();
        let signature = Signature::from_scalars(
            GenericArray::clone_from_slice(&hex!(
                "f5087878e212b703578f5c66f434883f3ef414dc23e2e8d8ab6a8d159ed5ad83"
            )),
            GenericArray::clone_from_slice(&hex!(
                "306b4c6c20213707982dffbb30fba99b96e792163dd59dbe606e734328dd7c8a"
            )),
        )
        .unwrap();
        let result = verifier.verify_prehash(
            &hex!("d9c83b92fa0979f4a5ddbd8dd22ab9377801c3c31bf50f932ace0d2146e2574da0d5552dbed4b18836280e9f94558ea6"),
            &signature,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn scalar_blinding() {
        let vector = &ECDSA_TEST_VECTORS[0];
        let d = Scalar::from_repr(GenericArray::clone_from_slice(vector.d)).unwrap();
        let k = Scalar::from_repr(GenericArray::clone_from_slice(vector.k)).unwrap();
        let k_blinded = BlindedScalar::new(k, &mut OsRng);
        let z = GenericArray::clone_from_slice(vector.m);
        let sig = d.try_sign_prehashed(k_blinded, &z).unwrap().0;

        assert_eq!(vector.r, sig.r().to_bytes().as_slice());
        assert_eq!(vector.s, sig.s().to_bytes().as_slice());
    }

    mod sign {
        use crate::{test_vectors::ecdsa::ECDSA_TEST_VECTORS, NistP256};
        ecdsa_core::new_signing_test!(NistP256, ECDSA_TEST_VECTORS);
    }

    mod verify {
        use crate::{test_vectors::ecdsa::ECDSA_TEST_VECTORS, NistP256};
        ecdsa_core::new_verification_test!(NistP256, ECDSA_TEST_VECTORS);
    }

    mod wycheproof {
        use crate::NistP256;
        ecdsa_core::new_wycheproof_test!(wycheproof, "wycheproof", NistP256);
    }
}
