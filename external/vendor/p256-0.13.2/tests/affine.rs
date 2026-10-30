//! Affine arithmetic tests.

#![cfg(all(feature = "arithmetic"))]

use elliptic_curve::{
    group::{prime::PrimeCurveAffine, GroupEncoding},
    sec1::{FromEncodedPoint, ToCompactEncodedPoint, ToEncodedPoint},
};
use hex_literal::hex;
use p256::{AffinePoint, EncodedPoint};

const UNCOMPRESSED_BASEPOINT: &[u8] = &hex!(
    "04 6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
        4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5"
);

const COMPRESSED_BASEPOINT: &[u8] =
    &hex!("03 6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296");

// Tag compact with 05 as the first byte, to trigger tag based compaction
const COMPACT_BASEPOINT: &[u8] =
    &hex!("05 8e38fc4ffe677662dde8e1a63fbcd45959d2a4c3004d27e98c4fedf2d0c14c01");

// Tag uncompact basepoint with 04 as the first byte as it is uncompressed
const UNCOMPACT_BASEPOINT: &[u8] = &hex!(
    "04 8e38fc4ffe677662dde8e1a63fbcd45959d2a4c3004d27e98c4fedf2d0c14c0
        13ca9d8667de0c07aa71d98b3c8065d2e97ab7bb9cb8776bcc0577a7ac58acd4e"
);

#[test]
fn uncompressed_round_trip() {
    let pubkey = EncodedPoint::from_bytes(UNCOMPRESSED_BASEPOINT).unwrap();
    let point = AffinePoint::from_encoded_point(&pubkey).unwrap();
    assert_eq!(point, AffinePoint::generator());

    let res: EncodedPoint = point.into();
    assert_eq!(res, pubkey);
}

#[test]
fn compressed_round_trip() {
    let pubkey = EncodedPoint::from_bytes(COMPRESSED_BASEPOINT).unwrap();
    let point = AffinePoint::from_encoded_point(&pubkey).unwrap();
    assert_eq!(point, AffinePoint::generator());

    let res: EncodedPoint = point.to_encoded_point(true);
    assert_eq!(res, pubkey);
}

#[test]
fn uncompressed_to_compressed() {
    let encoded = EncodedPoint::from_bytes(UNCOMPRESSED_BASEPOINT).unwrap();

    let res = AffinePoint::from_encoded_point(&encoded)
        .unwrap()
        .to_encoded_point(true);

    assert_eq!(res.as_bytes(), COMPRESSED_BASEPOINT);
}

#[test]
fn compressed_to_uncompressed() {
    let encoded = EncodedPoint::from_bytes(COMPRESSED_BASEPOINT).unwrap();

    let res = AffinePoint::from_encoded_point(&encoded)
        .unwrap()
        .to_encoded_point(false);

    assert_eq!(res.as_bytes(), UNCOMPRESSED_BASEPOINT);
}

#[test]
fn affine_negation() {
    let basepoint = AffinePoint::generator();
    assert_eq!(-(-basepoint), basepoint);
}

#[test]
fn compact_round_trip() {
    let pubkey = EncodedPoint::from_bytes(COMPACT_BASEPOINT).unwrap();
    assert!(pubkey.is_compact());

    let point = AffinePoint::from_encoded_point(&pubkey).unwrap();
    let res = point.to_compact_encoded_point().unwrap();
    assert_eq!(res, pubkey)
}

#[test]
fn uncompact_to_compact() {
    let pubkey = EncodedPoint::from_bytes(UNCOMPACT_BASEPOINT).unwrap();
    assert_eq!(false, pubkey.is_compact());

    let point = AffinePoint::from_encoded_point(&pubkey).unwrap();
    let res = point.to_compact_encoded_point().unwrap();
    assert_eq!(res.as_bytes(), COMPACT_BASEPOINT)
}

#[test]
fn compact_to_uncompact() {
    let pubkey = EncodedPoint::from_bytes(COMPACT_BASEPOINT).unwrap();
    assert!(pubkey.is_compact());

    let point = AffinePoint::from_encoded_point(&pubkey).unwrap();
    // Do not do compact encoding as we want to keep uncompressed point
    let res = point.to_encoded_point(false);
    assert_eq!(res.as_bytes(), UNCOMPACT_BASEPOINT);
}

#[test]
fn identity_encoding() {
    // This is technically an invalid SEC1 encoding, but is preferable to panicking.
    assert_eq!([0; 33], AffinePoint::IDENTITY.to_bytes().as_slice());
    assert!(bool::from(
        AffinePoint::from_bytes(&AffinePoint::IDENTITY.to_bytes())
            .unwrap()
            .is_identity()
    ))
}

#[test]
fn noncompatible_is_none() {
    use elliptic_curve::generic_array::GenericArray;
    let noncompactable_secret = GenericArray::from([
        175, 232, 180, 255, 91, 106, 124, 191, 224, 31, 177, 208, 236, 127, 191, 169, 201, 217, 75,
        141, 184, 175, 120, 85, 171, 8, 54, 57, 33, 177, 83, 211,
    ]);
    let public_key = p256::SecretKey::from_bytes(&noncompactable_secret)
        .unwrap()
        .public_key();
    let is_compactable = public_key
        .as_affine()
        .to_compact_encoded_point()
        .is_some()
        .unwrap_u8();
    assert_eq!(is_compactable, 0);
}
