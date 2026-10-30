//! Tests for AES-GCM when used with non-96-bit nonces.
//!
//! Vectors taken from NIST CAVS vectors' `gcmEncryptExtIV128.rsp` file:
//! <https://csrc.nist.gov/Projects/cryptographic-algorithm-validation-program/CAVP-TESTING-BLOCK-CIPHER-MODES>

use aead::{
    generic_array::{typenum, GenericArray},
    Aead, KeyInit,
};
use aes::Aes128;
use aes_gcm::AesGcm;
use hex_literal::hex;

/// Based on the following `gcmEncryptExtIV128.rsp` test vector:
///
/// [Keylen = 128]
/// [IVlen = 8]
/// [PTlen = 128]
/// [AADlen = 0]
/// [Taglen = 128]
///
/// Count = 0
mod ivlen8 {
    use super::*;

    type Aes128GcmWith8BitNonce = AesGcm<Aes128, typenum::U1>;

    #[test]
    fn encrypt() {
        let key = hex!("15b2d414826453f9e1c7dd0b69d8d1eb");
        let nonce = hex!("b6");
        let plaintext = hex!("8cfa255530c6fbc19d51bd4aeb39c91b");

        let ciphertext = Aes128GcmWith8BitNonce::new(&key.into())
            .encrypt(GenericArray::from_slice(&nonce), &plaintext[..])
            .unwrap();

        let (ct, tag) = ciphertext.split_at(ciphertext.len() - 16);
        assert_eq!(hex!("4822cb98bd5f5d921ee19285c9032375"), ct);
        assert_eq!(hex!("8a40670ebac98cf4e9cc1bf8f803167d"), tag);
    }
}

/// Based on the following `gcmEncryptExtIV128.rsp` test vector:
///
/// [Keylen = 128]
/// [IVlen = 1024]
/// [PTlen = 128]
/// [AADlen = 0]
/// [Taglen = 128]
///
/// Count = 0
mod ivlen1024 {
    use super::*;

    type Aes128GcmWith1024BitNonce = AesGcm<Aes128, typenum::U128>;

    #[test]
    fn encrypt() {
        let key = hex!("71eebc49c8fb773b2224eaff3ad68714");
        let nonce = hex!(
            "07e961e67784011f72faafd95b0eb64089c8de15ad685ec57e63d56e679d3e20
             2b18b75fcbbec3185ffc41653bc2ac4ae6ae8be8c85636f353a9d19a86100d0b
             d035cc6bdefcab4318ac7b1a08b819427ad8f6abc782466c6ebd4d6a0dd76e78
             389b0a2a66506bb85f038ffc1da220c24f3817c7b2d02c5e8fc5e7e3be5074bc"
        );
        let plaintext = hex!("705da82292143d2c949dc4ba014f6396");

        let ciphertext = Aes128GcmWith1024BitNonce::new(&key.into())
            .encrypt(GenericArray::from_slice(&nonce), &plaintext[..])
            .unwrap();

        let (ct, tag) = ciphertext.split_at(ciphertext.len() - 16);
        assert_eq!(hex!("032363cf0828a03553478bec0f51f372"), ct);
        assert_eq!(hex!("c681b2c568feaa21900bc44b86aeb946"), tag);
    }
}
