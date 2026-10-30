//! Common functionality shared by tests

/// Test vectors
#[derive(Debug)]
pub struct TestVector<K: 'static> {
    pub key: &'static K,
    pub nonce: &'static [u8; 12],
    pub aad: &'static [u8],
    pub plaintext: &'static [u8],
    pub ciphertext: &'static [u8],
    pub tag: &'static [u8; 16],
}

#[macro_export]
macro_rules! tests {
    ($aead:ty, $vectors:expr) => {
        #[test]
        fn encrypt() {
            for vector in $vectors {
                let key = GenericArray::from_slice(vector.key);
                let nonce = GenericArray::from_slice(vector.nonce);
                let payload = Payload {
                    msg: vector.plaintext,
                    aad: vector.aad,
                };

                let cipher = <$aead>::new(key);
                let ciphertext = cipher.encrypt(nonce, payload).unwrap();
                let (ct, tag) = ciphertext.split_at(ciphertext.len() - 16);
                assert_eq!(vector.ciphertext, ct);
                assert_eq!(vector.tag, tag);
            }
        }

        #[test]
        fn decrypt() {
            for vector in $vectors {
                let key = GenericArray::from_slice(vector.key);
                let nonce = GenericArray::from_slice(vector.nonce);
                let mut ciphertext = Vec::from(vector.ciphertext);
                ciphertext.extend_from_slice(vector.tag);

                let payload = Payload {
                    msg: &ciphertext,
                    aad: vector.aad,
                };

                let cipher = <$aead>::new(key);
                let plaintext = cipher.decrypt(nonce, payload).unwrap();

                assert_eq!(vector.plaintext, plaintext.as_slice());
            }
        }

        #[test]
        fn decrypt_modified() {
            let vector = &$vectors[0];
            let key = GenericArray::from_slice(vector.key);
            let nonce = GenericArray::from_slice(vector.nonce);

            let mut ciphertext = Vec::from(vector.ciphertext);
            ciphertext.extend_from_slice(vector.tag);

            // Tweak the first byte
            ciphertext[0] ^= 0xaa;

            let payload = Payload {
                msg: &ciphertext,
                aad: vector.aad,
            };

            let cipher = <$aead>::new(key);
            assert!(cipher.decrypt(nonce, payload).is_err());
        }

        #[test]
        fn decrypt_in_place_detached_modified() {
            let vector = &$vectors.iter().last().unwrap();
            let key = GenericArray::from_slice(vector.key);
            let nonce = GenericArray::from_slice(vector.nonce);

            let mut buffer = Vec::from(vector.ciphertext);
            assert!(!buffer.is_empty());

            // Tweak the first byte
            let mut tag = GenericArray::clone_from_slice(vector.tag);
            tag[0] ^= 0xaa;

            let cipher = <$aead>::new(key);
            assert!(cipher
                .decrypt_in_place_detached(nonce, &[], &mut buffer, &tag)
                .is_err());

            assert_eq!(vector.ciphertext, buffer);
        }
    };
}
