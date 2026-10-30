#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![doc = include_str!("../README.md")]
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/RustCrypto/meta/master/logo.svg",
    html_favicon_url = "https://raw.githubusercontent.com/RustCrypto/meta/master/logo.svg"
)]
#![deny(unsafe_code)]
#![warn(missing_docs, rust_2018_idioms)]

//! # Usage
//!
//! Simple usage (allocating, no associated data):
//!
//! ```
//! use aes_gcm::{
//!     aead::{Aead, AeadCore, KeyInit, OsRng},
//!     Aes256Gcm, Nonce, Key // Or `Aes128Gcm`
//! };
//!
//! # fn gen_key() -> Result<(), core::array::TryFromSliceError> {
//! // The encryption key can be generated randomly:
//! # #[cfg(all(feature = "getrandom", feature = "std"))] {
//! let key = Aes256Gcm::generate_key(OsRng);
//! # }
//!
//! // Transformed from a byte array:
//! let key: &[u8; 32] = &[42; 32];
//! let key: &Key<Aes256Gcm> = key.into();
//!
//! // Note that you can get byte array from slice using the `TryInto` trait:
//! let key: &[u8] = &[42; 32];
//! let key: [u8; 32] = key.try_into()?;
//! # Ok(()) }
//!
//! # fn main() -> Result<(), aes_gcm::Error> {
//! // Alternatively, the key can be transformed directly from a byte slice
//! // (panicks on length mismatch):
//! # let key: &[u8] = &[42; 32];
//! let key = Key::<Aes256Gcm>::from_slice(key);
//!
//! let cipher = Aes256Gcm::new(&key);
//! let nonce = Aes256Gcm::generate_nonce(&mut OsRng); // 96-bits; unique per message
//! let ciphertext = cipher.encrypt(&nonce, b"plaintext message".as_ref())?;
//! let plaintext = cipher.decrypt(&nonce, ciphertext.as_ref())?;
//! assert_eq!(&plaintext, b"plaintext message");
//! # Ok(())
//! # }
//! ```
//!
//! ## In-place Usage (eliminates `alloc` requirement)
//!
//! This crate has an optional `alloc` feature which can be disabled in e.g.
//! microcontroller environments that don't have a heap.
//!
//! The [`AeadInPlace::encrypt_in_place`] and [`AeadInPlace::decrypt_in_place`]
//! methods accept any type that impls the [`aead::Buffer`] trait which
//! contains the plaintext for encryption or ciphertext for decryption.
//!
//! Note that if you enable the `heapless` feature of this crate,
//! you will receive an impl of [`aead::Buffer`] for `heapless::Vec`
//! (re-exported from the [`aead`] crate as [`aead::heapless::Vec`]),
//! which can then be passed as the `buffer` parameter to the in-place encrypt
//! and decrypt methods:
//!
#![cfg_attr(
    all(feature = "getrandom", feature = "heapless", feature = "std"),
    doc = "```"
)]
#![cfg_attr(
    not(all(feature = "getrandom", feature = "heapless", feature = "std")),
    doc = "```ignore"
)]
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use aes_gcm::{
//!     aead::{AeadCore, AeadInPlace, KeyInit, OsRng, heapless::Vec},
//!     Aes256Gcm, Nonce, // Or `Aes128Gcm`
//! };
//!
//! let key = Aes256Gcm::generate_key(&mut OsRng);
//! let cipher = Aes256Gcm::new(&key);
//! let nonce = Aes256Gcm::generate_nonce(&mut OsRng); // 96-bits; unique per message
//!
//! let mut buffer: Vec<u8, 128> = Vec::new(); // Note: buffer needs 16-bytes overhead for auth tag
//! buffer.extend_from_slice(b"plaintext message");
//!
//! // Encrypt `buffer` in-place, replacing the plaintext contents with ciphertext
//! cipher.encrypt_in_place(&nonce, b"", &mut buffer)?;
//!
//! // `buffer` now contains the message ciphertext
//! assert_ne!(&buffer, b"plaintext message");
//!
//! // Decrypt `buffer` in-place, replacing its ciphertext context with the original plaintext
//! cipher.decrypt_in_place(&nonce, b"", &mut buffer)?;
//! assert_eq!(&buffer, b"plaintext message");
//! # Ok(())
//! # }
//! ```
//!
//! Similarly, enabling the `arrayvec` feature of this crate will provide an impl of
//! [`aead::Buffer`] for `arrayvec::ArrayVec` (re-exported from the [`aead`] crate as
//! [`aead::arrayvec::ArrayVec`]).

pub use aead::{self, AeadCore, AeadInPlace, Error, Key, KeyInit, KeySizeUser};

#[cfg(feature = "aes")]
pub use aes;

use cipher::{
    consts::{U0, U16},
    generic_array::{ArrayLength, GenericArray},
    BlockCipher, BlockEncrypt, BlockSizeUser, InnerIvInit, StreamCipherCore,
};
use core::marker::PhantomData;
use ghash::{universal_hash::UniversalHash, GHash};

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

#[cfg(feature = "aes")]
use aes::{cipher::consts::U12, Aes128, Aes256};

/// Maximum length of associated data.
pub const A_MAX: u64 = 1 << 36;

/// Maximum length of plaintext.
pub const P_MAX: u64 = 1 << 36;

/// Maximum length of ciphertext.
pub const C_MAX: u64 = (1 << 36) + 16;

/// AES-GCM nonces.
pub type Nonce<NonceSize> = GenericArray<u8, NonceSize>;

/// AES-GCM tags.
pub type Tag<TagSize = U16> = GenericArray<u8, TagSize>;

/// Trait implemented for valid tag sizes, i.e.
/// [`U12`][consts::U12], [`U13`][consts::U13], [`U14`][consts::U14],
/// [`U15`][consts::U15] and [`U16`][consts::U16].
pub trait TagSize: private::SealedTagSize {}

impl<T: private::SealedTagSize> TagSize for T {}

mod private {
    use aead::generic_array::ArrayLength;
    use cipher::{consts, Unsigned};

    // Sealed traits stop other crates from implementing any traits that use it.
    pub trait SealedTagSize: ArrayLength<u8> + Unsigned {}

    impl SealedTagSize for consts::U12 {}
    impl SealedTagSize for consts::U13 {}
    impl SealedTagSize for consts::U14 {}
    impl SealedTagSize for consts::U15 {}
    impl SealedTagSize for consts::U16 {}
}

/// AES-GCM with a 128-bit key and 96-bit nonce.
#[cfg(feature = "aes")]
#[cfg_attr(docsrs, doc(cfg(feature = "aes")))]
pub type Aes128Gcm = AesGcm<Aes128, U12>;

/// AES-GCM with a 256-bit key and 96-bit nonce.
#[cfg(feature = "aes")]
#[cfg_attr(docsrs, doc(cfg(feature = "aes")))]
pub type Aes256Gcm = AesGcm<Aes256, U12>;

/// AES block.
type Block = GenericArray<u8, U16>;

/// Counter mode with a 32-bit big endian counter.
type Ctr32BE<Aes> = ctr::CtrCore<Aes, ctr::flavors::Ctr32BE>;

/// AES-GCM: generic over an underlying AES implementation and nonce size.
///
/// This type is generic to support substituting alternative AES implementations
/// (e.g. embedded hardware implementations)
///
/// It is NOT intended to be instantiated with any block cipher besides AES!
/// Doing so runs the risk of unintended cryptographic properties!
///
/// The `NonceSize` generic parameter can be used to instantiate AES-GCM with other
/// nonce sizes, however it's recommended to use it with `typenum::U12`,
/// the default of 96-bits.
///
/// The `TagSize` generic parameter can be used to instantiate AES-GCM with other
/// authorization tag sizes, however it's recommended to use it with `typenum::U16`,
/// the default of 128-bits.
///
/// If in doubt, use the built-in [`Aes128Gcm`] and [`Aes256Gcm`] type aliases.
#[derive(Clone)]
pub struct AesGcm<Aes, NonceSize, TagSize = U16>
where
    TagSize: self::TagSize,
{
    /// Encryption cipher.
    cipher: Aes,

    /// GHASH authenticator.
    ghash: GHash,

    /// Length of the nonce.
    nonce_size: PhantomData<NonceSize>,

    /// Length of the tag.
    tag_size: PhantomData<TagSize>,
}

impl<Aes, NonceSize, TagSize> KeySizeUser for AesGcm<Aes, NonceSize, TagSize>
where
    Aes: KeySizeUser,
    TagSize: self::TagSize,
{
    type KeySize = Aes::KeySize;
}

impl<Aes, NonceSize, TagSize> KeyInit for AesGcm<Aes, NonceSize, TagSize>
where
    Aes: BlockSizeUser<BlockSize = U16> + BlockEncrypt + KeyInit,
    TagSize: self::TagSize,
{
    fn new(key: &Key<Self>) -> Self {
        Aes::new(key).into()
    }
}

impl<Aes, NonceSize, TagSize> From<Aes> for AesGcm<Aes, NonceSize, TagSize>
where
    Aes: BlockSizeUser<BlockSize = U16> + BlockEncrypt,
    TagSize: self::TagSize,
{
    fn from(cipher: Aes) -> Self {
        let mut ghash_key = ghash::Key::default();
        cipher.encrypt_block(&mut ghash_key);

        let ghash = GHash::new(&ghash_key);

        #[cfg(feature = "zeroize")]
        ghash_key.zeroize();

        Self {
            cipher,
            ghash,
            nonce_size: PhantomData,
            tag_size: PhantomData,
        }
    }
}

impl<Aes, NonceSize, TagSize> AeadCore for AesGcm<Aes, NonceSize, TagSize>
where
    NonceSize: ArrayLength<u8>,
    TagSize: self::TagSize,
{
    type NonceSize = NonceSize;
    type TagSize = TagSize;
    type CiphertextOverhead = U0;
}

impl<Aes, NonceSize, TagSize> AeadInPlace for AesGcm<Aes, NonceSize, TagSize>
where
    Aes: BlockCipher + BlockSizeUser<BlockSize = U16> + BlockEncrypt,
    NonceSize: ArrayLength<u8>,
    TagSize: self::TagSize,
{
    fn encrypt_in_place_detached(
        &self,
        nonce: &Nonce<NonceSize>,
        associated_data: &[u8],
        buffer: &mut [u8],
    ) -> Result<Tag<TagSize>, Error> {
        if buffer.len() as u64 > P_MAX || associated_data.len() as u64 > A_MAX {
            return Err(Error);
        }

        let (ctr, mask) = self.init_ctr(nonce);

        // TODO(tarcieri): interleave encryption with GHASH
        // See: <https://github.com/RustCrypto/AEADs/issues/74>
        ctr.apply_keystream_partial(buffer.into());

        let full_tag = self.compute_tag(mask, associated_data, buffer);
        Ok(Tag::clone_from_slice(&full_tag[..TagSize::to_usize()]))
    }

    fn decrypt_in_place_detached(
        &self,
        nonce: &Nonce<NonceSize>,
        associated_data: &[u8],
        buffer: &mut [u8],
        tag: &Tag<TagSize>,
    ) -> Result<(), Error> {
        if buffer.len() as u64 > C_MAX || associated_data.len() as u64 > A_MAX {
            return Err(Error);
        }

        let (ctr, mask) = self.init_ctr(nonce);

        // TODO(tarcieri): interleave encryption with GHASH
        // See: <https://github.com/RustCrypto/AEADs/issues/74>
        let expected_tag = self.compute_tag(mask, associated_data, buffer);

        use subtle::ConstantTimeEq;
        if expected_tag[..TagSize::to_usize()].ct_eq(tag).into() {
            ctr.apply_keystream_partial(buffer.into());
            Ok(())
        } else {
            Err(Error)
        }
    }
}

impl<Aes, NonceSize, TagSize> AesGcm<Aes, NonceSize, TagSize>
where
    Aes: BlockCipher + BlockSizeUser<BlockSize = U16> + BlockEncrypt,
    NonceSize: ArrayLength<u8>,
    TagSize: self::TagSize,
{
    /// Initialize counter mode.
    ///
    /// See algorithm described in Section 7.2 of NIST SP800-38D:
    /// <https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf>
    ///
    /// > Define a block, J0, as follows:
    /// > If len(IV)=96, then J0 = IV || 0{31} || 1.
    /// > If len(IV) ≠ 96, then let s = 128 ⎡len(IV)/128⎤-len(IV), and
    /// >     J0=GHASH(IV||0s+64||[len(IV)]64).
    fn init_ctr(&self, nonce: &Nonce<NonceSize>) -> (Ctr32BE<&Aes>, Block) {
        let j0 = if NonceSize::to_usize() == 12 {
            let mut block = ghash::Block::default();
            block[..12].copy_from_slice(nonce);
            block[15] = 1;
            block
        } else {
            let mut ghash = self.ghash.clone();
            ghash.update_padded(nonce);

            let mut block = ghash::Block::default();
            let nonce_bits = (NonceSize::to_usize() as u64) * 8;
            block[8..].copy_from_slice(&nonce_bits.to_be_bytes());
            ghash.update(&[block]);
            ghash.finalize()
        };

        let mut ctr = Ctr32BE::inner_iv_init(&self.cipher, &j0);
        let mut tag_mask = Block::default();
        ctr.write_keystream_block(&mut tag_mask);
        (ctr, tag_mask)
    }

    /// Authenticate the given plaintext and associated data using GHASH.
    fn compute_tag(&self, mask: Block, associated_data: &[u8], buffer: &[u8]) -> Tag {
        let mut ghash = self.ghash.clone();
        ghash.update_padded(associated_data);
        ghash.update_padded(buffer);

        let associated_data_bits = (associated_data.len() as u64) * 8;
        let buffer_bits = (buffer.len() as u64) * 8;

        let mut block = ghash::Block::default();
        block[..8].copy_from_slice(&associated_data_bits.to_be_bytes());
        block[8..].copy_from_slice(&buffer_bits.to_be_bytes());
        ghash.update(&[block]);

        let mut tag = ghash.finalize();
        for (a, b) in tag.as_mut_slice().iter_mut().zip(mask.as_slice()) {
            *a ^= *b;
        }

        tag
    }
}
