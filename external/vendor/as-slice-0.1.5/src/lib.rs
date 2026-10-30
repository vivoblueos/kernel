//! `AsSlice` and `AsMutSlice` traits
//!
//! These traits are somewhat similar to the `AsRef` and `AsMut` except that they are **NOT**
//! polymorphic (no input type parameter) and their methods always return slices (`[T]`).
//!
//! The main use case of these traits is writing generic code that accepts (fixed size) buffers. For
//! example, a bound `T: StableDeref + AsMutSlice<Element = u8> + 'static` will accepts types like
//! `&'static mut [u8]`, `&'static mut [u8; 128]` and `&'static mut GenericArray<u8, U1024>` -- all
//! of them are appropriate for DMA transfers.
//!
//! # Minimal Supported Rust Version (MSRV)
//!
//! This crate is guaranteed to compile on stable Rust 1.31 and up. It *might* compile on older
//! versions but that may change in any new patch release.

#![deny(missing_docs)]
#![deny(warnings)]
#![no_std]

extern crate generic_array;
extern crate ga13;
extern crate ga14;
extern crate stable_deref_trait;

/// Something that can be seen as an immutable slice
///
/// **NOTE**: This trait is implemented for arrays (`[T; N]`) of sizes 0 to 256
/// (inclusive) and arrays whose lengths are a power of 2 up to `1 << 16`. These
/// implementations don't show in the documentation because they would reduce
/// readability.
pub trait AsSlice {
    /// The element type of the slice view
    type Element;

    /// Returns the immutable slice view of `Self`
    fn as_slice(&self) -> &[Self::Element];
}

/// Something that can be seen as an mutable slice
///
/// **NOTE**: This trait is implemented for arrays (`[T; N]`) of sizes 0 to 256
/// (inclusive) and arrays whose lengths are a power of 2 up to `1 << 16`. These
/// implementations don't show in the documentation because they would reduce
/// readability.
pub trait AsMutSlice: AsSlice {
    /// Returns the mutable slice view of `Self`
    fn as_mut_slice(&mut self) -> &mut [Self::Element];
}

impl<'a, S> AsSlice for &'a S
where
    S: ?Sized + AsSlice,
{
    type Element = S::Element;

    fn as_slice(&self) -> &[S::Element] {
        (**self).as_slice()
    }
}

impl<'a, S> AsSlice for &'a mut S
where
    S: ?Sized + AsSlice,
{
    type Element = S::Element;

    fn as_slice(&self) -> &[S::Element] {
        (**self).as_slice()
    }
}

impl<'a, S> AsMutSlice for &'a mut S
where
    S: ?Sized + AsMutSlice,
{
    fn as_mut_slice(&mut self) -> &mut [S::Element] {
        (**self).as_mut_slice()
    }
}

impl<T> AsSlice for [T] {
    type Element = T;

    fn as_slice(&self) -> &[T] {
        self
    }
}

impl<T> AsMutSlice for [T] {
    fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }
}

impl<T, N> AsSlice for generic_array::GenericArray<T, N>
where
    N: generic_array::ArrayLength<T>,
{
    type Element = T;

    fn as_slice(&self) -> &[T] {
        &**self
    }
}

impl<T, N> AsMutSlice for generic_array::GenericArray<T, N>
where
    N: generic_array::ArrayLength<T>,
{
    fn as_mut_slice(&mut self) -> &mut [T] {
        &mut **self
    }
}

impl<T, N> AsSlice for ga13::GenericArray<T, N>
where
    N: ga13::ArrayLength<T>,
{
    type Element = T;

    fn as_slice(&self) -> &[T] {
        &**self
    }
}

impl<T, N> AsMutSlice for ga13::GenericArray<T, N>
where
    N: ga13::ArrayLength<T>,
{
    fn as_mut_slice(&mut self) -> &mut [T] {
        &mut **self
    }
}

impl<T, N> AsSlice for ga14::GenericArray<T, N>
where
    N: ga14::ArrayLength<T>,
{
    type Element = T;

    fn as_slice(&self) -> &[T] {
        &**self
    }
}

impl<T, N> AsMutSlice for ga14::GenericArray<T, N>
where
    N: ga14::ArrayLength<T>,
{
    fn as_mut_slice(&mut self) -> &mut [T] {
        &mut **self
    }
}

macro_rules! array {
    ($($N:expr),+) => {
        $(
            #[doc(hidden)]
            impl<T> AsSlice for [T; $N] {
                type Element = T;

                fn as_slice(&self) -> &[T] {
                    self
                }
            }

            #[doc(hidden)]
            impl<T> AsMutSlice for [T; $N] {
                fn as_mut_slice(&mut self) -> &mut [T] {
                    self
                }
            }
        )+
    }
}

array!(
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
    74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
    98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
    117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135,
    136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
    155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
    174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192,
    193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211,
    212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230,
    231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249,
    250, 251, 252, 253, 254, 255);

#[cfg(not(target_pointer_width = "8"))]
array!(256, 1 << 9, 1 << 10, 1 << 11, 1 << 12, 1 << 13, 1 << 14, 1 << 15);

#[cfg(not(any(target_pointer_width = "8", target_pointer_width = "16")))]
array!(1 << 16);
