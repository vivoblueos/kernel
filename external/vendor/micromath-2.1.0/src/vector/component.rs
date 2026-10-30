//! Components of numeric vectors.

use crate::F32;
use core::{
    fmt::Debug,
    ops::{Add, Div, Mul, Sub},
};

/// Components of numeric vectors.
///
/// All components must be [`Copy`] + [`Sized`] types which support a minimal
/// set of arithmetic operations ([`Add`], [`Sub`], [`Mul`], [`Div`]), as well as
/// [`Default`], [`PartialEq`] and [`PartialOrd`].
///
/// This trait is impl'd for the following primitive types:
///
/// - [`i8`], [`i16`], [`i32`]
/// - [`u8`], [`u16`], [`u32`]
/// - [`f32`]
pub trait Component:
    Copy
    + Debug
    + Default
    + PartialEq
    + PartialOrd
    + Send
    + Sized
    + Sync
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
{
}

impl Component for i8 {}
impl Component for i16 {}
impl Component for i32 {}
impl Component for u8 {}
impl Component for u16 {}
impl Component for u32 {}
impl Component for f32 {}
impl Component for F32 {}
