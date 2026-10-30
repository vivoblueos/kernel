//! 3-dimensional vector

use super::{Component, Vector};
use crate::F32;
use core::{
    iter::FromIterator,
    ops::{Add, AddAssign, Index, Mul, MulAssign, Sub, SubAssign},
};

/// 3-dimensional XYZ vector of `i8` values
pub type I8x3 = Vector3d<i8>;

/// 3-dimensional XYZ vector of `i16` values
pub type I16x3 = Vector3d<i16>;

/// 3-dimensional XYZ vector of `i32` values
pub type I32x3 = Vector3d<i32>;

/// 3-dimensional XYZ vector of `u8` values
pub type U8x3 = Vector3d<u8>;

/// 3-dimensional XYZ vector of `u16` values
pub type U16x3 = Vector3d<u16>;

/// 3-dimensional XYZ vector of `u32` values
pub type U32x3 = Vector3d<u32>;

/// 3-dimensional XYZ vector of `f32` values
pub type F32x3 = Vector3d<f32>;

/// 3-dimensional vector
#[derive(Copy, Clone, Debug, Default, PartialEq)]
pub struct Vector3d<C: Component> {
    /// X component
    pub x: C,

    /// Y component
    pub y: C,

    /// Z component
    pub z: C,
}

impl<C> Vector3d<C>
where
    C: Component,
{
    /// Return a 3-element array containing the coordinates
    // TODO(tarcieri): move this to the `Vector` trait leveraging const generics?
    pub fn to_array(&self) -> [C; 3] {
        [self.x, self.y, self.z]
    }
}

impl<C> FromIterator<C> for Vector3d<C>
where
    C: Component,
{
    fn from_iter<T>(into_iter: T) -> Self
    where
        T: IntoIterator<Item = C>,
    {
        let mut iter = into_iter.into_iter();

        let x = iter.next().expect("no x-axis component in slice");
        let y = iter.next().expect("no y-axis component in slice");
        let z = iter.next().expect("no z-axis component in slice");

        assert!(
            iter.next().is_none(),
            "too many items for 3-dimensional vector"
        );

        Self { x, y, z }
    }
}

impl<C> Vector<C> for Vector3d<C>
where
    C: Component,
{
    const AXES: usize = 3;

    fn get(self, index: usize) -> Option<C> {
        match index {
            0 => Some(self.x),
            1 => Some(self.y),
            2 => Some(self.z),
            _ => None,
        }
    }

    fn dot(self, rhs: Self) -> C {
        (self.x * rhs.x) + (self.y * rhs.y) + (self.z * rhs.z)
    }
}

impl<C> From<(C, C, C)> for Vector3d<C>
where
    C: Component,
{
    fn from(vector: (C, C, C)) -> Self {
        Self {
            x: vector.0,
            y: vector.1,
            z: vector.2,
        }
    }
}

impl<C> Index<usize> for Vector3d<C>
where
    C: Component,
{
    type Output = C;

    fn index(&self, i: usize) -> &C {
        match i {
            0 => &self.x,
            1 => &self.y,
            2 => &self.z,
            _ => panic!("index out of range"),
        }
    }
}

impl<C> Add for Vector3d<C>
where
    C: Component,
{
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
            z: self.z + rhs.z,
        }
    }
}

impl<C> AddAssign for Vector3d<C>
where
    C: Component,
{
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}

impl<C> Sub for Vector3d<C>
where
    C: Component,
{
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
            z: self.z - rhs.z,
        }
    }
}

impl<C> SubAssign for Vector3d<C>
where
    C: Component,
{
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other;
    }
}

/// Compute the cross product of two vectors
impl<C> Mul for Vector3d<C>
where
    C: Component,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self {
            x: (self.y * rhs.z) - (self.z * rhs.y),
            y: (self.z * rhs.x) - (self.x * rhs.z),
            z: (self.x * rhs.y) - (self.y * rhs.x),
        }
    }
}

/// Multiply vector by a scalar component
impl<C> Mul<C> for Vector3d<C>
where
    C: Component,
{
    type Output = Self;

    fn mul(self, rhs: C) -> Self {
        Self {
            x: self.x * rhs,
            y: self.y * rhs,
            z: self.z * rhs,
        }
    }
}

impl<C> MulAssign<C> for Vector3d<C>
where
    C: Component,
{
    fn mul_assign(&mut self, rhs: C) {
        *self = *self * rhs;
    }
}

impl From<I8x3> for F32x3 {
    fn from(vector: I8x3) -> F32x3 {
        Self {
            x: vector.x.into(),
            y: vector.y.into(),
            z: vector.z.into(),
        }
    }
}

impl From<I16x3> for F32x3 {
    fn from(vector: I16x3) -> F32x3 {
        Self {
            x: vector.x.into(),
            y: vector.y.into(),
            z: vector.z.into(),
        }
    }
}

impl From<U8x3> for F32x3 {
    fn from(vector: U8x3) -> F32x3 {
        Self {
            x: vector.x.into(),
            y: vector.y.into(),
            z: vector.z.into(),
        }
    }
}

impl From<U16x3> for F32x3 {
    fn from(vector: U16x3) -> F32x3 {
        Self {
            x: vector.x.into(),
            y: vector.y.into(),
            z: vector.z.into(),
        }
    }
}

impl From<Vector3d<F32>> for F32x3 {
    fn from(vector: Vector3d<F32>) -> F32x3 {
        Self {
            x: vector.x.into(),
            y: vector.y.into(),
            z: vector.z.into(),
        }
    }
}
