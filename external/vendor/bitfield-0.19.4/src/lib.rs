#![no_std]
#![deny(
    missing_docs,
    unused_extern_crates,
    unused_import_braces,
    unused_qualifications
)]
//!  This crate provides macros to generate bitfield-like struct.
//!
//!  See the documentation of the macros for how to use them.
//!
//!  Examples and tests are also a great way to understand how to use these macros.

pub use bitfield_macros::{bitfield_constructor, bitfield_debug, bitfield_fields};

/// Internal use macro, that `debug_assert` than msb >= lsb and thus they are not inverted
#[macro_export]
macro_rules! check_msb_lsb_order {
    ($msb:expr, $lsb:expr) => {
        debug_assert!(
            $msb >= $lsb,
            "the MSB ({}) is smaller than the LSB ({}), you likely inverted them",
            $msb,
            $lsb
        );
    };
}

/// Generates and dispatches trait implementations for a struct
///
/// This must be called outside of any `impl` block.
///
/// The syntax is `TheNameOfTheTrait for struct TheNameOfTheStruct(TheInnerType);` followed by the syntax of bitfield_fields.
///
/// Supported traits:
/// * Debug
/// * BitAnd
/// * BitOr
/// * BitXor
///
/// Additional derivations:
/// * new
///   * Creates a constructor, including parameters for all fields with a setter
#[macro_export(local_inner_macros)]
macro_rules! bitfield_impl {
    (Debug for struct $name:ident([$t:ty]); $($rest:tt)*) => {
        impl<T: AsRef<[$t]> + $crate::fmt::Debug> $crate::fmt::Debug for $name<T> {
            bitfield_debug!{struct $name; $($rest)*}
        }
    };
    (Debug for struct $name:ident($t:ty); $($rest:tt)*) => {
        impl $crate::fmt::Debug for $name {
            bitfield_debug!{struct $name; $($rest)*}
        }
    };
    (BitAnd for struct $name:ident([$t:ty]); $($rest:tt)*) => {
        bitfield_impl!{@bitwise BitAnd bitand BitAndAssign bitand_assign $name([$t]) &=}
    };
    (BitAnd for struct $name:ident($t:ty); $($rest:tt)*) => {
        bitfield_impl!{@bitwise BitAnd bitand BitAndAssign bitand_assign $name($t) &=}
    };
    (BitOr for struct $name:ident([$t:ty]); $($rest:tt)*) => {
        bitfield_impl!{@bitwise BitOr bitor BitOrAssign bitor_assign $name([$t]) |=}
    };
    (BitOr for struct $name:ident($t:ty); $($rest:tt)*) => {
        bitfield_impl!{@bitwise BitOr bitor BitOrAssign bitor_assign $name($t) |=}
    };
    (BitXor for struct $name:ident([$t:ty]); $($rest:tt)*) => {
        bitfield_impl!{@bitwise BitXor bitxor BitXorAssign bitxor_assign $name([$t]) ^=}
    };
    (BitXor for struct $name:ident($t:ty); $($rest:tt)*) => {
        bitfield_impl!{@bitwise BitXor bitxor BitXorAssign bitxor_assign $name($t) ^=}
    };
    (@bitwise $bitwise:ident $func:ident $bitwise_assign:ident $func_assign:ident $name:ident([$t:ty]) $op:tt) => {
        impl<T: AsMut<[$t]> + AsRef<[$t]>> $crate::ops::$bitwise for $name<T> {
            type Output = Self;
            fn $func(mut self, rhs: Self) -> Self {
                bitfield_impl!(@mutate self rhs $op);
                self
            }
        }
        impl<T: AsMut<[$t]> + AsRef<[$t]>> $crate::ops::$bitwise_assign for $name<T> {
            fn $func_assign(&mut self, rhs: Self) {
                bitfield_impl!(@mutate self rhs $op);
            }
        }
    };
    (@bitwise $bitwise:ident $func:ident $bitwise_assign:ident $func_assign:ident $name:ident($t:ty) $op:tt) => {
        impl $crate::ops::$bitwise for $name {
            type Output = Self;
            fn $func(mut self, rhs: Self) -> Self {
                self.0 $op rhs.0;
                self
            }
        }
        impl $crate::ops::$bitwise_assign for $name {
            fn $func_assign(&mut self, rhs: Self) {
                self.0 $op rhs.0;
            }
        }
    };
    (@mutate $self:ident $rhs:ident $op:tt) => {{
        let as_mut = AsMut::<[_]>::as_mut(&mut $self.0);
        let rhs = AsRef::<[_]>::as_ref(&$rhs.0);
        for i in 0..as_mut.len() {
            as_mut[i] $op rhs[i];
        }
    }};
    (new for struct $name:ident([$t:ty]); $($rest:tt)*) => {
        impl<T: AsMut<[$t]> + Default> $name<T> {
            bitfield_constructor!{$($rest)*}
        }
    };
    (new for struct $name:ident($t:ty); $($rest:tt)*) => {
        impl $name {
            bitfield_constructor!{$($rest)*}
        }
    };
    (new{$new:ident ($($setter_name:ident: $setter_type:ty),*$(,)?)} for struct $name:ident([$t:ty]); $($rest:tt)*) => {
        impl<T: AsMut<[$t]> + Default> $name<T> {
            pub fn $new($($setter_name: $setter_type),*) -> Self {
                let mut value = Self(T::default());
                $(
                    value.$setter_name($setter_name);
                )*
                value
            }
        }
    };
    (new{$new:ident ($($setter_name:ident: $setter_type:ty),*$(,)?)} for struct $name:ident($t:ty); $($rest:tt)*) => {
        impl $name {
            pub fn $new($($setter_name: $setter_type),*) -> Self {
                let mut value = Self($t::default());
                $(
                    value.$setter_name($setter_name);
                )*
                value
            }
        }
    };
    // display a more friendly error message when someone tries to use `impl <Trait>;` syntax when not supported
    ($macro:ident for struct $name:ident $($rest:tt)*) => {
        ::core::compile_error!(::core::stringify!(Unsupported impl $macro for struct $name));
    };
}

/// Implements `BitRange` and `BitRangeMut` for a tuple struct (or "newtype").
///
/// This macro will generate an implementation of the `BitRange` trait for an existing single
/// element tuple struct.
///
/// The syntax is more or less the same as declaring a "newtype", **without** the attributes,
/// documentation comments and pub keyword.
///
/// The difference with a normal "newtype" is the type in parentheses. If the type is `[t]` (where
/// `t` is any of the unsigned integer type), the "newtype" will be generic and implement
/// `BitRange` for `T: AsRef<[t]>` and `BitRangeMut` for `T: AsMut<[t]>` (for example a slice, an array or a `Vec`). You can
/// also use `MSB0 [t]`. The difference will be the positions of the bit. You can use the
/// `bits_positions` example to see where each bits is. If the type is neither of this two, the
/// "newtype" will wrap a value of the specified type and implements `BitRange` the same ways as
/// the wrapped type.
///
/// # Examples
///
/// ```rust
/// # use bitfield::bitfield_bitrange;
/// # fn main() {}
/// struct BitField1(u32);
/// bitfield_bitrange!{struct BitField1(u32)}
///
/// struct BitField2<T>(T);
/// bitfield_bitrange!{struct BitField2([u8])}
///
/// struct BitField3<T>(T);
/// bitfield_bitrange!{struct BitField3(MSB0 [u8])}
/// ```
///
#[macro_export(local_inner_macros)]
macro_rules! bitfield_bitrange {
    (@impl_bitrange_slice $name:ident, $slice_ty:ty, $bitrange_ty:ty) => {
        impl<T: AsRef<[$slice_ty]>> $crate::BitRange<$bitrange_ty>
            for $name<T> {
                fn bit_range(&self, msb: usize, lsb: usize) -> $bitrange_ty {
                    check_msb_lsb_order!(msb, lsb);
                    let bit_len = $crate::size_of::<$slice_ty>()*8;
                    let value_bit_len = $crate::size_of::<$bitrange_ty>()*8;
                    let mut value = 0;
                    for i in (lsb..=msb).rev() {
                        value <<= 1;
                        value |= ((self.0.as_ref()[i/bit_len] >> (i%bit_len)) & 1) as $bitrange_ty;
                    }
                    value << (value_bit_len - (msb - lsb + 1)) >> (value_bit_len - (msb - lsb + 1))
                }
        }
        impl<T: AsMut<[$slice_ty]>> $crate::BitRangeMut<$bitrange_ty>
            for $name<T> {

                fn set_bit_range(&mut self, msb: usize, lsb: usize, value: $bitrange_ty) {
                    check_msb_lsb_order!(msb, lsb);
                    let bit_len = $crate::size_of::<$slice_ty>()*8;
                    let mut value = value;
                    for i in lsb..=msb {
                        self.0.as_mut()[i/bit_len] &= !(1 << (i%bit_len));
                        self.0.as_mut()[i/bit_len] |= (value & 1) as $slice_ty << (i%bit_len);
                        value >>= 1;
                    }
                }
            }
    };
    (@impl_bitrange_slice_msb0 $name:ident, $slice_ty:ty, $bitrange_ty:ty) => {
        impl<T: AsRef<[$slice_ty]>> $crate::BitRange<$bitrange_ty>
            for $name<T> {
            fn bit_range(&self, msb: usize, lsb: usize) -> $bitrange_ty {
                check_msb_lsb_order!(msb, lsb);
                let bit_len = $crate::size_of::<$slice_ty>()*8;
                let value_bit_len = $crate::size_of::<$bitrange_ty>()*8;
                let mut value = 0;
                for i in lsb..=msb {
                    value <<= 1;
                    value |= ((self.0.as_ref()[i/bit_len] >> (bit_len - i%bit_len - 1)) & 1)
                        as $bitrange_ty;
                }
                value << (value_bit_len - (msb - lsb + 1)) >> (value_bit_len - (msb - lsb + 1))
            }
        }
        impl<T: AsMut<[$slice_ty]>> $crate::BitRangeMut<$bitrange_ty>
            for $name<T> {
            fn set_bit_range(&mut self, msb: usize, lsb: usize, value: $bitrange_ty) {
                check_msb_lsb_order!(msb, lsb);
                let bit_len = $crate::size_of::<$slice_ty>()*8;
                let mut value = value;
                for i in (lsb..=msb).rev() {
                    self.0.as_mut()[i/bit_len] &= !(1 << (bit_len - i%bit_len - 1));
                    self.0.as_mut()[i/bit_len] |= (value & 1) as $slice_ty
                        << (bit_len - i%bit_len - 1);
                    value >>= 1;
                }
            }
        }
    };
    (struct $name:ident([$t:ty])) => {
        bitfield_bitrange!(@impl_bitrange_slice $name, $t, u8);
        bitfield_bitrange!(@impl_bitrange_slice $name, $t, u16);
        bitfield_bitrange!(@impl_bitrange_slice $name, $t, u32);
        bitfield_bitrange!(@impl_bitrange_slice $name, $t, u64);
        bitfield_bitrange!(@impl_bitrange_slice $name, $t, u128);
        bitfield_bitrange!(@impl_bitrange_slice $name, $t, i8);
        bitfield_bitrange!(@impl_bitrange_slice $name, $t, i16);
        bitfield_bitrange!(@impl_bitrange_slice $name, $t, i32);
        bitfield_bitrange!(@impl_bitrange_slice $name, $t, i64);
        bitfield_bitrange!(@impl_bitrange_slice $name, $t, i128);
    };
    (struct $name:ident(MSB0 [$t:ty])) => {
        bitfield_bitrange!(@impl_bitrange_slice_msb0 $name, $t, u8);
        bitfield_bitrange!(@impl_bitrange_slice_msb0 $name, $t, u16);
        bitfield_bitrange!(@impl_bitrange_slice_msb0 $name, $t, u32);
        bitfield_bitrange!(@impl_bitrange_slice_msb0 $name, $t, u64);
        bitfield_bitrange!(@impl_bitrange_slice_msb0 $name, $t, u128);
        bitfield_bitrange!(@impl_bitrange_slice_msb0 $name, $t, i8);
        bitfield_bitrange!(@impl_bitrange_slice_msb0 $name, $t, i16);
        bitfield_bitrange!(@impl_bitrange_slice_msb0 $name, $t, i32);
        bitfield_bitrange!(@impl_bitrange_slice_msb0 $name, $t, i64);
        bitfield_bitrange!(@impl_bitrange_slice_msb0 $name, $t, i128);
    };
    (struct $name:ident($t:ty)) => {
        impl<T> $crate::BitRange<T> for $name where $t: $crate::BitRange<T> {
            fn bit_range(&self, msb: usize, lsb: usize) -> T {
                self.0.bit_range(msb, lsb)
            }
        }
        impl<T> $crate::BitRangeMut<T> for $name where $t: $crate::BitRangeMut<T> {
            fn set_bit_range(&mut self, msb: usize, lsb: usize, value: T) {
                self.0.set_bit_range(msb, lsb, value);
            }
        }
    };
}

/// Combines `bitfield_bitrange` and `bitfield_fields`.
///
/// The syntax of this macro is the syntax of a tuple struct, including attributes and
/// documentation comments, followed by a semicolon, some optional elements, and finally the fields
/// as described in the `bitfield_fields` documentation.
///
/// The first optional element is `no default BitRange;`. With that, no implementation of
/// `BitRange` will be generated.
///
/// The second optional element is a set of lines of the form `impl <Trait>;`. The following traits are supported:
/// * `Debug`; This will generate an implementation of `fmt::Debug` with the `bitfield_debug` macro.
/// * `BitAnd`, `BitOr`, `BitXor`; These will generate implementations of the relevant `ops::Bit___` and `ops::Bit___Assign` traits.
/// * `new`; This will generate a constructor that calls all of the bitfield's setter methods with an argument of the appropriate type
///
/// The difference with calling those macros separately is that `bitfield_fields` is called
/// from an appropriate `impl` block. If you use the non-slice form of `bitfield_bitrange`, the
/// default type for `bitfield_fields` will be set to the wrapped fields.
///
/// See the documentation of these macros for more information on their respective syntax.
///
/// # Example
///
/// ```rust
/// # use bitfield::bitfield;
/// # fn main() {}
/// bitfield!{
///   pub struct BitField1(u16);
///   impl Debug;
///   // The fields default to u16
///   field1, set_field1: 10, 0;
///   pub field2, _ : 12, 3;
/// }
/// ```
///
/// or with a custom `BitRange` and `BitRangeMut` implementation :
/// ```rust
/// # use bitfield::{bitfield, BitRange, BitRangeMut};
/// # fn main() {}
/// bitfield!{
///   pub struct BitField1(u16);
///   no default BitRange;
///   impl Debug;
///   impl BitAnd;
///   u8;
///   field1, set_field1: 10, 0;
///   pub field2, _ : 12, 3;
/// }
/// impl BitRange<u8> for BitField1 {
///     fn bit_range(&self, msb: usize, lsb: usize) -> u8 {
///         let width = msb - lsb + 1;
///         let mask = (1 << width) - 1;
///         ((self.0 >> lsb) & mask) as u8
///     }
/// }
/// impl BitRangeMut<u8> for BitField1 {
///     fn set_bit_range(&mut self, msb: usize, lsb: usize, value: u8) {
///         self.0 = (value as u16) << lsb;
///     }
/// }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! bitfield {
    // Force `impl <Trait>` to always be after `no default BitRange` it the two are present.
    // This simplify the rest of the macro.
    ($(#[$attribute:meta])* $vis:vis struct $name:ident($($type:tt)*); $(impl $trait:ident$({$($trait_arg:tt)*})?;)+ no default BitRange; $($rest:tt)*) => {
         bitfield!{$(#[$attribute])* $vis struct $name($($type)*); no default BitRange; $(impl $trait$({$($trait_arg)*})?;)* $($rest)*}
     };

    // If we have `impl <Trait>` without `no default BitRange`, we will still match, because when
    // we call `bitfield_bitrange`, we add `no default BitRange`.
    ($(#[$attribute:meta])* $vis:vis struct $name:ident([$t:ty]); no default BitRange; impl $trait:ident$({$($trait_arg:tt)*})?; $($rest:tt)*) => {
        bitfield_impl!{$trait$({$($trait_arg)*})? for struct $name([$t]); $($rest)*}

        bitfield!{$(#[$attribute])* $vis struct $name([$t]); no default BitRange;  $($rest)*}
    };
    ($(#[$attribute:meta])* $vis:vis struct $name:ident([$t:ty]); no default BitRange; $($rest:tt)*) => {
        $(#[$attribute])*
        $vis struct $name<T>(pub T);

        //impl<T: AsMut<[$t]> + AsRef<[$t]>> $name<T> {
        //    bitfield_fields!{$($rest)*}
        //}
        impl<T: AsRef<[$t]>> $name<T> {
           bitfield_fields!{only getter; $($rest)*}
        }
        impl<T: AsMut<[$t]>> $name<T> {
           bitfield_fields!{only setter; $($rest)*}
        }
    };
    ($(#[$attribute:meta])* $vis:vis struct $name:ident([$t:ty]); $($rest:tt)*) => {
        bitfield_bitrange!(struct $name([$t]));
        bitfield!{$(#[$attribute])* $vis struct $name([$t]); no default BitRange; $($rest)*}
    };

    // The only difference between the MSB0 version anf the non-MSB0 version, is the BitRange
    // implementation. We delegate everything else to the non-MSB0 version of the macro.
    ($(#[$attribute:meta])* $vis:vis struct $name:ident(MSB0 [$t:ty]); no default BitRange; $($rest:tt)*) => {
        bitfield!{$(#[$attribute])* $vis struct $name([$t]); no default BitRange; $($rest)*}
    };
    ($(#[$attribute:meta])* $vis:vis struct $name:ident(MSB0 [$t:ty]); $($rest:tt)*) => {
        bitfield_bitrange!(struct $name(MSB0 [$t]));
        bitfield!{$(#[$attribute])* $vis struct $name([$t]); no default BitRange; $($rest)*}
    };

    ($(#[$attribute:meta])* $vis:vis struct $name:ident($t:ty); no default BitRange; impl $trait:ident$({$($trait_arg:tt)*})?; $($rest:tt)*) => {
        bitfield_impl!{$trait$({$($trait_arg)*})? for struct $name($t); $($rest)*}

        bitfield!{$(#[$attribute])* $vis struct $name($t); no default BitRange; $($rest)*}
    };
    ($(#[$attribute:meta])* $vis:vis struct $name:ident($t:ty); no default BitRange; $($rest:tt)*) => {
        $(#[$attribute])*
        $vis struct $name(pub $t);

        impl $name {
            bitfield_fields!{$t; $($rest)*}
         }
    };
    ($(#[$attribute:meta])* $vis:vis struct $name:ident($t:ty); $($rest:tt)*) => {
        bitfield_bitrange!(struct $name($t));
        bitfield!{$(#[$attribute])* $vis struct $name($t); no default BitRange; $($rest)*}
    };
}

#[doc(hidden)]
pub use core::convert::Into;
#[doc(hidden)]
pub use core::convert::TryInto;
#[doc(hidden)]
pub use core::fmt;
#[doc(hidden)]
pub use core::mem::size_of;
#[doc(hidden)]
pub use core::ops;

/// A trait to get ranges of bits.
pub trait BitRange<T> {
    /// Get a range of bits.
    fn bit_range(&self, msb: usize, lsb: usize) -> T;
}

/// A trait to set ranges of bits.
pub trait BitRangeMut<T> {
    /// Set a range of bits.
    fn set_bit_range(&mut self, msb: usize, lsb: usize, value: T);
}

/// A trait to get a single bit.
///
/// This trait is implemented for all type that implement `BitRange<u8>`.
pub trait Bit {
    /// Get a single bit.
    fn bit(&self, bit: usize) -> bool;
}

/// A trait to set a single bit.
///
/// This trait is implemented for all type that implement `BitRangeMut<u8>`.
pub trait BitMut {
    /// Set a single bit.
    fn set_bit(&mut self, bit: usize, value: bool);
}

impl<T: BitRange<u8>> Bit for T {
    fn bit(&self, bit: usize) -> bool {
        self.bit_range(bit, bit) != 0
    }
}

impl<T: BitRangeMut<u8>> BitMut for T {
    fn set_bit(&mut self, bit: usize, value: bool) {
        self.set_bit_range(bit, bit, value as u8);
    }
}

#[doc(hidden)]
trait ToUnsigned {
    type Output;
}

macro_rules! impl_to_unsigned {
    ($($t:ty => $u:ty),* $(,)?) => {
        $(
            impl ToUnsigned for $t {
                type Output = $u;
            }
        )*
    };
}

impl_to_unsigned! {
    u8 => u8, u16 => u16, u32 => u32, u64 => u64, u128 => u128,
    i8 => u8, i16 => u16, i32 => u32, i64 => u64, i128 => u128,
}

macro_rules! impl_bitrange_for_u {
    ($t:ty, $bitrange_ty:ty) => {
        impl BitRange<$bitrange_ty> for $t {
            #[inline]
            #[allow(clippy::cast_lossless)]
            #[allow(clippy::manual_bits)]
            fn bit_range(&self, msb: usize, lsb: usize) -> $bitrange_ty {
                check_msb_lsb_order!(msb, lsb);
                let bit_len = size_of::<$t>() * 8;
                let result_bit_len = size_of::<$bitrange_ty>() * 8;
                let result =
                    ((*self << (bit_len - msb - 1)) >> (bit_len - msb - 1 + lsb)) as $bitrange_ty;
                result << (result_bit_len - (msb - lsb + 1)) >> (result_bit_len - (msb - lsb + 1))
            }
        }

        impl BitRangeMut<$bitrange_ty> for $t {
            #[inline]
            #[allow(clippy::cast_lossless)]
            #[allow(clippy::manual_bits)]
            fn set_bit_range(&mut self, msb: usize, lsb: usize, value: $bitrange_ty) {
                check_msb_lsb_order!(msb, lsb);
                let bit_len = size_of::<$t>() * 8;
                let mask: <$t as ToUnsigned>::Output = !(0 as <$t as ToUnsigned>::Output)
                    << (bit_len - msb - 1)
                    >> (bit_len - msb - 1 + lsb)
                    << (lsb);
                *self &= !mask as $t;
                *self |= (((value as <$t as ToUnsigned>::Output) << lsb) & mask) as $t;
            }
        }
    };
}

macro_rules! impl_bitrange_for_u_combinations {
((),($($bitrange_ty:ty),*)) => {

};
(($t:ty),($($bitrange_ty:ty),*)) => {
        $(impl_bitrange_for_u!{$t, $bitrange_ty})*
};
    (($t_head:ty, $($t_rest:ty),*),($($bitrange_ty:ty),*)) => {
        impl_bitrange_for_u_combinations!{($t_head), ($($bitrange_ty),*)}
        impl_bitrange_for_u_combinations!{($($t_rest),*), ($($bitrange_ty),*)}
    };
}

impl_bitrange_for_u_combinations! {(u8, u16, u32, u64, u128), (u8, u16, u32, u64, u128)}
impl_bitrange_for_u_combinations! {(u8, u16, u32, u64, u128), (i8, i16, i32, i64, i128)}
impl_bitrange_for_u_combinations! {(i8, i16, i32, i64, i128), (u8, u16, u32, u64, u128)}
impl_bitrange_for_u_combinations! {(i8, i16, i32, i64, i128), (i8, i16, i32, i64, i128)}
