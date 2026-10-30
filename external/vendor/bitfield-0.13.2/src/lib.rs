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

/// Declares the fields of struct.
///
/// This macro will generate the methods to access the fields of a bitfield. It must be called
/// from an `impl` block for a type that implements the `BitRange` and/or the `Bit` traits
/// (which traits are required depending on what type of fields are used).
///
/// The syntax of this macro is composed of declarations ended by semicolons. There are two types
/// of declarations: default type, and fields.
///
/// A default type is just a type followed by a semicolon. This will affect all the following field
/// declarations.
///
/// A field declaration is composed of the following:
///
/// * Optional attributes (`#[...]`), documentation comments (`///`) are attributes;
/// * An optional pub keyword to make the methods public
/// * An optional type followed by a comma
/// * Optionally, the word `into` followed by a type, followed by a comma
/// * The getter and setter idents, separated by a comma
/// * A colon
/// * One to three expressions of type `usize`
///
/// The attributes and pub will be applied to the two methods generated.
///
/// If the `into` part is used, the getter will convert the field after reading it.
///
/// The getter and setter idents can be `_` to not generate one of the two. For example, if the
/// setter is `_`, the field will be read-only.
///
/// The expressions at the end are the bit positions. Their meaning depends on the number of
/// expressions:
///
///  * One expression: the field is a single bit. The type is ignored and `bool` is used. The trait
///    `Bit` is used.
///  * Two expressions: `msb, lsb`, the field is composed of the bits from `msb` to `lsb`, included.
///  * Three expressions: `msb, lsb, count`, the field is an array. The first element is composed of
///    the bits from `msb` to `lsb`. The following elements are consecutive bits range of the same
///    size.
///
/// # Example
///
/// ```rust
/// # #[macro_use] extern crate bitfield;
/// # fn main() {}
/// # struct FooBar(u64);
/// # bitfield_bitrange!{struct FooBar(u64)}
/// # impl From<u32> for FooBar{ fn from(_: u32) -> FooBar {unimplemented!()}}
/// # impl From<FooBar> for u32{ fn from(_: FooBar) -> u32 {unimplemented!()}}
/// # impl FooBar {
/// bitfield_fields!{
///     // The default type will be `u64
///     u64;
///     // filed1 is read-write, public, the methods are inline
///     #[inline]
///     pub field1, set_field1: 10, 0;
///     // `field2` is  read-only, private, and of type bool.
///     field2, _ : 0;
///     // `field3` will be read as an `u32` and then converted to `FooBar`.
///     // The setter is not affected, it still need an `u32` value.
///     u32, into FooBar, field3, set_field3: 10, 0;
///     // `field4` will be read as an `u32` and then converted to `FooBar`.
///     // The setter will take a `FooBar`, and converted back to an `u32`.
///     u32, from into FooBar, field4, set_field4: 10, 0;
/// }
/// # }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! bitfield_fields {
    (@field $(#[$attribute:meta])* ($($vis:tt)*) $t:ty, $from:ty, $into:ty, _, $setter:ident: $msb:expr,
     $lsb:expr, $count:expr) => {
        $(#[$attribute])*
        #[allow(unknown_lints)]
        #[allow(eq_op)]
        $($vis)* fn $setter(&mut self, index: usize, value: $from) {
            use $crate::BitRange;
            __bitfield_debug_assert!(index < $count);
            let width = $msb - $lsb + 1;
            let lsb = $lsb + index*width;
            let msb = lsb + width - 1;
            self.set_bit_range(msb, lsb, $crate::Into::<$t>::into(value));
        }
    };
    (@field $(#[$attribute:meta])* ($($vis:tt)*) $t:ty, $from:ty, $into:ty, _, $setter:ident: $msb:expr,
     $lsb:expr) => {
        $(#[$attribute])*
        $($vis)* fn $setter(&mut self, value: $from) {
            use $crate::BitRange;
            self.set_bit_range($msb, $lsb, $crate::Into::<$t>::into(value));
        }
    };
    (@field $(#[$attribute:meta])* ($($vis:tt)*) $t:ty, $from:ty, $into:ty, _, $setter:ident: $bit:expr) => {
        $(#[$attribute])*
        $($vis)* fn $setter(&mut self, value: bool) {
            use $crate::Bit;
            self.set_bit($bit, value);
        }
    };
    (@field $(#[$attribute:meta])* ($($vis:tt)*) $t:ty, $from:ty, $into:ty, $getter:ident, _: $msb:expr,
     $lsb:expr, $count:expr) => {
        $(#[$attribute])*
        #[allow(unknown_lints)]
        #[allow(eq_op)]
        $($vis)* fn $getter(&self, index: usize) -> $into {
            use $crate::BitRange;
            __bitfield_debug_assert!(index < $count);
            let width = $msb - $lsb + 1;
            let lsb = $lsb + index*width;
            let msb = lsb + width - 1;
            let raw_value: $t = self.bit_range(msb, lsb);
            $crate::Into::into(raw_value)
        }
    };
    (@field $(#[$attribute:meta])* ($($vis:tt)*) $t:ty, $from:ty, $into:ty, $getter:ident, _: $msb:expr,
     $lsb:expr) => {
        $(#[$attribute])*
        $($vis)* fn $getter(&self) -> $into {
            use $crate::BitRange;
            let raw_value: $t = self.bit_range($msb, $lsb);
            $crate::Into::into(raw_value)
        }
    };
    (@field $(#[$attribute:meta])* ($($vis:tt)*) $t:ty, $from:ty, $into:ty, $getter:ident, _: $bit:expr) => {
        $(#[$attribute])*
        $($vis)* fn $getter(&self) -> bool {
            use $crate::Bit;
            self.bit($bit)
        }
    };
    (@field $(#[$attribute:meta])* ($($vis:tt)*) $t:ty, $from:ty, $into:ty, $getter:ident, $setter:ident:
     $($exprs:expr),*) => {
        bitfield_fields!(@field $(#[$attribute])* ($($vis)*) $t, $from, $into, $getter, _: $($exprs),*);
        bitfield_fields!(@field $(#[$attribute])* ($($vis)*) $t, $from, $into, _, $setter: $($exprs),*);
    };

    ($t:ty;) => {};
    ($default_ty:ty; pub $($rest:tt)*) => {
        bitfield_fields!{$default_ty; () pub $($rest)*}
    };
    ($default_ty:ty; #[$attribute:meta] $($rest:tt)*) => {
        bitfield_fields!{$default_ty; (#[$attribute]) $($rest)*}
    };
    ($default_ty:ty; ($(#[$attributes:meta])*) #[$attribute:meta] $($rest:tt)*) => {
        bitfield_fields!{$default_ty; ($(#[$attributes])* #[$attribute]) $($rest)*}
    };
    ($default_ty:ty; ($(#[$attribute:meta])*) pub $t:ty, from into $into:ty, $getter:tt, $setter:tt:
     $($exprs:expr),*; $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* (pub) $t, $into, $into, $getter, $setter: $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };
    ($default_ty:ty; ($(#[$attribute:meta])*) pub $t:ty, into $into:ty, $getter:tt, $setter:tt:
     $($exprs:expr),*; $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* (pub) $t, $t, $into, $getter, $setter: $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };
    ($default_ty:ty; ($(#[$attribute:meta])*) pub $t:ty, $getter:tt, $setter:tt:  $($exprs:expr),*;
     $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* (pub) $t, $t, $t, $getter, $setter: $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };
    ($default_ty:ty; ($(#[$attribute:meta])*) pub from into $into:ty, $getter:tt, $setter:tt:
     $($exprs:expr),*; $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* (pub) $default_ty, $into, $into, $getter, $setter:
                         $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };
    ($default_ty:ty; ($(#[$attribute:meta])*) pub into $into:ty, $getter:tt, $setter:tt:
     $($exprs:expr),*; $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* (pub) $default_ty, $default_ty, $into, $getter, $setter:
                         $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };
    ($default_ty:ty; ($(#[$attribute:meta])*) pub $getter:tt, $setter:tt:  $($exprs:expr),*;
     $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* (pub) $default_ty, $default_ty, $default_ty, $getter, $setter:
                                $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };

    ($default_ty:ty; ($(#[$attribute:meta])*) $t:ty, from into $into:ty, $getter:tt, $setter:tt:
     $($exprs:expr),*; $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* () $t, $into, $into, $getter, $setter: $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };

    ($default_ty:ty; ($(#[$attribute:meta])*) $t:ty, into $into:ty, $getter:tt, $setter:tt:
     $($exprs:expr),*; $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* () $t, $t, $into, $getter, $setter: $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };

    ($default_ty:ty; ($(#[$attribute:meta])*) $t:ty, $getter:tt, $setter:tt:  $($exprs:expr),*;
     $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* () $t, $t, $t, $getter, $setter: $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };
    ($default_ty:ty; ($(#[$attribute:meta])*) from into $into:ty, $getter:tt, $setter:tt:
     $($exprs:expr),*; $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* () $default_ty, $into, $into, $getter, $setter:
                         $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };
    ($default_ty:ty; ($(#[$attribute:meta])*) into $into:ty, $getter:tt, $setter:tt:
     $($exprs:expr),*; $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* () $default_ty, $default_ty, $into, $getter, $setter:
                         $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };
    ($default_ty:ty; ($(#[$attribute:meta])*) $getter:tt, $setter:tt:  $($exprs:expr),*;
     $($rest:tt)*) => {
        bitfield_fields!{@field $(#[$attribute])* () $default_ty, $default_ty, $default_ty, $getter, $setter:
                                $($exprs),*}
        bitfield_fields!{$default_ty; $($rest)*}
    };
    ($previous_default_ty:ty; $default_ty:ty; $($rest:tt)*) => {
        bitfield_fields!{$default_ty; $($rest)*}
    };
    ($default_ty:ty; $($rest:tt)*) => {
        bitfield_fields!{$default_ty; () $($rest)*}
    };
    ($($rest:tt)*) => {
        bitfield_fields!{SET_A_DEFAULT_TYPE_OR_SPECIFY_THE_TYPE_FOR_EACH_FIELDS; $($rest)*}
    }
}

/// Generates a `fmt::Debug` implementation.
///
/// This macros must be called from a `impl Debug for ...` block. It will generate the `fmt` method.
///
/// In most of the case, you will not directly call this macros, but use `bitfield`.
///
/// The syntax is `struct TheNameOfTheStruct` followed by the syntax of `bitfield_fields`.
///
/// The write-only fields are ignored.
///
/// # Example
///
/// ```rust
/// # #[macro_use] extern crate bitfield;
/// struct FooBar(u32);
/// bitfield_bitrange!{struct FooBar(u32)}
/// impl FooBar{
///     bitfield_fields!{
///        u32;
///        field1, _: 7, 0;
///        field2, _: 31, 24;
///     }
/// }
///
/// impl std::fmt::Debug for FooBar {
///     bitfield_debug!{
///        struct FooBar;
///        field1, _: 7, 0;
///        field2, _: 31, 24;
///     }
/// }
///
/// fn main() {
///     let foobar = FooBar(0x11223344);
///     println!("{:?}", foobar);

/// }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! bitfield_debug {
    (struct $name:ident; $($rest:tt)*) => {
        fn fmt(&self, f: &mut $crate::fmt::Formatter) -> $crate::fmt::Result {
            let mut debug_struct = f.debug_struct(__bitfield_stringify!($name));
            debug_struct.field(".0", &self.0);
            bitfield_debug!{debug_struct, self, $($rest)*}
            debug_struct.finish()
        }
    };
    ($debug_struct:ident, $self:ident, #[$attribute:meta] $($rest:tt)*) => {
        bitfield_debug!{$debug_struct, $self, $($rest)*}
    };
    ($debug_struct:ident, $self:ident, pub $($rest:tt)*) => {
        bitfield_debug!{$debug_struct, $self, $($rest)*}
    };
    ($debug_struct:ident, $self:ident, _, $setter:tt: $($exprs:expr),*; $($rest:tt)*) => {
        bitfield_debug!{$debug_struct, $self, $($rest)*}
    };
    ($debug_struct:ident, $self:ident, $type:ty; $($rest:tt)*) => {
        bitfield_debug!{$debug_struct, $self, $($rest)*}
    };
    ($debug_struct:ident, $self:ident, $getter:ident, $setter:tt: $msb:expr, $lsb:expr, $count:expr;
     $($rest:tt)*) => {
        let mut array = [$self.$getter(0); $count];
        for (i, e) in (&mut array).into_iter().enumerate() {
            *e = $self.$getter(i);
        }
        $debug_struct.field(__bitfield_stringify!($getter), &array);
        bitfield_debug!{$debug_struct, $self, $($rest)*}
    };
    ($debug_struct:ident, $self:ident, $getter:ident, $setter:tt: $($exprs:expr),*; $($rest:tt)*)
        => {
        $debug_struct.field(__bitfield_stringify!($getter), &$self.$getter());
        bitfield_debug!{$debug_struct, $self, $($rest)*}
    };
    ($debug_struct:ident, $self:ident, from into $into:ty, $($rest:tt)*) => {
        bitfield_debug!{$debug_struct, $self, $($rest)*}
    };
    ($debug_struct:ident, $self:ident, into $into:ty, $($rest:tt)*) => {
        bitfield_debug!{$debug_struct, $self, $($rest)*}
    };
    ($debug_struct:ident, $self:ident, $type:ty, $($rest:tt)*) => {
        bitfield_debug!{$debug_struct, $self, $($rest)*}
    };
    ($debug_struct:ident, $self:ident, ) => {};
}

/// Implements `BitRange` for a tuple struct (or "newtype").
///
/// This macro will generate an implementation of the `BitRange` trait for an existing single
/// element tuple struct.
///
/// The syntax is more or less the same as declaring a "newtype", **without** the attributes,
/// documentation comments and pub keyword.
///
/// The difference with a normal "newtype" is the type in parentheses. If the type is `[t]` (where
/// `t` is any of the unsigned integer type), the "newtype" will be generic and implement
/// `BitRange` for `T: AsMut<[t]> + AsRef<[t]>` (for example a slice, an array or a `Vec`). You can
/// also use `MSB0 [t]`. The difference will be the positions of the bit. You can use the
/// `bits_positions` example to see where each bits is. If the type is neither of this two, the
/// "newtype" will wrap a value of the specified type and implements `BitRange` the same ways as
/// the wrapped type.
///
/// # Examples
///
/// ```rust
/// # #[macro_use] extern crate bitfield;
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
        impl<T: AsMut<[$slice_ty]> + AsRef<[$slice_ty]>> $crate::BitRange<$bitrange_ty>
            for $name<T> {
                fn bit_range(&self, msb: usize, lsb: usize) -> $bitrange_ty {
                    let bit_len = $crate::size_of::<$slice_ty>()*8;
                    let value_bit_len = $crate::size_of::<$bitrange_ty>()*8;
                    let mut value = 0;
                    for i in (lsb..=msb).rev() {
                        value <<= 1;
                        value |= ((self.0.as_ref()[i/bit_len] >> (i%bit_len)) & 1) as $bitrange_ty;
                    }
                    value << (value_bit_len - (msb - lsb + 1)) >> (value_bit_len - (msb - lsb + 1))
                }

                fn set_bit_range(&mut self, msb: usize, lsb: usize, value: $bitrange_ty) {
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
        impl<T: AsMut<[$slice_ty]> + AsRef<[$slice_ty]>> $crate::BitRange<$bitrange_ty>
            for $name<T> {
            fn bit_range(&self, msb: usize, lsb: usize) -> $bitrange_ty {
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

            fn set_bit_range(&mut self, msb: usize, lsb: usize, value: $bitrange_ty) {
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
/// The second optional element is `impl Debug;`. This will generate an implementation of
/// `fmt::Debug` with the `bitfield_debug` macro.
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
/// # #[macro_use] extern crate bitfield;
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
/// or with a custom `BitRange` implementation :
/// ```rust
/// # #[macro_use] extern crate bitfield;
/// # use bitfield::BitRange;
/// # fn main() {}
/// bitfield!{
///   pub struct BitField1(u16);
///   no default BitRange;
///   impl Debug;
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
///     fn set_bit_range(&mut self, msb: usize, lsb: usize, value: u8) {
///         self.0 = (value as u16) << lsb;
///     }
/// }
/// ```
#[macro_export(local_inner_macros)]
macro_rules! bitfield {
    ($(#[$attribute:meta])* pub struct $($rest:tt)*) => {
        bitfield!($(#[$attribute])* (pub) struct $($rest)*);
    };
    ($(#[$attribute:meta])* struct $($rest:tt)*) => {
        bitfield!($(#[$attribute])* () struct $($rest)*);
    };
    // Force `impl Debug` to always be after `no default BitRange` it the two are present.
    // This simplify the rest of the macro.
    ($(#[$attribute:meta])* ($($vis:tt)*) struct $name:ident($($type:tt)*); impl Debug; no default BitRange; $($rest:tt)*) => {
         bitfield!{$(#[$attribute])* ($($vis)*) struct $name($($type)*); no default BitRange; impl Debug; $($rest)*}
     };

    // If we have `impl Debug` without `no default BitRange`, we will still match, because when
    // we call `bitfield_bitrange`, we add `no default BitRange`.
    ($(#[$attribute:meta])* ($($vis:tt)*) struct $name:ident([$t:ty]); no default BitRange; impl Debug; $($rest:tt)*) => {
        impl<T: AsMut<[$t]> + AsRef<[$t]> + $crate::fmt::Debug> $crate::fmt::Debug for $name<T> {
            bitfield_debug!{struct $name; $($rest)*}
        }

        bitfield!{$(#[$attribute])* ($($vis)*) struct $name([$t]); no default BitRange;  $($rest)*}
    };
    ($(#[$attribute:meta])* ($($vis:tt)*) struct $name:ident([$t:ty]); no default BitRange; $($rest:tt)*) => {
        $(#[$attribute])*
        $($vis)* struct $name<T>(pub T);

        impl<T: AsMut<[$t]> + AsRef<[$t]>> $name<T> {
            bitfield_fields!{$($rest)*}
        }
    };
    ($(#[$attribute:meta])* ($($vis:tt)*) struct $name:ident([$t:ty]); $($rest:tt)*) => {
        bitfield_bitrange!(struct $name([$t]));
        bitfield!{$(#[$attribute])* ($($vis)*) struct $name([$t]); no default BitRange; $($rest)*}
    };

    // The only difference between the MSB0 version anf the non-MSB0 version, is the BitRange
    // implementation. We delegate everything else to the non-MSB0 version of the macro.
    ($(#[$attribute:meta])* ($($vis:tt)*) struct $name:ident(MSB0 [$t:ty]); no default BitRange; $($rest:tt)*) => {
        bitfield!{$(#[$attribute])* ($($vis)*) struct $name([$t]); no default BitRange; $($rest)*}
    };
    ($(#[$attribute:meta])* ($($vis:tt)*) struct $name:ident(MSB0 [$t:ty]); $($rest:tt)*) => {
        bitfield_bitrange!(struct $name(MSB0 [$t]));
        bitfield!{$(#[$attribute])* ($($vis)*) struct $name([$t]); no default BitRange; $($rest)*}
    };

    ($(#[$attribute:meta])* ($($vis:tt)*) struct $name:ident($t:ty); no default BitRange; impl Debug; $($rest:tt)*) => {
        impl $crate::fmt::Debug for $name {
            bitfield_debug!{struct $name; $($rest)*}
        }

        bitfield!{$(#[$attribute])* ($($vis)*) struct $name($t); no default BitRange; $($rest)*}
    };
    ($(#[$attribute:meta])* ($($vis:tt)*) struct $name:ident($t:ty); no default BitRange; $($rest:tt)*) => {
        $(#[$attribute])*
        $($vis)* struct $name(pub $t);

        impl $name {
            bitfield_fields!{$t; $($rest)*}
         }
    };
    ($(#[$attribute:meta])* ($($vis:tt)*) struct $name:ident($t:ty); $($rest:tt)*) => {
        bitfield_bitrange!(struct $name($t));
        bitfield!{$(#[$attribute])* ($($vis)*) struct $name($t); no default BitRange; $($rest)*}
    };
}

#[doc(hidden)]
pub use core::convert::Into;
#[doc(hidden)]
pub use core::fmt;
#[doc(hidden)]
pub use core::mem::size_of;

/// A trait to get or set ranges of bits.
pub trait BitRange<T> {
    /// Get a range of bits.
    fn bit_range(&self, msb: usize, lsb: usize) -> T;
    /// Set a range of bits.
    fn set_bit_range(&mut self, msb: usize, lsb: usize, value: T);
}

/// A trait to get or set a single bit.
///
/// This trait is implemented for all type that implement `BitRange<u8>`.
pub trait Bit {
    /// Get a single bit.
    fn bit(&self, bit: usize) -> bool;

    /// Set a single bit.
    fn set_bit(&mut self, bit: usize, value: bool);
}

impl<T: BitRange<u8>> Bit for T {
    fn bit(&self, bit: usize) -> bool {
        self.bit_range(bit, bit) != 0
    }
    fn set_bit(&mut self, bit: usize, value: bool) {
        self.set_bit_range(bit, bit, value as u8);
    }
}

macro_rules! impl_bitrange_for_u {
    ($t:ty, $bitrange_ty:ty) => {
        impl BitRange<$bitrange_ty> for $t {
            #[inline]
            #[allow(unknown_lints)]
            #[allow(cast_lossless)]
            fn bit_range(&self, msb: usize, lsb: usize) -> $bitrange_ty {
                let bit_len = size_of::<$t>()*8;
                let result_bit_len = size_of::<$bitrange_ty>()*8;
                let result = ((*self << (bit_len - msb - 1)) >> (bit_len - msb - 1 + lsb))
                    as $bitrange_ty;
                result << (result_bit_len - (msb - lsb + 1)) >> (result_bit_len - (msb - lsb + 1))
            }

            #[inline]
            #[allow(unknown_lints)]
            #[allow(cast_lossless)]
            fn set_bit_range(&mut self, msb: usize, lsb: usize, value: $bitrange_ty) {
                let bit_len = size_of::<$t>()*8;
                let mask: $t = !(0 as $t)
                    << (bit_len - msb - 1)
                    >> (bit_len - msb - 1 + lsb)
                    << (lsb);
                *self &= !mask;
                *self |= (value as $t << lsb) & mask;
            }
        }
    }
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

// Same as std::stringify but callable from local_inner_macros macros defined inside
// this crate.
#[macro_export]
#[doc(hidden)]
macro_rules! __bitfield_stringify {
    ($s:ident) => {
        stringify!($s)
    };
}

// Same as std::debug_assert but callable from local_inner_macros macros defined inside
// this crate.
#[macro_export]
#[doc(hidden)]
macro_rules! __bitfield_debug_assert {
    ($e:expr) => {
        debug_assert!($e)
    };
}
