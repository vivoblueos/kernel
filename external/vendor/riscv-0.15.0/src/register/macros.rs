/// Convenience macro to wrap the `csrrs` assembly instruction for reading a CSR register.
///
/// This macro should generally not be called directly.
///
/// Instead, use the [read_csr_as](crate::read_csr_as) or [read_csr_as_usize](crate::read_csr_as_usize) macros.
#[macro_export]
macro_rules! read_csr {
    ($csr_number:literal) => {
        $crate::read_csr!($csr_number, any(target_arch = "riscv32", target_arch = "riscv64"));
    };
    ($csr_number:literal, $($cfg:meta),*) => {
        /// Reads the CSR.
        ///
        /// **WARNING**: panics on non-`riscv` targets.
        #[inline(always)]
        unsafe fn _read() -> usize {
            _try_read().unwrap()
        }

        /// Attempts to read the CSR.
        #[inline(always)]
        unsafe fn _try_read() -> $crate::result::Result<usize> {
            match () {
                #[cfg($($cfg),*)]
                () => {
                    let r: usize;
                    core::arch::asm!(concat!("csrrs {0}, ", stringify!($csr_number), ", x0"), out(reg) r);
                    Ok(r)
                }
                #[cfg(not($($cfg),*))]
                () => Err($crate::result::Error::Unimplemented),
            }
        }
    };
}

/// `RV32`: Convenience macro to wrap the `csrrs` assembly instruction for reading a CSR register.
///
/// This macro should generally not be called directly.
///
/// Instead, use the [read_csr_as_rv32](crate::read_csr_as_rv32) or [read_csr_as_usize_rv32](crate::read_csr_as_usize_rv32) macros.
#[macro_export]
macro_rules! read_csr_rv32 {
    ($csr_number:literal) => {
        $crate::read_csr!($csr_number, target_arch = "riscv32");
    };
}

/// Convenience macro to read a CSR register value as a `register` type.
///
/// The `register` type must be a defined type in scope of the macro call.
#[macro_export]
macro_rules! read_csr_as {
    ($register:ident, $csr_number:literal) => {
        $crate::read_csr_as!($register, $csr_number, any(target_arch = "riscv32", target_arch = "riscv64"));
    };
    ($register:ident, $csr_number:literal, $sentinel:tt) => {
        $crate::read_csr_as!($register, $csr_number, $sentinel, any(target_arch = "riscv32", target_arch = "riscv64"));
    };

    (base $register:ident, $csr_number:literal, $($cfg:meta),*) => {
        $crate::read_csr!($csr_number, $($cfg),*);

        /// Reads the CSR.
        ///
        /// **WARNING**: panics on non-`riscv` targets.
        #[inline]
        pub fn read() -> $register {
            $register {
                bits: unsafe { _read() },
            }
        }
    };

    ($register:ident, $csr_number:literal, $($cfg:meta),*) => {
        $crate::read_csr_as!(base $register, $csr_number, $($cfg),*);

        /// Attempts to reads the CSR.
        #[inline]
        pub fn try_read() -> $crate::result::Result<$register> {
            Ok($register {
                bits: unsafe { _try_read()? },
            })
        }
    };

    ($register:ident, $csr_number:literal, $sentinel:tt, $($cfg:meta),*) => {
        $crate::read_csr_as!(base $register, $csr_number, $($cfg),*);

        /// Attempts to reads the CSR.
        #[inline]
        pub fn try_read() -> $crate::result::Result<$register> {
            match unsafe { _try_read()? } {
                $sentinel => Err($crate::result::Error::Unimplemented),
                bits => Ok($register { bits }),
            }
        }
    };
}

/// `RV32`: Convenience macro to read a CSR register value as a `register` type.
///
/// The `register` type must be a defined type in scope of the macro call.
#[macro_export]
macro_rules! read_csr_as_rv32 {
    ($register:ident, $csr_number:literal) => {
        $crate::read_csr_as!($register, $csr_number, target_arch = "riscv32");
    };
}

/// Convenience macro to read a CSR register value as a [`usize`].
#[macro_export]
macro_rules! read_csr_as_usize {
    ($csr_number:literal) => {
        $crate::read_csr_as_usize!($csr_number, any(target_arch = "riscv32", target_arch = "riscv64"));
    };
    ($csr_number:literal, $($cfg:meta),*) => {
        $crate::read_csr!($csr_number, $($cfg),*);

        /// Reads the CSR.
        ///
        /// **WARNING**: panics on non-`riscv` targets.
        #[inline]
        pub fn read() -> usize {
            unsafe { _read() }
        }

        /// Attempts to read the CSR.
        #[inline]
        pub fn try_read() -> $crate::result::Result<usize> {
            unsafe { _try_read() }
        }
    };
}

/// `RV32`: Convenience macro to read a CSR register value as a [`usize`].
#[macro_export]
macro_rules! read_csr_as_usize_rv32 {
    ($csr_number:literal) => {
        $crate::read_csr_as_usize!($csr_number, target_arch = "riscv32");
    };
}

/// Convenience macro to wrap the `csrrw` assembly instruction for writing to CSR registers.
///
/// This macro should generally not be called directly.
///
/// Instead, use the [write_csr_as_usize](crate::write_csr_as_usize) macro.
#[macro_export]
macro_rules! write_csr {
    ($csr_number:literal) => {
        $crate::write_csr!($csr_number, any(target_arch = "riscv32", target_arch = "riscv64"));
    };
    ($csr_number:literal, $($cfg:meta),*) => {
        /// Writes the CSR.
        ///
        /// **WARNING**: panics on non-`riscv` targets.
        #[inline(always)]
        unsafe fn _write(bits: usize) {
            _try_write(bits).unwrap();
        }

        /// Attempts to write the CSR.
        #[inline(always)]
        #[cfg_attr(not($($cfg),*), allow(unused_variables))]
        unsafe fn _try_write(bits: usize) -> $crate::result::Result<()> {
            match () {
                #[cfg($($cfg),*)]
                () => {
                    core::arch::asm!(concat!("csrrw x0, ", stringify!($csr_number), ", {0}"), in(reg) bits);
                    Ok(())
                }
                #[cfg(not($($cfg),*))]
                () => Err($crate::result::Error::Unimplemented),
            }
        }
    };
}

/// `RV32`: Convenience macro to wrap the `csrrw` assembly instruction for writing to CSR registers.
///
/// This macro should generally not be called directly.
///
/// Instead, use the [write_csr_as_usize_rv32](crate::write_csr_as_usize_rv32) macro.
#[macro_export]
macro_rules! write_csr_rv32 {
    ($csr_number:literal) => {
        $crate::write_csr!($csr_number, target_arch = "riscv32");
    };
}

/// Convenience macro to write a value with `bits` to a CSR
#[macro_export]
macro_rules! write_csr_as {
    ($csr_type:ty, $csr_number:literal) => {
        $crate::write_csr_as!($csr_type, $csr_number, any(target_arch = "riscv32", target_arch = "riscv64"));
    };
    (safe $csr_type:ty, $csr_number:literal) => {
        $crate::write_csr_as!(safe $csr_type, $csr_number, any(target_arch = "riscv32", target_arch = "riscv64"));
    };
    ($csr_type:ty, $csr_number:literal, $($cfg:meta),*) => {
        $crate::write_csr!($csr_number, $($cfg),*);

        /// Writes the CSR.
        ///
        /// **WARNING**: panics on non-`riscv` targets.
        #[inline]
        pub unsafe fn write(value: $csr_type) {
            _write(value.bits);
        }

        /// Attempts to write the CSR.
        #[inline]
        pub unsafe fn try_write(value: $csr_type) -> $crate::result::Result<()> {
            _try_write(value.bits)
        }
    };
    (safe $csr_type:ty, $csr_number:literal, $($cfg:meta),*) => {
        $crate::write_csr!($csr_number, $($cfg),*);

        /// Writes the CSR.
        ///
        /// **WARNING**: panics on non-`riscv` targets.
        #[inline]
        pub fn write(value: $csr_type) {
            unsafe { _write(value.bits) }
        }

        /// Attempts to write the CSR.
        #[inline]
        pub fn try_write(value: $csr_type) -> $crate::result::Result<()> {
            unsafe { _try_write(value.bits) }
        }
    };
}

/// Convenience macro to write a value to a CSR register.
#[macro_export]
macro_rules! write_csr_as_rv32 {
    ($csr_type:ty, $csr_number:literal) => {
        $crate::write_csr_as!($csr_type, $csr_number, target_arch = "riscv32");
    };
    (safe $csr_type:ty, $csr_number:literal) => {
        $crate::write_csr_as!(safe $csr_type, $csr_number, target_arch = "riscv32");
    };
}

/// Convenience macro to write a [`usize`] value to a CSR register.
#[macro_export]
macro_rules! write_csr_as_usize {
    ($csr_number:literal) => {
        $crate::write_csr_as_usize!($csr_number, any(target_arch = "riscv32", target_arch = "riscv64"));
    };
    (safe $csr_number:literal) => {
        $crate::write_csr_as_usize!(safe $csr_number, any(target_arch = "riscv32", target_arch = "riscv64"));
    };
    ($csr_number:literal, $($cfg:meta),*) => {
        $crate::write_csr!($csr_number, $($cfg),*);

        /// Writes the CSR.
        ///
        /// **WARNING**: panics on non-`riscv` targets.
        #[inline]
        pub unsafe fn write(bits: usize) {
            _write(bits);
        }

        /// Attempts to write the CSR.
        #[inline]
        pub unsafe fn try_write(bits: usize) -> $crate::result::Result<()> {
            _try_write(bits)
        }
    };
    (safe $csr_number:literal, $($cfg:meta),*) => {
        $crate::write_csr!($csr_number, $($cfg),*);

        /// Writes the CSR.
        ///
        /// **WARNING**: panics on non-`riscv` targets.
        #[inline]
        pub fn write(bits: usize) {
            unsafe { _write(bits) }
        }

        /// Attempts to write the CSR.
        #[inline]
        pub fn try_write(bits: usize) -> $crate::result::Result<()> {
            unsafe { _try_write(bits) }
        }
    };
}

/// `RV32`: Convenience macro to write a [`usize`] value to a CSR register.
#[macro_export]
macro_rules! write_csr_as_usize_rv32 {
    ($csr_number:literal) => {
        $crate::write_csr_as_usize!($csr_number, target_arch = "riscv32");
    };
    (safe $csr_number:literal) => {
        $crate::write_csr_as_usize!(safe $csr_number, target_arch = "riscv32");
    };
}

/// Convenience macro around the `csrrs` assembly instruction to set the CSR register.
///
/// This macro is intended for use with the [set_csr](crate::set_csr) or [set_clear_csr](crate::set_clear_csr) macros.
#[macro_export]
macro_rules! set {
    ($csr_number:literal) => {
        $crate::set!($csr_number, any(target_arch = "riscv32", target_arch = "riscv64"));
    };
    ($csr_number:literal, $($cfg:meta),*) => {
        /// Set the CSR.
        ///
        /// **WARNING**: panics on non-`riscv` targets.
        #[inline(always)]
        unsafe fn _set(bits: usize) {
            _try_set(bits).unwrap();
        }

        /// Attempts to set the CSR.
        #[inline(always)]
        #[cfg_attr(not($($cfg),*), allow(unused_variables))]
        unsafe fn _try_set(bits: usize) -> $crate::result::Result<()> {
            match () {
                #[cfg($($cfg),*)]
                () => {
                    core::arch::asm!(concat!("csrrs x0, ", stringify!($csr_number), ", {0}"), in(reg) bits);
                    Ok(())
                }
                #[cfg(not($($cfg),*))]
                () => Err($crate::result::Error::Unimplemented),
            }
        }
    };
}

/// `RV32`: Convenience macro around the `csrrs` assembly instruction to set the CSR register.
///
/// This macro is intended for use with the [set_csr](crate::set_csr) or [set_clear_csr](crate::set_clear_csr) macros.
#[macro_export]
macro_rules! set_rv32 {
    ($csr_number:literal) => {
        $crate::set!($csr_number, target_arch = "riscv32");
    };
}

/// Convenience macro around the `csrrc` assembly instruction to clear the CSR register.
///
/// This macro is intended for use with the [clear_csr](crate::clear_csr) or [set_clear_csr](crate::set_clear_csr) macros.
#[macro_export]
macro_rules! clear {
    ($csr_number:literal) => {
        $crate::clear!($csr_number, any(target_arch = "riscv32", target_arch = "riscv64"));
    };
    ($csr_number:literal, $($cfg:meta),*) => {
        /// Clear the CSR.
        ///
        /// **WARNING**: panics on non-`riscv` targets.
        #[inline(always)]
        unsafe fn _clear(bits: usize) {
            _try_clear(bits).unwrap();
        }

        /// Attempts to clear the CSR.
        #[inline(always)]
        #[cfg_attr(not($($cfg),*), allow(unused_variables))]
        unsafe fn _try_clear(bits: usize) -> $crate::result::Result<()> {
            match () {
                #[cfg($($cfg),*)]
                () => {
                    core::arch::asm!(concat!("csrrc x0, ", stringify!($csr_number), ", {0}"), in(reg) bits);
                    Ok(())
                }
                #[cfg(not($($cfg),*))]
                () => Err($crate::result::Error::Unimplemented),
            }
        }
    };
}

/// `RV32`: Convenience macro around the `csrrc` assembly instruction to clear the CSR register.
///
/// This macro is intended for use with the [clear_csr](crate::clear_csr) or [set_clear_csr](crate::set_clear_csr) macros.
#[macro_export]
macro_rules! clear_rv32 {
    ($csr_number:literal) => {
        $crate::clear!($csr_number, target_arch = "riscv32");
    };
}

/// Convenience macro to define field setter functions for a CSR type.
#[macro_export]
macro_rules! set_csr {
    ($(#[$attr:meta])*, $set_field:ident, $e:expr) => {
        $(#[$attr])*
        #[inline]
        pub unsafe fn $set_field() {
            _set($e);
        }
    };
}

/// Convenience macro to define field clear functions for a CSR type.
#[macro_export]
macro_rules! clear_csr {
    ($(#[$attr:meta])*, $clear_field:ident, $e:expr) => {
        $(#[$attr])*
        #[inline]
        pub unsafe fn $clear_field() {
            _clear($e);
        }
    };
}

/// Convenience macro to define field setter and clear functions for a CSR type.
#[macro_export]
macro_rules! set_clear_csr {
    ($(#[$attr:meta])*, $set_field:ident, $clear_field:ident, $e:expr) => {
        $crate::set_csr!($(#[$attr])*, $set_field, $e);
        $crate::clear_csr!($(#[$attr])*, $clear_field, $e);
    }
}

/// Convenience macro to read a composite value from a CSR register.
///
/// - `RV32`: reads 32-bits from `hi` and 32-bits from `lo` to create a 64-bit value
/// - `RV64`: reads a 64-bit value from `lo`
#[macro_export]
macro_rules! read_composite_csr {
    ($hi:expr, $lo:expr) => {
        /// Reads the CSR as a 64-bit value
        #[inline]
        pub fn read64() -> u64 {
            match () {
                #[cfg(target_arch = "riscv32")]
                () => loop {
                    let hi = $hi;
                    let lo = $lo;
                    if hi == $hi {
                        return ((hi as u64) << 32) | lo as u64;
                    }
                },

                #[cfg(not(target_arch = "riscv32"))]
                () => $lo as u64,
            }
        }
    };
}

/// Convenience macro to write a composite value to a CSR register.
///
/// - `RV32`: writes 32-bits into `hi` and 32-bits into `lo` to create a 64-bit value
/// - `RV64`: writes a 64-bit value into `lo`
#[macro_export]
macro_rules! write_composite_csr {
    ($hi:expr, $lo:expr) => {
        /// Writes the CSR as a 64-bit value
        #[inline]
        pub unsafe fn write64(bits: u64) {
            match () {
                #[cfg(target_arch = "riscv32")]
                () => {
                    $hi((bits >> 32) as usize);
                    $lo(bits as usize);
                }

                #[cfg(not(target_arch = "riscv32"))]
                () => $lo(bits as usize),
            }
        }
    };
}

macro_rules! set_pmp {
    () => {
        /// Set the pmp configuration corresponding to the index.
        ///
        /// **WARNING**: panics on non-`riscv` targets, and/or if `index` is out-of-bounds.
        #[inline]
        pub unsafe fn set_pmp(index: usize, range: Range, permission: Permission, locked: bool) {
            try_set_pmp(index, range, permission, locked).unwrap()
        }

        /// Attempts to set the pmp configuration corresponding to the index.
        ///
        /// Returns an error if the index is invalid.
        #[inline]
        pub unsafe fn try_set_pmp(
            index: usize,
            range: Range,
            permission: Permission,
            locked: bool,
        ) -> $crate::result::Result<()> {
            let max = match () {
                #[cfg(target_arch = "riscv32")]
                () => Ok(4usize),
                #[cfg(target_arch = "riscv64")]
                () => Ok(8usize),
                #[cfg(not(any(target_arch = "riscv32", target_arch = "riscv64")))]
                () => Err($crate::result::Error::Unimplemented),
            }?;

            if index < max {
                let mut value = _try_read()?;
                value &= !(0xFF << (8 * index)); // clear previous value
                let byte = (locked as usize) << 7 | (range as usize) << 3 | (permission as usize);
                value |= byte << (8 * index);
                _try_write(value)
            } else {
                Err($crate::result::Error::IndexOutOfBounds {
                    index,
                    min: 0,
                    max: max - 1,
                })
            }
        }
    };
}

macro_rules! clear_pmp {
    () => {
        /// Clear the pmp configuration corresponding to the index.
        ///
        /// **WARNING**: panics on non-`riscv` targets, and/or if `index` is out-of-bounds.
        #[inline]
        pub unsafe fn clear_pmp(index: usize) {
            try_clear_pmp(index).unwrap();
        }

        /// Attempts to clear the pmp configuration corresponding to the index.
        ///
        /// Returns an error if the index is invalid.
        #[inline]
        pub unsafe fn try_clear_pmp(index: usize) -> $crate::result::Result<()> {
            let max = match () {
                #[cfg(target_arch = "riscv32")]
                () => Ok(4usize),
                #[cfg(target_arch = "riscv64")]
                () => Ok(8usize),
                #[cfg(not(any(target_arch = "riscv32", target_arch = "riscv64")))]
                () => Err($crate::result::Error::Unimplemented),
            }?;

            if index < max {
                let mut value = _try_read()?;
                value &= !(0xFF << (8 * index)); // clear previous value
                _try_write(value)
            } else {
                Err($crate::result::Error::IndexOutOfBounds {
                    index,
                    min: 0,
                    max: max - 1,
                })
            }
        }
    };
}

/// Helper macro to define a CSR type.
///
/// This macro creates a type represents a CSR register, without defining any bitfields.
///
/// It is mainly used by [read_write_csr](crate::read_write_csr),
/// [read_only_csr](crate::read_only_csr), and [write_only_csr](crate::write_only_csr) macros.
#[macro_export]
macro_rules! csr {
    ($(#[$doc:meta])*
     $ty:ident,
     $mask:expr) => {
        #[repr(C)]
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub struct $ty {
            bits: usize,
        }

        impl $ty {
            /// Bitmask for legal bitfields of the CSR type.
            pub const BITMASK: usize = $mask;

            /// Creates a new CSR type from raw bits value.
            ///
            /// Only bits in the [BITMASK](Self::BITMASK) will be set.
            pub const fn from_bits(bits: usize) -> Self {
                Self { bits: bits & $mask }
            }

            /// Gets the raw bits value.
            pub const fn bits(&self) -> usize {
                self.bits & $mask
            }

            /// Gets the bitmask for the CSR type's bitfields.
            pub const fn bitmask(&self) -> usize {
                Self::BITMASK
            }
        }
    };
}

#[macro_export]
macro_rules! csr_field_enum {
    ($(#[$field_ty_doc:meta])*
     $field_ty:ident {
         default: $default_variant:ident,
         $(
             $(#[$field_doc:meta])*
             $variant:ident = $value:expr$(,)?
          )+
     }$(,)?
    ) => {
         $(#[$field_ty_doc])*
         #[repr(usize)]
         #[derive(Clone, Copy, Debug, Eq, PartialEq)]
         pub enum $field_ty {
             $(
                 $(#[$field_doc])*
                 $variant = $value
             ),+
         }

         impl $field_ty {
             /// Creates a new field variant.
             pub const fn new() -> Self {
                 Self::$default_variant
             }

             /// Attempts to convert a [`usize`] into a valid variant.
             pub const fn from_usize(val: usize) -> $crate::result::Result<Self> {
                 match val {
                     $($value => Ok(Self::$variant),)+
                     _ => Err($crate::result::Error::InvalidVariant(val)),
                 }
             }

             /// Converts the variant into a [`usize`].
             pub const fn into_usize(self) -> usize {
                 self as usize
             }
         }

         impl Default for $field_ty {
             fn default() -> Self {
                 Self::new()
             }
         }

         impl From<$field_ty> for usize {
             fn from(val: $field_ty) -> Self {
                 val.into_usize()
             }
         }

         impl TryFrom<usize> for $field_ty {
             type Error = $crate::result::Error;

             fn try_from(val: usize) -> $crate::result::Result<Self> {
                 Self::from_usize(val)
             }
         }
    };
}

/// Helper macro to create a read-write CSR type.
///
/// The type allows to read the CSR value into memory, and update the field values in-memory.
///
/// The user can then write the entire bitfield value back into the CSR with a single write.
#[macro_export]
macro_rules! read_write_csr {
    ($(#[$doc:meta])+
     $ty:ident: $csr:expr,
     mask: $mask:expr$(,)?
    ) => {
        $crate::csr!($(#[$doc])+ $ty, $mask);

        $crate::read_csr_as!($ty, $csr);
        $crate::write_csr_as!($ty, $csr);
    };
}

/// Helper macro to create a read-only CSR type.
///
/// The type allows to read the CSR value into memory.
#[macro_export]
macro_rules! read_only_csr {
    ($(#[$doc:meta])+
     $ty:ident: $csr:expr,
     mask: $mask:expr$(,)?
    ) => {
        $crate::csr! { $(#[$doc])+ $ty, $mask }

        $crate::read_csr_as!($ty, $csr);
    };

    ($(#[$doc:meta])+
     $ty:ident: $csr:expr,
     mask: $mask:expr,
     sentinel: $sentinel:tt$(,)?,
    ) => {
        $crate::csr! { $(#[$doc])+ $ty, $mask }

        $crate::read_csr_as!($ty, $csr, $sentinel);
    };
}

/// Helper macro to create a read-only CSR type.
///
/// The type allows to read the CSR value into memory.
#[macro_export]
macro_rules! write_only_csr {
    ($(#[$doc:meta])+
     $ty:ident: $csr:expr,
     mask: $mask:expr$(,)?
    ) => {
        $crate::csr! { $(#[$doc])+ $ty, $mask }

        $crate::write_csr_as!($ty, $csr);
    };
}

/// Defines field accessor functions for a read-write CSR type.
#[macro_export]
macro_rules! read_write_csr_field {
    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident: $bit:literal$(,)?
     ) => {
         $crate::paste! {
             $crate::read_only_csr_field!(
                 $ty,
                 $(#[$field_doc])+
                 $field: $bit,
             );

             $crate::write_only_csr_field!(
                 $ty,
                 $(#[$field_doc])+
                 [<set_ $field>]: $bit,
             );
         }
    };

    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident: $bit_start:literal ..= $bit_end:literal$(,)?
    ) => {
        $crate::paste! {
            $crate::read_only_csr_field!(
                $ty,
                $(#[$field_doc])+
                $field: $bit_start ..= $bit_end,
            );

            $crate::write_only_csr_field!(
                $ty,
                $(#[$field_doc])+
                [<set_ $field>]: $bit_start ..= $bit_end,
            );
        }
    };

    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident: [$bit_start:literal : $bit_end:literal]$(,)?
    ) => {
        $crate::paste! {
            $crate::read_only_csr_field!(
                $ty,
                $(#[$field_doc])+
                $field: [$bit_start : $bit_end],
            );

            $crate::write_only_csr_field!(
                $ty,
                $(#[$field_doc])+
                [<set_ $field>]: [$bit_start : $bit_end],
            );
        }
    };

    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident,
     $field_ty:ident: [$field_start:literal : $field_end:literal],
    ) => {
        $crate::paste! {
            $crate::read_only_csr_field!(
                $ty,
                $(#[$field_doc])+
                $field,
                $field_ty: [$field_start : $field_end],
            );

            $crate::write_only_csr_field!(
                $ty,
                $(#[$field_doc])+
                [<set_ $field>],
                $field_ty: [$field_start : $field_end],
            );
        }
    };
}

/// Defines field accessor functions for a read-only CSR type.
#[macro_export]
macro_rules! read_only_csr_field {
    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident: $bit:literal$(,)?) => {
        const _: () = assert!($bit < usize::BITS);

        impl $ty {
            $(#[$field_doc])+
            #[inline]
            pub fn $field(&self) -> bool {
                $crate::bits::bf_extract(self.bits, $bit, 1) != 0
            }
        }
    };

    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident: $bit_start:literal..=$bit_end:literal$(,)?) => {
        const _: () = assert!($bit_end < usize::BITS);
        const _: () = assert!($bit_start < $bit_end);

        $crate::paste! {
            impl $ty {
                $(#[$field_doc])+
                #[inline]
                pub fn $field(&self, index: usize) -> bool {
                    self.[<try_ $field>](index).unwrap()
                }

                $(#[$field_doc])+
                #[inline]
                pub fn [<try_ $field>](&self, index: usize) -> $crate::result::Result<bool> {
                    if ($bit_start..=$bit_end).contains(&index) {
                        Ok($crate::bits::bf_extract(self.bits, index, 1) != 0)
                    } else {
                        Err($crate::result::Error::IndexOutOfBounds {
                            index,
                            min: $bit_start,
                            max: $bit_end,
                        })
                    }
                }
            }
        }
    };

    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident: [$bit_start:literal : $bit_end:literal]$(,)?) => {
        const _: () = assert!($bit_end < usize::BITS);
        const _: () = assert!($bit_start < $bit_end);

        impl $ty {
            $(#[$field_doc])+
            #[inline]
            pub fn $field(&self) -> usize {
                $crate::bits::bf_extract(self.bits, $bit_start, $bit_end - $bit_start + 1)
            }
        }
    };

    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident,
     $field_ty:ident: [$field_start:literal : $field_end:literal]$(,)?
    ) => {
        const _: () = assert!($field_end < usize::BITS);
        const _: () = assert!($field_start <= $field_end);

        $crate::paste! {
            impl $ty {
                $(#[$field_doc])+
                #[inline]
                pub fn $field(&self) -> $field_ty {
                    self.[<try_ $field>]().unwrap()
                }

                $(#[$field_doc])+
                #[inline]
                pub fn [<try_ $field>](&self) -> $crate::result::Result<$field_ty> {
                    let value = $crate::bits::bf_extract(
                        self.bits,
                        $field_start,
                        $field_end - $field_start + 1,
                    );

                    $field_ty::from_usize(value)
                }
            }
        }
    };
}

/// Defines field accessor functions for a write-only CSR type.
#[macro_export]
macro_rules! write_only_csr_field {
    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident: $bit:literal$(,)?) => {
        const _: () = assert!($bit < usize::BITS);

        impl $ty {
            $(#[$field_doc])+
            #[doc = ""]
            #[doc = "**NOTE**: only updates in-memory values, does not write to CSR."]
            #[inline]
            pub fn $field(&mut self, $field: bool) {
                self.bits = $crate::bits::bf_insert(self.bits, $bit, 1, $field as usize);
            }
        }
    };

    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident: $bit_start:literal..=$bit_end:literal$(,)?) => {
        const _: () = assert!($bit_end < usize::BITS);
        const _: () = assert!($bit_start < $bit_end);

        $crate::paste! {
            impl $ty {
                $(#[$field_doc])+
                #[doc = ""]
                #[doc = "**NOTE**: only updates in-memory values, does not write to CSR."]
                #[inline]
                pub fn $field(&mut self, index: usize, $field: bool) {
                    self.[<try_ $field>](index, $field).unwrap();
                }

                $(#[$field_doc])+
                #[doc = ""]
                #[doc = "**NOTE**: only updates in-memory values, does not write to CSR."]
                #[inline]
                pub fn [<try_ $field>](&mut self, index: usize, $field: bool) -> $crate::result::Result<()> {
                    if ($bit_start..=$bit_end).contains(&index) {
                        self.bits = $crate::bits::bf_insert(self.bits, index, 1, $field as usize);
                        Ok(())
                    } else {
                        Err($crate::result::Error::IndexOutOfBounds {
                            index,
                            min: $bit_start,
                            max: $bit_end,
                        })
                    }
                }
            }
        }
    };

    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident: [$bit_start:literal : $bit_end:literal]$(,)?) => {
        const _: () = assert!($bit_end < usize::BITS);
        const _: () = assert!($bit_start < $bit_end);

        impl $ty {
            $(#[$field_doc])+
            #[doc = ""]
            #[doc = "**NOTE**: only updates in-memory values, does not write to CSR."]
            #[inline]
            pub fn $field(&mut self, $field: usize) {
                self.bits = $crate::bits::bf_insert(
                    self.bits,
                    $bit_start,
                    $bit_end - $bit_start + 1,
                    $field,
                );
            }
        }
    };

    ($ty:ident,
     $(#[$field_doc:meta])+
     $field:ident,
     $field_ty:ident: [$field_start:literal : $field_end:literal]$(,)?
    ) => {
        const _: () = assert!($field_end < usize::BITS);
        const _: () = assert!($field_start <= $field_end);

        impl $ty {
            $(#[$field_doc])+
            #[doc = ""]
            #[doc = "**NOTE**: only updates in-memory values, does not write to CSR."]
            #[inline]
            pub fn $field(&mut self, $field: $field_ty) {
                self.bits = $crate::bits::bf_insert(
                    self.bits,
                    $field_start,
                    $field_end - $field_start + 1,
                    $field.into(),
                );
            }
        }
    };
}

#[cfg(test)]
#[macro_export]
macro_rules! test_csr_field {
    // test a single bit field
    ($reg:ident, $field:ident) => {{
        $crate::paste! {
            let val = $reg.$field();

            $reg.[<set_ $field>](!val);
            assert_eq!($reg.$field(), !val);

            $reg.[<set_ $field>](val);
            assert_eq!($reg.$field(), val);
        }
    }};

    // test a range bit field (valid)
    ($reg:ident, $field:ident, $index:expr) => {{
        $crate::paste! {
            assert!(!$reg.$field($index));
            assert_eq!($reg.[<try_ $field>]($index), Ok(false));

            $reg.[<set_ $field>]($index, true);
            assert!($reg.$field($index));

            assert_eq!($reg.[<try_set_ $field>]($index, false), Ok(()));
            assert_eq!($reg.[<try_ $field>]($index), Ok(false));

            assert!(!$reg.$field($index));
        }
    }};

    // test a range bit field (invalid)
    ($reg:ident, $field:ident, $index:expr, $err:expr) => {{
        $crate::paste! {
            assert_eq!($reg.[<try_ $field>]($index), Err($err));
            assert_eq!($reg.[<try_set_ $field>]($index, false), Err($err));
        }
    }};

    // test an enum bit field
    ($reg:ident, $field:ident: $var:expr) => {{
        $crate::paste! {
            $reg.[<set_ $field>]($var);
            assert_eq!($reg.$field(), $var);
            assert_eq!($reg.[<try_ $field>](), Ok($var));
        }
    }};

    // test a multi-bit bitfield
    ($reg:ident, $field:ident: [$start:expr, $end:expr], $reset:expr) => {{
        let bits = $reg.bits();

        let shift = $end - $start + 1;
        let mask = (1usize << shift) - 1;

        let exp_val = (bits >> $start) & mask;

        $crate::paste! {
            assert_eq!($reg.$field(), exp_val);

            $reg.[<set_ $field>]($reset);
            assert_eq!($reg.$field(), $reset);

            $reg.[<set_ $field>](exp_val);
            assert_eq!($reg.$field(), exp_val);
        }
    }};
}
