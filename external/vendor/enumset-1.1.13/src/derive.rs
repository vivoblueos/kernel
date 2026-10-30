#[cfg(all(doc, feature = "serde"))]
use serde::{Deserialize, Serialize};

#[cfg(doc)]
use crate::EnumSet;

/// The procedural macro used to derive [`EnumSetType`], and allow enums to be used with
/// [`EnumSet`].
///
/// # Limitations
///
/// Currently, the following limitations apply to what kinds of enums this macro may be used with:
///
/// * The enum must have no data fields in any variant.
/// * Explicit variant discriminants must be zero or positive and no larger than
///   `0xFFFFFFBF`(except when `map = "compact"`).
/// * Each explicit discriminant must be a literal, not more general const expressions.
///
/// # Additional Impls
///
/// In addition to the implementation of `EnumSetType`, this procedural macro creates multiple
/// other impls that are either required for the macro to work, or make the procedural macro more
/// ergonomic to use.
///
/// A full list of traits implemented is as follows:
///
/// * [`Copy`], [`Clone`], [`Eq`], [`PartialEq`] implementations are created to allow `EnumSet`
///   to function properly. These automatic implementations may be suppressed using
///   `#[enumset(no_super_impls)]`, but these traits must still be implemented in another way.
/// * [`PartialEq`], [`Sub`], [`BitAnd`], [`BitOr`], [`BitXor`], and [`Not`] implementations are
///   created to allow the crate to be used more ergonomically in expressions. These automatic
///   implementations may be suppressed using `#[enumset(no_ops)]`.
///
/// # Options
///
/// Options are given with `#[enumset(foo)]` annotations attached to the same enum as the derive.
/// Multiple options may be given in the same annotation using the `#[enumset(foo, bar)]` syntax.
///
/// A full list of options available is as follows:
///
/// * `#[enumset(no_super_impls)]` prevents the procedural macro from generating implementations
///   for the supertraits of `EnumSetType`. When this attribute is specified, implementations of
///   [`Copy`], [`Clone`], [`Eq`], and [`PartialEq`] must be provided manually. These impls should
///   function identically to the automatically derived versions, or unintentional behavior may be
///   a result.
/// * `#[enumset(no_ops)]` prevents the procedural macro from implementing any operator traits.
/// * `#[enumset(crate_name = "enumset2")]` may be used to change the name of the `enumset` crate
///   used in the generated code. When the `proc-macro-crate` feature is enabled, enumset parses
///   `Cargo.toml` to determine the name of the crate, and this flag is unnecessary.
/// * `#[enumset(map = "…")]` controls how enum variants are mapped to bits in the `EnumSet`. For
///   more information, see the [Mapping Options](#mapping-options) section.
/// * `#[enumset(repr = "…")]` is used to control the in-memory representation of `EnumSet`s. For
///   more information, see the [Representation Options](#representation-options) section.
///
/// Additional features may be specified when the `serde` feature is enabled. These options are
/// ignored when `serde` is not enabled. For more information, see the
/// [Serialization Options](#serialization-options) section.
///
/// ## Mapping Options
///
/// The following options exist to control how enum variants are mapped to bits in an `EnumSet`:
///
/// * `#[enumset(map = "lsb")]` maps an enum variant with a discriminant of `n` to the `n + 1`th
///   least significant bit of the enumset. If no mapping is specified, this is used by default.
/// * `#[enumset(map = "msb")]` maps an enum variant with a discriminant of `n` to the `n + 1`th
///   most significant bit of the enumset. This requires an explicit integer representation or else
///   compilation will fail.
/// * `#[enumset(map = "compact")]` maps each enum variant to an unspecified bit in the set. This
///   allows the library to use less memory than it may otherwise and allows any discriminant
///   values to be used without issue.
/// * `#[enumset(map = "mask")]` treats each enum variant's discriminant as a mask rather than a
///   bit index. Each discriminant must be a power of two, and may be of arbitrary size.
///
/// ## Representation Options
///
/// The following options exist to control the in-memory representation of an `EnumSet`:
///
/// * `#[enumset(repr = "u…")]` forces the `EnumSet` to use a specific primitive integer type.
///   Allowed types are `u8`, `u16`, `u32`, `u64` and `u128`. This allows the `EnumSet` to be
///   safely used across FFI boundaries. Additionally, the procedural macro will generate an
///   implementation of <code>[EnumSetTypeWithRepr]&lt;Repr = R&gt;</code>.
/// * `#[enumset(repr = "array")]` forces the `EnumSet` of this type to be backed with an array,
///   even if all the variants could fit into a primitive numeric type.
///
/// By default, `enumset` tries to choose the representation most suitable to the type, but no
/// guarantees are made about which it picks.
///
/// [EnumSetTypeWithRepr]: crate::traits::EnumSetTypeWithRepr
///
/// ## Serialization Options
///
/// The following options exist to control how an `EnumSet` is serialized with `serde`:
///
/// * `#[enumset(serialize_repr = "u…")]` causes the set to be serialized as a single integer
///   of the corresponding primitive type.
/// * `#[enumset(serialize_repr = "array")]` causes the set to be serialized as a list of `u64`s
///   corresponding to the [array representation](EnumSet#array-representation) of the set.
/// * `#[enumset(serialize_repr = "list")]` causes the set to be serialized as a list of enum
///   variants. This requires your enum type implement [`Serialize`] and [`Deserialize`].
/// * `#[enumset(serialize_repr = "map")]` causes the set to be serialized as a map of enum
///   variants to booleans. The set contains a value if the boolean is `true`. This requires your
///   enum type implement `Serialize` and `Deserialize`.
/// * `#[enumset(serialize_deny_unknown)]` causes the generated deserializer to return an error
///   for unknown bits instead of silently ignoring them.
///
/// By default, `enumset` uses the smallest integer type that can contain all enum variants or an
/// array if there is no such integer type.
///
/// # Examples
///
/// Deriving a plain `EnumSetType`:
///
/// ```rust
/// # use enumset::*;
/// #[derive(EnumSetType)]
/// pub enum Enum {
///    A, B, C, D, E, F, G,
/// }
/// ```
///
/// Deriving a sparse `EnumSetType`:
///
/// ```rust
/// # use enumset::*;
/// #[derive(EnumSetType)]
/// pub enum SparseEnum {
///    A = 10, B = 20, C = 30, D = 127,
/// }
/// ```
///
/// Deriving an `EnumSetType` without adding ops:
///
/// ```rust
/// # use enumset::*;
/// #[derive(EnumSetType)]
/// #[enumset(no_ops)]
/// pub enum NoOpsEnum {
///    A, B, C, D, E, F, G,
/// }
/// ```
///
/// [`Sub`]: core::ops::Sub
/// [`BitAnd`]: core::ops::BitAnd
/// [`BitOr`]: core::ops::BitOr
/// [`BitXor`]: core::ops::BitXor
/// [`Not`]: core::ops::Not
#[cfg_attr(
    not(feature = "serde"),
    doc = "\n\n",
    doc = "[`Serialize`]: https://docs.rs/serde/latest/serde/trait.Serialize.html\n",
    doc = "[`Deserialize`]: https://docs.rs/serde/latest/serde/trait.Deserialize.html\n"
)]
pub use enumset_derive::EnumSetType;
