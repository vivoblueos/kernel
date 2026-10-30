#![cfg_attr(not(feature = "std"), allow(internal_features))]
#![cfg_attr(not(feature = "std"), feature(lang_items, start))]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg_attr(not(feature = "std"), start)]
fn start(_argc: isize, _argv: *const *const u8) -> isize {
    0
}

use docsplay::Display;

/// this type is pretty swell
#[derive(Display)]
#[prefix_enum_doc_attributes]
enum TestType {
    /// this variant is too
    Variant1,

    /// this variant is two
    Variant2,
}

static_assertions::assert_impl_all!(TestType: core::fmt::Display);

#[cfg(feature = "std")]
fn main() {}
