pub use proc_macro2;
use proc_macro2::TokenTree;

#[allow(non_snake_case)]
#[inline(always)]
pub fn assert_impl_IntoIterator_Item_TokenTree(_: &impl IntoIterator<Item = TokenTree>) {}
