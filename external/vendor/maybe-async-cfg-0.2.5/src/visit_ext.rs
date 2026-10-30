#[allow(unused_imports)]
use std::iter::FromIterator;

#[allow(unused_imports)]
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote;
use syn::{
    visit_mut::{self, VisitMut},
};

////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IdentMode {
    Use,
    Other,
}

pub trait VisitMutExt {
    fn process_attrs(&mut self, _attrs: &mut Vec<syn::Attribute>) -> syn::Result<()> {
        Ok(())
    }
    fn process_ident(&mut self, _ident: &mut syn::Ident, _mode: IdentMode) -> syn::Result<()> {
        Ok(())
    }

    fn process_attribute(&mut self, _node: &mut syn::Attribute) -> syn::Result<()> {
        Ok(())
    }
    fn process_expr(&mut self, _node: &mut syn::Expr) -> syn::Result<()> {
        Ok(())
    }
    fn process_file(&mut self, _node: &mut syn::File) -> syn::Result<()> {
        Ok(())
    }
    fn process_item(&mut self, _node: &mut syn::Item) -> syn::Result<()> {
        Ok(())
    }
    fn process_item_impl(&mut self, _node: &mut syn::ItemImpl) -> syn::Result<()> {
        Ok(())
    }
    fn process_item_trait(&mut self, _node: &mut syn::ItemTrait) -> syn::Result<()> {
        Ok(())
    }
    fn process_item_fn(&mut self, _node: &mut syn::ItemFn) -> syn::Result<()> {
        Ok(())
    }
    fn process_macro(&mut self, _node: &mut syn::Macro) -> syn::Result<()> {
        Ok(())
    }
    fn process_path_segment(&mut self, _node: &mut syn::PathSegment) -> syn::Result<()> {
        Ok(())
    }
    fn process_type_param(&mut self, _node: &mut syn::TypeParam) -> syn::Result<()> {
        Ok(())
    }
    fn process_use_tree(&mut self, _node: &mut syn::UseTree) -> syn::Result<()> {
        Ok(())
    }

    fn after_process_item(&mut self, _node: &mut syn::Item) -> syn::Result<()> {
        Ok(())
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

pub struct Visitor<T> {
    pub inner: T,
//    err: Option<syn::Error>,
}

impl<T> Visitor<T> {
    pub fn new(inner: T) -> Self {
        Self { inner }
    }

    pub fn process(&mut self, item: TokenStream2) -> syn::Result<TokenStream2>
    where
        Self: VisitMutExt,
    {
        let mut syntax_tree: syn::File = syn::parse(item.into())?;
        self.visit_file_mut(&mut syntax_tree);
        let ts = quote!(#syntax_tree);

        Ok(ts)
    }
}



////////////////////////////////////////////////////////////////////////////////////////////////////

macro_rules! impl_fn {
    (@expr $value:expr, value) => {
        $value
    };
    (@expr $value:expr, (_, value)) => {
        &mut $value.1
    };
    (@func $self:expr, $node:ident, $proc:ident(node $(.$path:ident)? as Some($expr:tt) $(, $mode:expr)?) ) => {
        if let Some(value) = impl_fn!(@arg $node $(.$path)?) {
            $self.$proc( impl_fn!(@expr value, $expr) $(, $mode)? ).unwrap();
        };
    };
    (@func $self:expr, $node:ident, $proc:ident(node $(.$path:ident)? $(, $mode:expr)?) ) => {
        $self.$proc( impl_fn!(@arg $node $(.$path)?) $(, $mode)? ).unwrap();
    };
    (@funcs $self:expr, $node:ident, { $($proc:ident $params:tt ;)+ } ) => {
        $(
            impl_fn!(@func $self, $node, $proc $params);
        )+
    };
    (@arg $node:ident $(.$path:ident)+) => {
        &mut $node $(.$path)+
    };
    (@arg $node:ident) => {
        $node
    };
    ($name:ident, $ty:ty, ) => {
        fn $name(&mut self, node: &mut $ty) {
            visit_mut::$name(self, node);
        }
    };
    ($name:ident, $ty:ty, $before:tt) => {
        fn $name(&mut self, node: &mut $ty) {
            impl_fn!(@funcs self, node, $before);

            visit_mut::$name(self, node);
        }
    };
    ($name:ident, $ty:ty, $before:tt, $after:tt) => {
        fn $name(&mut self, node: &mut $ty) {
            impl_fn!(@funcs self, node, $before);

            visit_mut::$name(self, node);

            impl_fn!(@funcs self, node, $after);
        }
    };
}

#[rustfmt::skip]
impl<T> VisitMut for Visitor<T> where Self: VisitMutExt,
{
    impl_fn!(visit_abi_mut,                 syn::Abi,               );
    impl_fn!(visit_angle_bracketed_generic_arguments_mut,   
                                            syn::AngleBracketedGenericArguments,    
                                                                    );
    impl_fn!(visit_arm_mut,                 syn::Arm,               { process_attrs(node.attrs); });
    impl_fn!(visit_attr_style_mut,          syn::AttrStyle,         );
    impl_fn!(visit_attribute_mut,           syn::Attribute,         { process_attribute(node); });
    impl_fn!(visit_bare_fn_arg_mut,         syn::BareFnArg,         { process_attrs(node.attrs); });
    impl_fn!(visit_bin_op_mut,              syn::BinOp,             );
    impl_fn!(visit_binding_mut,             syn::Binding,           { process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_block_mut,               syn::Block,             );
    impl_fn!(visit_bound_lifetimes_mut,     syn::BoundLifetimes,    );
    impl_fn!(visit_const_param_mut,         syn::ConstParam,        { process_attrs(node.attrs); });
    impl_fn!(visit_constraint_mut,          syn::Constraint,        );
    impl_fn!(visit_data_mut,                syn::Data,              );
    impl_fn!(visit_data_enum_mut,           syn::DataEnum,          );
    impl_fn!(visit_data_struct_mut,         syn::DataStruct,        );
    impl_fn!(visit_data_union_mut,          syn::DataUnion,         );
    impl_fn!(visit_derive_input_mut,        syn::DeriveInput,       { process_attrs(node.attrs); });
    impl_fn!(visit_expr_mut,                syn::Expr,              { process_expr(node); });
    impl_fn!(visit_expr_array_mut,          syn::ExprArray,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_assign_mut,         syn::ExprAssign,        { process_attrs(node.attrs); });
    impl_fn!(visit_expr_assign_op_mut,      syn::ExprAssignOp,      { process_attrs(node.attrs); });
    impl_fn!(visit_expr_async_mut,          syn::ExprAsync,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_await_mut,          syn::ExprAwait,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_binary_mut,         syn::ExprBinary,        { process_attrs(node.attrs); });
    impl_fn!(visit_expr_block_mut,          syn::ExprBlock,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_box_mut,            syn::ExprBox,           { process_attrs(node.attrs); });
    impl_fn!(visit_expr_break_mut,          syn::ExprBreak,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_call_mut,           syn::ExprCall,          { process_attrs(node.attrs); });
    impl_fn!(visit_expr_cast_mut,           syn::ExprCast,          { process_attrs(node.attrs); });
    impl_fn!(visit_expr_closure_mut,        syn::ExprClosure,       { process_attrs(node.attrs); });
    impl_fn!(visit_expr_continue_mut,       syn::ExprContinue,      { process_attrs(node.attrs); });
    impl_fn!(visit_expr_field_mut,          syn::ExprField,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_for_loop_mut,       syn::ExprForLoop,       { process_attrs(node.attrs); });
    impl_fn!(visit_expr_group_mut,          syn::ExprGroup,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_if_mut,             syn::ExprIf,            { process_attrs(node.attrs); });
    impl_fn!(visit_expr_index_mut,          syn::ExprIndex,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_let_mut,            syn::ExprLet,           { process_attrs(node.attrs); });
    impl_fn!(visit_expr_lit_mut,            syn::ExprLit,           { process_attrs(node.attrs); });
    impl_fn!(visit_expr_loop_mut,           syn::ExprLoop,          { process_attrs(node.attrs); });
    impl_fn!(visit_expr_macro_mut,          syn::ExprMacro,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_match_mut,          syn::ExprMatch,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_method_call_mut,    syn::ExprMethodCall,    { process_attrs(node.attrs); });
    impl_fn!(visit_expr_paren_mut,          syn::ExprParen,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_path_mut,           syn::ExprPath,          { process_attrs(node.attrs); });
    impl_fn!(visit_expr_range_mut,          syn::ExprRange,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_reference_mut,      syn::ExprReference,     { process_attrs(node.attrs); });
    impl_fn!(visit_expr_repeat_mut,         syn::ExprRepeat,        { process_attrs(node.attrs); });
    impl_fn!(visit_expr_return_mut,         syn::ExprReturn,        { process_attrs(node.attrs); });
    impl_fn!(visit_expr_struct_mut,         syn::ExprStruct,        { process_attrs(node.attrs); });
    impl_fn!(visit_expr_try_mut,            syn::ExprTry,           { process_attrs(node.attrs); });
    impl_fn!(visit_expr_try_block_mut,      syn::ExprTryBlock,      { process_attrs(node.attrs); });
    impl_fn!(visit_expr_tuple_mut,          syn::ExprTuple,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_type_mut,           syn::ExprType,          { process_attrs(node.attrs); });
    impl_fn!(visit_expr_unary_mut,          syn::ExprUnary,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_unsafe_mut,         syn::ExprUnsafe,        { process_attrs(node.attrs); });
    impl_fn!(visit_expr_while_mut,          syn::ExprWhile,         { process_attrs(node.attrs); });
    impl_fn!(visit_expr_yield_mut,          syn::ExprYield,         { process_attrs(node.attrs); });
    impl_fn!(visit_field_mut,               syn::Field,             { process_attrs(node.attrs); });
    impl_fn!(visit_field_pat_mut,           syn::FieldPat,          { process_attrs(node.attrs); });
    impl_fn!(visit_field_value_mut,         syn::FieldValue,        { process_attrs(node.attrs); });
    impl_fn!(visit_fields_mut,              syn::Fields,            );
    impl_fn!(visit_fields_named_mut,        syn::FieldsNamed,       );
    impl_fn!(visit_fields_unnamed_mut,      syn::FieldsUnnamed,     );
    impl_fn!(visit_file_mut,                syn::File,              { process_attrs(node.attrs); process_file(node); });
    impl_fn!(visit_fn_arg_mut,              syn::FnArg,             );
    impl_fn!(visit_foreign_item_mut,        syn::ForeignItem,       );
    impl_fn!(visit_foreign_item_fn_mut,     syn::ForeignItemFn,     { process_attrs(node.attrs); });
    impl_fn!(visit_foreign_item_macro_mut,  syn::ForeignItemMacro,  { process_attrs(node.attrs); });
    impl_fn!(visit_foreign_item_static_mut, syn::ForeignItemStatic, { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_foreign_item_type_mut,   syn::ForeignItemType,   { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_generic_argument_mut,    syn::GenericArgument,   );
    impl_fn!(visit_generic_method_argument_mut, 
                                            syn::GenericMethodArgument, 
                                                                    );
    impl_fn!(visit_generic_param_mut,       syn::GenericParam,      );
    impl_fn!(visit_generics_mut,            syn::Generics,          );
    impl_fn!(visit_ident_mut,               syn::Ident,             );
    impl_fn!(visit_impl_item_mut,           syn::ImplItem,          );
    impl_fn!(visit_impl_item_const_mut,     syn::ImplItemConst,     { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_impl_item_macro_mut,     syn::ImplItemMacro,     { process_attrs(node.attrs); });
    impl_fn!(visit_impl_item_method_mut,    syn::ImplItemMethod,    { process_attrs(node.attrs); });
    impl_fn!(visit_impl_item_type_mut,      syn::ImplItemType,      { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_index_mut,               syn::Index,             );
    impl_fn!(visit_item_mut,                syn::Item,              { process_item(node); },            { after_process_item(node); });
    impl_fn!(visit_item_const_mut,          syn::ItemConst,         { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_item_enum_mut,           syn::ItemEnum,          { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_item_extern_crate_mut,   syn::ItemExternCrate,   { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); process_ident(node.rename as Some((_, value)), IdentMode::Other); });
    impl_fn!(visit_item_fn_mut,             syn::ItemFn,            { process_attrs(node.attrs); process_item_fn(node); });
    impl_fn!(visit_item_foreign_mod_mut,    syn::ItemForeignMod,    { process_attrs(node.attrs); });
    impl_fn!(visit_item_impl_mut,           syn::ItemImpl,          { process_attrs(node.attrs); process_item_impl(node); });
    impl_fn!(visit_item_macro_mut,          syn::ItemMacro,         { process_attrs(node.attrs); process_ident(node.ident as Some(value), IdentMode::Other); });
    impl_fn!(visit_item_macro2_mut,         syn::ItemMacro2,        { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_item_mod_mut,            syn::ItemMod,           { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_item_static_mut,         syn::ItemStatic,        { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_item_struct_mut,         syn::ItemStruct,        { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_item_trait_mut,          syn::ItemTrait,         { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); process_item_trait(node); });
    impl_fn!(visit_item_trait_alias_mut,    syn::ItemTraitAlias,    { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_item_type_mut,           syn::ItemType,          { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_item_union_mut,          syn::ItemUnion,         { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_item_use_mut,            syn::ItemUse,           { process_attrs(node.attrs); });
    impl_fn!(visit_label_mut,               syn::Label,             );
    impl_fn!(visit_lifetime_mut,            syn::Lifetime,          );
    impl_fn!(visit_lifetime_def_mut,        syn::LifetimeDef,       { process_attrs(node.attrs); });
    impl_fn!(visit_lit_mut,                 syn::Lit,               );
    impl_fn!(visit_lit_bool_mut,            syn::LitBool,           );
    impl_fn!(visit_lit_byte_mut,            syn::LitByte,           );
    impl_fn!(visit_lit_byte_str_mut,        syn::LitByteStr,        );
    impl_fn!(visit_lit_char_mut,            syn::LitChar,           );
    impl_fn!(visit_lit_float_mut,           syn::LitFloat,          );
    impl_fn!(visit_lit_int_mut,             syn::LitInt,            );
    impl_fn!(visit_lit_str_mut,             syn::LitStr,            );
    impl_fn!(visit_local_mut,               syn::Local,             { process_attrs(node.attrs); });
    impl_fn!(visit_macro_mut,               syn::Macro,             { process_macro(node); });
    impl_fn!(visit_macro_delimiter_mut,     syn::MacroDelimiter,    );
    impl_fn!(visit_member_mut,              syn::Member,            );
    impl_fn!(visit_meta_mut,                syn::Meta,              );
    impl_fn!(visit_meta_list_mut,           syn::MetaList,          );
    impl_fn!(visit_meta_name_value_mut,     syn::MetaNameValue,     );
    impl_fn!(visit_method_turbofish_mut,    syn::MethodTurbofish,   );
    impl_fn!(visit_nested_meta_mut,         syn::NestedMeta,        );
    impl_fn!(visit_parenthesized_generic_arguments_mut, 
                                            syn::ParenthesizedGenericArguments, 
                                                                    );
    impl_fn!(visit_pat_mut,                 syn::Pat,               );
    impl_fn!(visit_pat_box_mut,             syn::PatBox,            { process_attrs(node.attrs); });
    impl_fn!(visit_pat_ident_mut,           syn::PatIdent,          { process_attrs(node.attrs); });
    impl_fn!(visit_pat_lit_mut,             syn::PatLit,            { process_attrs(node.attrs); });
    impl_fn!(visit_pat_macro_mut,           syn::PatMacro,          { process_attrs(node.attrs); });
    impl_fn!(visit_pat_or_mut,              syn::PatOr,             { process_attrs(node.attrs); });
    impl_fn!(visit_pat_path_mut,            syn::PatPath,           { process_attrs(node.attrs); });
    impl_fn!(visit_pat_range_mut,           syn::PatRange,          { process_attrs(node.attrs); });
    impl_fn!(visit_pat_reference_mut,       syn::PatReference,      { process_attrs(node.attrs); });
    impl_fn!(visit_pat_rest_mut,            syn::PatRest,           { process_attrs(node.attrs); });
    impl_fn!(visit_pat_slice_mut,           syn::PatSlice,          { process_attrs(node.attrs); });
    impl_fn!(visit_pat_struct_mut,          syn::PatStruct,         { process_attrs(node.attrs); });
    impl_fn!(visit_pat_tuple_mut,           syn::PatTuple,          { process_attrs(node.attrs); });
    impl_fn!(visit_pat_tuple_struct_mut,    syn::PatTupleStruct,    { process_attrs(node.attrs); });
    impl_fn!(visit_pat_type_mut,            syn::PatType,           { process_attrs(node.attrs); });
    impl_fn!(visit_pat_wild_mut,            syn::PatWild,           { process_attrs(node.attrs); });
    impl_fn!(visit_path_mut,                syn::Path,              );
    impl_fn!(visit_path_arguments_mut,      syn::PathArguments,     );
    impl_fn!(visit_path_segment_mut,        syn::PathSegment,       { process_path_segment(node); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_predicate_eq_mut,        syn::PredicateEq,       );
    impl_fn!(visit_predicate_lifetime_mut,  syn::PredicateLifetime, );
    impl_fn!(visit_predicate_type_mut,      syn::PredicateType,     );
    impl_fn!(visit_qself_mut,               syn::QSelf,             );
    impl_fn!(visit_range_limits_mut,        syn::RangeLimits,       );
    impl_fn!(visit_receiver_mut,            syn::Receiver,          { process_attrs(node.attrs); });
    impl_fn!(visit_return_type_mut,         syn::ReturnType,        );
    impl_fn!(visit_signature_mut,           syn::Signature,         { process_ident(node.ident, IdentMode::Other); } );
    impl_fn!(visit_span_mut,                Span,                   );
    impl_fn!(visit_stmt_mut,                syn::Stmt,              );
    impl_fn!(visit_trait_bound_mut,         syn::TraitBound,        );
    impl_fn!(visit_trait_bound_modifier_mut,syn::TraitBoundModifier,);
    impl_fn!(visit_trait_item_mut,          syn::TraitItem,         );
    impl_fn!(visit_trait_item_const_mut,    syn::TraitItemConst,    { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_trait_item_macro_mut,    syn::TraitItemMacro,    { process_attrs(node.attrs); });
    impl_fn!(visit_trait_item_method_mut,   syn::TraitItemMethod,   { process_attrs(node.attrs); });
    impl_fn!(visit_trait_item_type_mut,     syn::TraitItemType,     { process_attrs(node.attrs); process_ident(node.ident, IdentMode::Other); });
    impl_fn!(visit_type_mut,                syn::Type,              );
    impl_fn!(visit_type_array_mut,          syn::TypeArray,         );
    impl_fn!(visit_type_bare_fn_mut,        syn::TypeBareFn,        );
    impl_fn!(visit_type_group_mut,          syn::TypeGroup,         );
    impl_fn!(visit_type_impl_trait_mut,     syn::TypeImplTrait,     );
    impl_fn!(visit_type_infer_mut,          syn::TypeInfer,         );
    impl_fn!(visit_type_macro_mut,          syn::TypeMacro,         );
    impl_fn!(visit_type_never_mut,          syn::TypeNever,         );
    impl_fn!(visit_type_param_mut,          syn::TypeParam,         { process_attrs(node.attrs); process_type_param(node); });
    impl_fn!(visit_type_param_bound_mut,    syn::TypeParamBound,    );
    impl_fn!(visit_type_paren_mut,          syn::TypeParen,         );
    impl_fn!(visit_type_path_mut,           syn::TypePath,          );
    impl_fn!(visit_type_ptr_mut,            syn::TypePtr,           );
    impl_fn!(visit_type_reference_mut,      syn::TypeReference,     );
    impl_fn!(visit_type_slice_mut,          syn::TypeSlice,         );
    impl_fn!(visit_type_trait_object_mut,   syn::TypeTraitObject,   );
    impl_fn!(visit_type_tuple_mut,          syn::TypeTuple,         );
    impl_fn!(visit_un_op_mut,               syn::UnOp,              );
    impl_fn!(visit_use_glob_mut,            syn::UseGlob,           );
    impl_fn!(visit_use_group_mut,           syn::UseGroup,          );
    impl_fn!(visit_use_name_mut,            syn::UseName,           { process_ident(node.ident, IdentMode::Use); });
    impl_fn!(visit_use_path_mut,            syn::UsePath,           { process_ident(node.ident, IdentMode::Use); });
    impl_fn!(visit_use_rename_mut,          syn::UseRename,         { process_ident(node.ident, IdentMode::Use); process_ident(node.rename, IdentMode::Use); });
    impl_fn!(visit_use_tree_mut,            syn::UseTree,           { process_use_tree(node); });
    impl_fn!(visit_variadic_mut,            syn::Variadic,          { process_attrs(node.attrs); });
    impl_fn!(visit_variant_mut,             syn::Variant,           { process_attrs(node.attrs); });
    impl_fn!(visit_vis_crate_mut,           syn::VisCrate,          );
    impl_fn!(visit_vis_public_mut,          syn::VisPublic,         );
    impl_fn!(visit_vis_restricted_mut,      syn::VisRestricted,     );
    impl_fn!(visit_visibility_mut,          syn::Visibility,        );
    impl_fn!(visit_where_clause_mut,        syn::WhereClause,       );
    impl_fn!(visit_where_predicate_mut,     syn::WherePredicate,    );

}
