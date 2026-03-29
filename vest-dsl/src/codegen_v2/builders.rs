use proc_macro2::TokenStream;
use quote::quote;

pub(super) fn build_right_nested_tokens<F>(
    items: &[TokenStream],
    empty: Option<TokenStream>,
    wrap: &F,
) -> TokenStream
where
    F: Fn(&TokenStream, TokenStream) -> TokenStream,
{
    match items {
        [] => empty.expect("right-nested token builder was given an empty sequence"),
        [single] => single.clone(),
        [first, rest @ ..] => wrap(first, build_right_nested_tokens(rest, empty.clone(), wrap)),
    }
}

pub(super) fn build_nested_pair_type(items: &[TokenStream]) -> TokenStream {
    build_right_nested_tokens(items, Some(quote! { () }), &|first, rest| {
        quote! { (#first, #rest) }
    })
}

pub(super) fn build_nested_pair_expr(items: &[TokenStream]) -> TokenStream {
    build_right_nested_tokens(items, Some(quote! { () }), &|first, rest| {
        quote! { (#first, #rest) }
    })
}
