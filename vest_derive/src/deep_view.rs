use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use std::collections::BTreeSet;
use syn::spanned::Spanned;
use syn::{
    parse_macro_input, parse_quote, AngleBracketedGenericArguments, Data, DataEnum, DataStruct,
    DeriveInput, Field, Fields, GenericArgument, GenericParam, Generics, Ident, Path,
    PathArguments, Result, Type, TypeParam,
};

pub(crate) fn derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match expand(input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.into_compile_error().into(),
    }
}

fn expand(input: DeriveInput) -> Result<TokenStream2> {
    let runtime_name = input.ident.clone();
    let spec_name = format_ident!("{}Spec", runtime_name);
    let helper_name = format_ident!("__{}_deep_view", to_snake_case(&runtime_name.to_string()));
    let type_params = runtime_type_param_names(&input.generics);

    let spec_generics = spec_generics_from_runtime(&input.generics);
    let spec_item = expand_spec_item(
        &input.vis,
        &spec_name,
        &spec_generics,
        &input.data,
        &type_params,
    )?;

    let mut impl_generics = input.generics.clone();
    add_deep_view_bounds(&mut impl_generics);
    let (impl_generics, ty_generics, where_clause) = impl_generics.split_for_impl();

    let mut helper_generics = input.generics.clone();
    add_deep_view_bounds(&mut helper_generics);
    let helper_generic_params = &helper_generics.params;
    let helper_generic_params = if helper_generic_params.is_empty() {
        quote!()
    } else {
        quote!(<#helper_generic_params>)
    };
    let helper_where_clause = &helper_generics.where_clause;

    let spec_ty = spec_type_for_runtime_item(&spec_name, &input.generics);
    let helper_body = expand_deep_view_body(&runtime_name, &spec_name, &helper_name, &input.data)?;

    Ok(quote! {
        ::vstd::prelude::verus! {
            #spec_item

            pub open spec fn #helper_name #helper_generic_params (
                v: &#runtime_name #ty_generics
            ) -> #spec_ty
            #helper_where_clause
                decreases v,
            {
                #helper_body
            }

            impl #impl_generics ::vstd::prelude::DeepView for #runtime_name #ty_generics #where_clause {
                type V = #spec_ty;

                open spec fn deep_view(&self) -> Self::V {
                    #helper_name(self)
                }
            }
        }
    })
}

fn runtime_type_param_names(generics: &Generics) -> BTreeSet<String> {
    generics
        .type_params()
        .map(|param| param.ident.to_string())
        .collect()
}

fn to_snake_case(name: &str) -> String {
    let mut out = String::new();
    for (i, ch) in name.chars().enumerate() {
        if ch.is_uppercase() {
            if i != 0 {
                out.push('_');
            }
            for lower in ch.to_lowercase() {
                out.push(lower);
            }
        } else {
            out.push(ch);
        }
    }
    out
}

fn add_deep_view_bounds(generics: &mut Generics) {
    let type_param_idents: Vec<_> = generics
        .type_params()
        .map(|type_param| type_param.ident.clone())
        .collect();
    let where_clause = generics.make_where_clause();
    for ident in type_param_idents {
        where_clause
            .predicates
            .push(parse_quote!(#ident: ::vstd::prelude::DeepView));
    }
}

fn spec_generics_from_runtime(generics: &Generics) -> Generics {
    let mut spec_generics = Generics::default();
    for param in &generics.params {
        match param {
            GenericParam::Type(ty) => {
                spec_generics
                    .params
                    .push(GenericParam::Type(TypeParam::from(ty.ident.clone())));
            }
            GenericParam::Const(c) => {
                spec_generics.params.push(GenericParam::Const(c.clone()));
            }
            GenericParam::Lifetime(_) => {}
        }
    }

    if !spec_generics.params.is_empty() {
        spec_generics.lt_token = Some(Default::default());
        spec_generics.gt_token = Some(Default::default());
    }

    spec_generics
}

fn spec_type_for_runtime_item(spec_name: &Ident, generics: &Generics) -> TokenStream2 {
    let args: Vec<_> = generics
        .params
        .iter()
        .filter_map(|param| match param {
            GenericParam::Type(ty) => {
                let ident = &ty.ident;
                Some(quote!(<#ident as ::vstd::prelude::DeepView>::V))
            }
            GenericParam::Const(c) => {
                let ident = &c.ident;
                Some(quote!(#ident))
            }
            GenericParam::Lifetime(_) => None,
        })
        .collect();

    if args.is_empty() {
        quote!(#spec_name)
    } else {
        quote!(#spec_name<#(#args),*>)
    }
}

fn expand_spec_item(
    vis: &syn::Visibility,
    spec_name: &Ident,
    spec_generics: &Generics,
    data: &Data,
    type_params: &BTreeSet<String>,
) -> Result<TokenStream2> {
    match data {
        Data::Struct(data) => expand_spec_struct(vis, spec_name, spec_generics, data, type_params),
        Data::Enum(data) => expand_spec_enum(vis, spec_name, spec_generics, data, type_params),
        Data::Union(data) => Err(syn::Error::new(
            data.union_token.span(),
            "DeepView derive does not support unions",
        )),
    }
}

fn expand_spec_struct(
    vis: &syn::Visibility,
    spec_name: &Ident,
    spec_generics: &Generics,
    data: &DataStruct,
    type_params: &BTreeSet<String>,
) -> Result<TokenStream2> {
    let ty_generics = &spec_generics.params;
    let ty_generics = if ty_generics.is_empty() {
        quote!()
    } else {
        quote!(<#ty_generics>)
    };

    match &data.fields {
        Fields::Named(fields) => {
            let fields = fields
                .named
                .iter()
                .map(|field| spec_named_field(field, type_params))
                .collect::<Result<Vec<_>>>()?;
            Ok(quote! {
                #vis struct #spec_name #ty_generics {
                    #(#fields),*
                }
            })
        }
        Fields::Unnamed(fields) => {
            let fields = fields
                .unnamed
                .iter()
                .map(|field| spec_unnamed_field(field, type_params))
                .collect::<Result<Vec<_>>>()?;
            Ok(quote! {
                #vis struct #spec_name #ty_generics ( #(#fields),* );
            })
        }
        Fields::Unit => Ok(quote! {
            #vis struct #spec_name #ty_generics;
        }),
    }
}

fn expand_spec_enum(
    vis: &syn::Visibility,
    spec_name: &Ident,
    spec_generics: &Generics,
    data: &DataEnum,
    type_params: &BTreeSet<String>,
) -> Result<TokenStream2> {
    let ty_generics = &spec_generics.params;
    let ty_generics = if ty_generics.is_empty() {
        quote!()
    } else {
        quote!(<#ty_generics>)
    };
    let variants = data
        .variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;
            match &variant.fields {
                Fields::Named(fields) => {
                    let fields = fields
                        .named
                        .iter()
                        .map(|field| spec_named_field(field, type_params))
                        .collect::<Result<Vec<_>>>()?;
                    Ok(quote! {
                        #variant_name { #(#fields),* }
                    })
                }
                Fields::Unnamed(fields) => {
                    let fields = fields
                        .unnamed
                        .iter()
                        .map(|field| spec_unnamed_field(field, type_params))
                        .collect::<Result<Vec<_>>>()?;
                    Ok(quote! {
                        #variant_name( #(#fields),* )
                    })
                }
                Fields::Unit => Ok(quote!(#variant_name)),
            }
        })
        .collect::<Result<Vec<_>>>()?;

    Ok(quote! {
        #vis enum #spec_name #ty_generics {
            #(#variants),*
        }
    })
}

fn spec_named_field(field: &Field, type_params: &BTreeSet<String>) -> Result<TokenStream2> {
    let vis = &field.vis;
    let name = field.ident.as_ref().expect("named field");
    let ty = spec_type_for_field(&field.ty, type_params)?;
    Ok(quote!(#vis #name: #ty))
}

fn spec_unnamed_field(field: &Field, type_params: &BTreeSet<String>) -> Result<TokenStream2> {
    let vis = &field.vis;
    let ty = spec_type_for_field(&field.ty, type_params)?;
    Ok(quote!(#vis #ty))
}

fn spec_type_for_field(ty: &Type, type_params: &BTreeSet<String>) -> Result<Type> {
    match ty {
        Type::Reference(reference) => spec_type_for_field(&reference.elem, type_params),
        Type::Slice(slice) => {
            let elem = spec_type_for_field(&slice.elem, type_params)?;
            Ok(parse_quote!(::vstd::prelude::Seq<#elem>))
        }
        Type::Array(array) => {
            let elem = spec_type_for_field(&array.elem, type_params)?;
            Ok(parse_quote!(::vstd::prelude::Seq<#elem>))
        }
        Type::Tuple(tuple) => {
            let elems = tuple
                .elems
                .iter()
                .map(|elem| spec_type_for_field(elem, type_params))
                .collect::<Result<Vec<_>>>()?;
            Ok(parse_quote!((#(#elems),*)))
        }
        Type::Paren(paren) => spec_type_for_field(&paren.elem, type_params),
        Type::Group(group) => spec_type_for_field(&group.elem, type_params),
        Type::Path(path) => spec_type_for_path(path, type_params),
        _ => Err(syn::Error::new(
            ty.span(),
            "DeepView derive does not support this field type yet",
        )),
    }
}

fn spec_type_for_path(type_path: &syn::TypePath, type_params: &BTreeSet<String>) -> Result<Type> {
    if type_path.qself.is_some() {
        return Err(syn::Error::new(
            type_path.span(),
            "DeepView derive does not support qualified self types",
        ));
    }

    let path = &type_path.path;
    let last = path.segments.last().expect("path segment");
    let ident = last.ident.to_string();

    if path.segments.len() == 1 && last.arguments.is_empty() && type_params.contains(&ident) {
        let ident = &last.ident;
        return Ok(parse_quote!(#ident));
    }

    match ident.as_str() {
        "bool" | "char" | "str" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "i8"
        | "i16" | "i32" | "i64" | "i128" | "isize" => Ok(Type::Path(type_path.clone())),
        "Option" => {
            let args = generic_type_args(&last.arguments, "Option", 1)?;
            let inner = args[0];
            let inner = spec_type_for_field(inner, type_params)?;
            Ok(parse_quote!(Option<#inner>))
        }
        "Vec" => {
            let args = generic_type_args(&last.arguments, "Vec", 1)?;
            let inner = args[0];
            let inner = spec_type_for_field(inner, type_params)?;
            Ok(parse_quote!(::vstd::prelude::Seq<#inner>))
        }
        "Box" | "Rc" | "Arc" => {
            let mut spec_path = path.clone();
            for segment in &mut spec_path.segments {
                if let PathArguments::AngleBracketed(args) = &mut segment.arguments {
                    segment.arguments =
                        PathArguments::AngleBracketed(spec_angle_args(args, type_params)?);
                }
            }
            Ok(Type::Path(parse_quote!(#spec_path)))
        }
        _ => user_defined_spec_type(path, type_params),
    }
}

fn generic_type_args<'a>(
    args: &'a PathArguments,
    type_name: &str,
    expected: usize,
) -> Result<Vec<&'a Type>> {
    let PathArguments::AngleBracketed(args) = args else {
        return Err(syn::Error::new(
            args.span(),
            format!("DeepView derive expected `{type_name}` to use angle-bracketed type arguments"),
        ));
    };

    let tys: Vec<_> = args
        .args
        .iter()
        .filter_map(|arg| match arg {
            GenericArgument::Type(ty) => Some(ty),
            _ => None,
        })
        .collect();

    if tys.len() != expected {
        return Err(syn::Error::new(
            args.span(),
            format!("DeepView derive expected `{type_name}` to have {expected} type argument(s)"),
        ));
    }

    Ok(tys)
}

fn user_defined_spec_type(path: &Path, type_params: &BTreeSet<String>) -> Result<Type> {
    let mut spec_path = path.clone();
    for segment in &mut spec_path.segments {
        if let PathArguments::AngleBracketed(args) = &mut segment.arguments {
            segment.arguments = PathArguments::AngleBracketed(spec_angle_args(args, type_params)?);
        }
    }

    let last = spec_path.segments.last_mut().expect("path segment");
    last.ident = format_ident!("{}Spec", last.ident);

    Ok(Type::Path(parse_quote!(#spec_path)))
}

fn spec_angle_args(
    args: &AngleBracketedGenericArguments,
    type_params: &BTreeSet<String>,
) -> Result<AngleBracketedGenericArguments> {
    let mut spec_args = AngleBracketedGenericArguments {
        colon2_token: args.colon2_token.clone(),
        lt_token: args.lt_token,
        args: Default::default(),
        gt_token: args.gt_token,
    };

    for arg in &args.args {
        match arg {
            GenericArgument::Lifetime(_) => {}
            GenericArgument::Type(ty) => {
                let ty = spec_type_for_field(ty, type_params)?;
                spec_args.args.push(GenericArgument::Type(ty));
            }
            GenericArgument::Const(c) => {
                spec_args.args.push(GenericArgument::Const(c.clone()));
            }
            _ => {
                return Err(syn::Error::new(
                    arg.span(),
                    "DeepView derive does not support this generic argument yet",
                ));
            }
        }
    }

    Ok(spec_args)
}

fn expand_deep_view_body(
    runtime_name: &Ident,
    spec_name: &Ident,
    helper_name: &Ident,
    data: &Data,
) -> Result<TokenStream2> {
    match data {
        Data::Struct(data) => expand_struct_body(runtime_name, spec_name, helper_name, data),
        Data::Enum(data) => expand_enum_body(runtime_name, spec_name, helper_name, data),
        Data::Union(data) => Err(syn::Error::new(
            data.union_token.span(),
            "DeepView derive does not support unions",
        )),
    }
}

fn expand_struct_body(
    runtime_name: &Ident,
    spec_name: &Ident,
    helper_name: &Ident,
    data: &DataStruct,
) -> Result<TokenStream2> {
    match &data.fields {
        Fields::Named(fields) => {
            let bindings: Vec<_> = fields
                .named
                .iter()
                .map(|field| field.ident.clone().expect("named field"))
                .collect();
            let field_exprs = fields.named.iter().zip(bindings.iter()).map(|(field, binding)| {
                let name = field.ident.as_ref().expect("named field");
                let expr = field_deep_view_expr(
                    &quote!(#binding),
                    &field.ty,
                    runtime_name,
                    helper_name,
                );
                quote!(#name: #expr)
            });
            Ok(quote! {
                match v {
                    #runtime_name { #(#bindings),* } => #spec_name {
                        #(#field_exprs),*
                    }
                }
            })
        }
        Fields::Unnamed(fields) => {
            let bindings: Vec<_> = (0..fields.unnamed.len())
                .map(|index| Ident::new(&format!("field_{index}"), fields.span()))
                .collect();
            let field_exprs = fields
                .unnamed
                .iter()
                .zip(bindings.iter())
                .map(|(field, binding)| {
                    field_deep_view_expr(&quote!(#binding), &field.ty, runtime_name, helper_name)
                });
            Ok(quote! {
                match v {
                    #runtime_name(#(#bindings),*) => #spec_name(#(#field_exprs),*)
                }
            })
        }
        Fields::Unit => Ok(quote!(#spec_name)),
    }
}

fn expand_enum_body(
    runtime_name: &Ident,
    spec_name: &Ident,
    helper_name: &Ident,
    data: &DataEnum,
) -> Result<TokenStream2> {
    let arms = data
        .variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;
            match &variant.fields {
                Fields::Named(fields) => {
                    let bindings: Vec<_> = fields
                        .named
                        .iter()
                        .map(|field| field.ident.clone().expect("named field"))
                        .collect();
                    let deep_fields = fields.named.iter().zip(bindings.iter()).map(
                        |(field, binding)| {
                            let expr = field_deep_view_expr(
                                &quote!(#binding),
                                &field.ty,
                                runtime_name,
                                helper_name,
                            );
                            quote!(#binding: #expr)
                        },
                    );
                    Ok(quote! {
                        #runtime_name::#variant_name { #(#bindings),* } => {
                            #spec_name::#variant_name { #(#deep_fields),* }
                        }
                    })
                }
                Fields::Unnamed(fields) => {
                    let bindings: Vec<_> = (0..fields.unnamed.len())
                        .map(|index| Ident::new(&format!("field_{index}"), variant.span()))
                        .collect();
                    let deep_fields = fields
                        .unnamed
                        .iter()
                        .zip(bindings.iter())
                        .map(|(field, binding)| {
                            field_deep_view_expr(
                                &quote!(#binding),
                                &field.ty,
                                runtime_name,
                                helper_name,
                            )
                        });
                    Ok(quote! {
                        #runtime_name::#variant_name(#(#bindings),*) => {
                            #spec_name::#variant_name(#(#deep_fields),*)
                        }
                    })
                }
                Fields::Unit => Ok(quote! {
                    #runtime_name::#variant_name => #spec_name::#variant_name
                }),
            }
        })
        .collect::<Result<Vec<_>>>()?;

    Ok(quote! {
        match v {
            #(#arms),*
        }
    })
}

fn field_deep_view_expr(
    binding_ref: &TokenStream2,
    ty: &Type,
    runtime_name: &Ident,
    helper_name: &Ident,
) -> TokenStream2 {
    match ty {
        Type::Group(group) => field_deep_view_expr(binding_ref, &group.elem, runtime_name, helper_name),
        Type::Paren(paren) => field_deep_view_expr(binding_ref, &paren.elem, runtime_name, helper_name),
        Type::Path(type_path) if is_same_runtime_type(type_path, runtime_name) => {
            quote!(#helper_name(#binding_ref))
        }
        Type::Path(type_path) if type_path.qself.is_none() => {
            let last = type_path.path.segments.last().expect("path segment");
            match last.ident.to_string().as_str() {
                "Box" => {
                    let inner = generic_type_args(&last.arguments, "Box", 1)
                        .expect("Box generic args")
                        [0];
                    let inner_ref = quote!(&**(#binding_ref));
                    let inner_expr = field_deep_view_expr(&inner_ref, inner, runtime_name, helper_name);
                    quote!(::alloc::boxed::Box::new(#inner_expr))
                }
                "Rc" => {
                    let inner = generic_type_args(&last.arguments, "Rc", 1)
                        .expect("Rc generic args")
                        [0];
                    let inner_ref = quote!(&**(#binding_ref));
                    let inner_expr = field_deep_view_expr(&inner_ref, inner, runtime_name, helper_name);
                    quote!(::alloc::rc::Rc::new(#inner_expr))
                }
                "Arc" => {
                    let inner = generic_type_args(&last.arguments, "Arc", 1)
                        .expect("Arc generic args")
                        [0];
                    let inner_ref = quote!(&**(#binding_ref));
                    let inner_expr = field_deep_view_expr(&inner_ref, inner, runtime_name, helper_name);
                    quote!(::alloc::sync::Arc::new(#inner_expr))
                }
                _ => quote!((#binding_ref).deep_view()),
            }
        }
        _ => quote!((#binding_ref).deep_view()),
    }
}

fn is_same_runtime_type(type_path: &syn::TypePath, runtime_name: &Ident) -> bool {
    type_path.qself.is_none()
        && type_path.path.segments.len() == 1
        && type_path
            .path
            .segments
            .first()
            .map(|segment| segment.ident == *runtime_name && segment.arguments.is_empty())
            .unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::expand;
    use syn::parse_quote;

    #[test]
    fn expands_struct_into_spec_type_and_impl() {
        let input = parse_quote! {
            pub struct Triple<'i> {
                pub a: u8,
                pub b: u8,
                pub c: &'i [u8],
            }
        };

        let expanded = expand(input).unwrap().to_string();

        assert!(expanded.contains("pub struct TripleSpec"));
        assert!(expanded.contains("pub c : :: vstd :: prelude :: Seq < u8 >"));
        assert!(expanded.contains("type V = TripleSpec"));
        assert!(expanded.contains("match v"));
        assert!(expanded.contains("__triple_deep_view"));
    }

    #[test]
    fn expands_enum_recursively() {
        let input = parse_quote! {
            pub enum Wrapper<'i, T> {
                Borrowed(&'i [u8]),
                Nested(Option<Box<Foo<'i, T>>>),
                Plain(T),
            }
        };

        let expanded = expand(input).unwrap().to_string();

        assert!(expanded.contains("pub enum WrapperSpec < T >"));
        assert!(expanded.contains("Borrowed"));
        assert!(expanded.contains(":: vstd :: prelude :: Seq < u8 >"));
        assert!(expanded.contains("Nested"));
        assert!(expanded.contains("Option < Box < FooSpec < T > > >"));
        assert!(expanded
            .contains("type V = WrapperSpec < < T as :: vstd :: prelude :: DeepView > :: V >"));
    }

    #[test]
    fn expands_generic_runtime_field_to_generic_spec_param() {
        let input = parse_quote! {
            pub struct Holder<T, const N: usize> {
                pub inner: Foo<T, N>,
                pub tail: [u8; N],
            }
        };

        let expanded = expand(input).unwrap().to_string();

        assert!(expanded.contains("pub struct HolderSpec < T , const N : usize >"));
        assert!(expanded.contains("pub inner : FooSpec"));
        assert!(expanded.contains("T , N"));
        assert!(expanded.contains("pub tail : :: vstd :: prelude :: Seq < u8 >"));
        assert!(expanded
            .contains("type V = HolderSpec < < T as :: vstd :: prelude :: DeepView > :: V , N >"));
    }

    #[test]
    fn expands_recursive_enum_with_box_indirection() {
        let input = parse_quote! {
            pub enum Nested {
                More(Box<Nested>),
                Done,
            }
        };

        let expanded = expand(input).unwrap().to_string();

        assert!(expanded.contains("pub enum NestedSpec"));
        assert!(expanded.contains("More"));
        assert!(expanded.contains("NestedSpec"));
        assert!(expanded.contains("Box :: new"));
        assert!(!expanded.contains("where Box < Nested > : :: vstd :: prelude :: DeepView"));
    }
}
