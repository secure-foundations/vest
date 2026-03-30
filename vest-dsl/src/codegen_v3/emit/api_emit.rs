use proc_macro2::{Ident, TokenStream};
use quote::quote;

use super::module_emit::{
    call_tokens, emit_function_item, public_borrow_type_tokens, public_owned_type_tokens,
    public_parse_type_tokens, value_kind_type_tokens, DefinitionEmitter,
};

impl<'a> DefinitionEmitter<'a> {
    pub(super) fn constructor_item(&self) -> TokenStream {
        let env = self.constructor_env();
        let body_expr_raw = self.top_level_body_expr_tokens(&self.def_ctx.def.body, &env);
        let body_expr = self.wrap_top_level_mapper_expr(body_expr_raw);
        self.constructor_fn(body_expr)
    }

    pub(super) fn public_items(&self) -> TokenStream {
        let parse_fn = self.parse_fn();
        let serialize_fn = self.serialize_fn();
        let length_fn = self.length_fn();
        let generate_fn = self.generate_fn();

        quote! {
            #parse_fn
            #serialize_fn
            #length_fn
            #generate_fn
        }
    }

    fn constructor_param_generic_idents(&self) -> Vec<Ident> {
        self.param_specs
            .iter()
            .filter(|param| param.needs_generate_ref)
            .map(super::module_emit::EmitParam::ctor_generic_ident)
            .collect()
    }

    fn constructor_param_list_tokens(&self) -> Vec<TokenStream> {
        self.param_specs
            .iter()
            .map(|param| {
                let ident = &param.ident;
                if param.needs_generate_ref {
                    let arg_ty = param.ctor_generic_ident();
                    quote! { #ident: #arg_ty }
                } else {
                    let ty = value_kind_type_tokens(&param.kind, &self.plan.names);
                    quote! { #ident: #ty }
                }
            })
            .collect()
    }

    fn constructor_where_bounds(&self, lt: TokenStream) -> Vec<TokenStream> {
        self.param_specs
            .iter()
            .filter(|param| param.needs_generate_ref)
            .map(|param| {
                let arg_ty = param.ctor_generic_ident();
                let raw_ty = value_kind_type_tokens(&param.kind, &self.plan.names);
                if param.needs_length_param {
                    quote! { #arg_ty: LengthParam<#lt, #raw_ty> }
                } else {
                    quote! { #arg_ty: RuntimeValParam<#lt, #raw_ty> }
                }
            })
            .collect()
    }

    fn constructor_return_type(&self) -> TokenStream {
        let combinator_type = &self.def_ctx.names.combinator_ident;
        if self.needs_runtime_ref {
            let alias_name = &self.def_ctx.names.alias_ident;
            quote! { #combinator_type<#alias_name<'a>> }
        } else {
            quote! { #combinator_type }
        }
    }

    fn constructor_fn(&self, body_expr: TokenStream) -> TokenStream {
        let fn_name = &self.def_ctx.names.ctor_fn_ident;
        let combinator_type = self.constructor_return_type();
        let ctor_name = &self.def_ctx.names.combinator_ident;
        let params = self.constructor_param_list_tokens();
        let ctor_doc = format!("Constructor for {} combinator", self.def_ctx.def.name);

        if params.is_empty() {
            quote! {
                #[doc = #ctor_doc]
                pub fn #fn_name() -> #combinator_type {
                    #ctor_name(#body_expr)
                }
            }
        } else if self.needs_runtime_ref {
            let generic_args = self.constructor_param_generic_idents();
            let where_bounds = self.constructor_where_bounds(quote! { 'a });
            quote! {
                #[doc = #ctor_doc]
                pub fn #fn_name<'a, #(#generic_args),*>(#(#params),*) -> #combinator_type
                where
                    #(#where_bounds,)*
                {
                    #ctor_name(#body_expr)
                }
            }
        } else {
            quote! {
                #[doc = #ctor_doc]
                pub fn #fn_name(#(#params),*) -> #combinator_type {
                    #ctor_name(#body_expr)
                }
            }
        }
    }

    fn wrap_top_level_mapper_expr(&self, body_expr: TokenStream) -> TokenStream {
        if self.def_ctx.analysis.emits_mapper {
            let mapper = &self.def_ctx.names.mapper_ident;
            quote! { Mapped::new(#body_expr, #mapper) }
        } else {
            body_expr
        }
    }

    fn parse_fn(&self) -> TokenStream {
        let fn_name = &self.def_ctx.names.parse_fn_ident;
        let params = self.param_list_tokens();
        let parse_doc = format!("Parse function for {} combinator", self.def_ctx.def.name);
        let combinator_ctor = self.public_ctor_call_tokens();
        let parse_type = public_parse_type_tokens(self.def_ctx, quote! { 'p });

        emit_function_item(
            parse_doc,
            fn_name.clone(),
            Some(quote! { <'p> }),
            std::iter::once(quote! { input: &'p [u8] })
                .chain(params)
                .collect(),
            quote! { Result<(usize, #parse_type), ParseError> },
            quote! {
                let combinator = #combinator_ctor;
                combinator.parse(input)
            },
        )
    }

    fn serialize_fn(&self) -> TokenStream {
        let fn_name = &self.def_ctx.names.serialize_fn_ident;
        let borrow_type = public_borrow_type_tokens(
            self.def_ctx,
            &self.defs,
            &self.plan.analysis,
            &self.plan.names,
        );
        let params = self.param_list_tokens();
        let serialize_doc = format!(
            "Serialize function for {} combinator",
            self.def_ctx.def.name
        );
        let combinator_ctor = self.public_ctor_call_tokens();

        emit_function_item(
            serialize_doc,
            fn_name.clone(),
            Some(quote! { <'s> }),
            vec![
                quote! { v: #borrow_type },
                quote! { data: &mut Vec<u8> },
                quote! { pos: usize },
            ]
            .into_iter()
            .chain(params)
            .collect(),
            quote! { Result<usize, SerializeError> },
            quote! {
                let combinator = #combinator_ctor;
                combinator.serialize(v, data, pos)
            },
        )
    }

    fn length_fn(&self) -> TokenStream {
        let fn_name = &self.def_ctx.names.length_fn_ident;
        let borrow_type = public_borrow_type_tokens(
            self.def_ctx,
            &self.defs,
            &self.plan.analysis,
            &self.plan.names,
        );
        let params = self.param_list_tokens();
        let length_doc = format!("Length function for {} combinator", self.def_ctx.def.name);
        let combinator_ctor = self.public_ctor_call_tokens();

        emit_function_item(
            length_doc,
            fn_name.clone(),
            Some(quote! { <'s> }),
            std::iter::once(quote! { v: #borrow_type })
                .chain(params)
                .collect(),
            quote! { usize },
            quote! {
                let combinator = #combinator_ctor;
                combinator.length(v)
            },
        )
    }

    fn generate_fn(&self) -> TokenStream {
        let fn_name = &self.def_ctx.names.generate_fn_ident;
        let owned_type = public_owned_type_tokens(self.def_ctx);
        let params = self.generate_param_list_tokens();
        let generate_doc = format!("Generate function for {} combinator", self.def_ctx.def.name);
        let combinator_ctor = self.public_ctor_call_tokens();
        let generics = (self.needs_runtime_ref && !params.is_empty()).then(|| quote! { <'g> });

        emit_function_item(
            generate_doc,
            fn_name.clone(),
            generics,
            std::iter::once(quote! { g: &mut GenSt })
                .chain(params)
                .collect(),
            quote! { GResult<#owned_type, GenerateError> },
            quote! {
                let mut combinator = #combinator_ctor;
                combinator.generate(g)
            },
        )
    }

    fn param_list_tokens(&self) -> Vec<TokenStream> {
        self.param_list_tokens_with_lifetime(false)
    }

    fn generate_param_list_tokens(&self) -> Vec<TokenStream> {
        self.param_list_tokens_with_lifetime(true)
    }

    fn param_list_tokens_with_lifetime(&self, generate_mode: bool) -> Vec<TokenStream> {
        self.param_specs
            .iter()
            .map(|param| {
                let ident = &param.ident;
                let ty = value_kind_type_tokens(&param.kind, &self.plan.names);
                if generate_mode && param.needs_generate_ref {
                    quote! { #ident: &'g mut #ty }
                } else {
                    quote! { #ident: #ty }
                }
            })
            .collect()
    }

    fn public_ctor_call_tokens(&self) -> TokenStream {
        let fn_name = &self.def_ctx.names.ctor_fn_ident;
        let arg_names: Vec<_> = self
            .param_specs
            .iter()
            .map(|param| {
                let ident = &param.ident;
                quote! { #ident }
            })
            .collect();
        call_tokens(fn_name, &arg_names)
    }
}
