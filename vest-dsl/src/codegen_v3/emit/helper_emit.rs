use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};

use super::super::helper_specs::{
    self, child_path, BindingEnv, CapturedValue, DependentPairHelperSpec, DispatchEnumHelperSpec,
    HelperSpec,
};
use super::super::{wrapper_inner_for, CombIR, DispatchBranchIR, WrapperUse};
use super::module_emit::{
    build_nested_tuple_pattern, concrete_borrow_type_tokens, concrete_owned_type_tokens,
    dispatch_variant_ident, public_borrow_type_tokens, public_owned_type_tokens,
    public_parse_type_tokens, value_kind_type_tokens, value_shape_borrow_expr_tokens,
    value_shape_field_expr_tokens, DefinitionEmitter, DispatchBranchTypes,
};

impl<'a> DefinitionEmitter<'a> {
    pub(super) fn helper_items(&self) -> TokenStream {
        self.helper_collection()
            .ordered()
            .iter()
            .fold(TokenStream::new(), |mut tokens, spec| {
                match spec {
                    HelperSpec::Dep(spec) => tokens.extend(self.dep_helper_item(spec)),
                    HelperSpec::Dispatch(spec) => tokens.extend(self.dispatch_helper_item(spec)),
                }
                tokens
            })
    }

    fn dispatch_helper_item(&self, spec: &DispatchEnumHelperSpec<'_>) -> TokenStream {
        let helper = self.dispatch_helper_ident(&spec.path);
        let branch_specs = self.dispatch_branch_specs(&spec.path, spec.branches, &spec.env);
        let branch_params: Vec<_> = branch_specs.iter().map(|spec| spec.param.clone()).collect();
        let default_branch_types: Vec<_> = branch_specs
            .iter()
            .map(|spec| spec.default_type.clone())
            .collect();

        let variant_defs: Vec<_> = branch_specs
            .iter()
            .map(|spec| {
                let variant = &spec.variant;
                let ty = &spec.param;
                quote! { #variant(#ty) }
            })
            .collect();

        let where_bounds: Vec<_> = branch_specs
            .iter()
            .map(|spec| {
                let ty = &spec.param;
                let parse_ty = &spec.parse_type;
                let borrow_ty = &spec.borrow_type;
                let owned_ty = &spec.owned_type;
                quote! {
                    for<'p, 's> #ty: Combinator<
                        [u8],
                        Vec<u8>,
                        Type<'p> = #parse_ty,
                        SType<'s> = #borrow_ty,
                        GType = #owned_ty,
                    >
                }
            })
            .collect();

        let parse_type = public_parse_type_tokens(self.def_ctx, quote! { 'p });
        let serialize_type = public_borrow_type_tokens(
            self.def_ctx,
            &self.defs,
            &self.plan.analysis,
            &self.plan.names,
        );
        let generate_type = public_owned_type_tokens(self.def_ctx);
        let type_name = &self.def_ctx.names.type_ident;
        let generate_enum_name = if self.def_ctx.analysis.needs_lifetime {
            &self.def_ctx.names.owned_ident
        } else {
            &self.def_ctx.names.type_ident
        };

        let parse_arms: Vec<_> = branch_specs
            .iter()
            .zip(spec.branches.iter())
            .map(|(spec, branch)| {
                let variant = &spec.variant;
                let nominal_variant = &spec.nominal_variant;
                let value = self.concrete_field_from_expr(quote! { v }, &branch.comb);
                quote! {
                    #helper::#variant(inner) => {
                        let (n, v) = inner.parse(s)?;
                        Ok((n, #type_name::#nominal_variant(#value)))
                    }
                }
            })
            .collect();

        let generate_arms: Vec<_> = branch_specs
            .iter()
            .map(|spec| {
                let variant = &spec.variant;
                let nominal_variant = &spec.nominal_variant;
                quote! {
                    #helper::#variant(inner) => {
                        let (n, v) = inner.generate(g)?;
                        Ok((n, #generate_enum_name::#nominal_variant(v)))
                    }
                }
            })
            .collect();

        let length_arms: Vec<_> = branch_specs
            .iter()
            .zip(spec.branches.iter())
            .enumerate()
            .map(|(idx, (spec, branch))| {
                let variant = &spec.variant;
                let nominal_variant = &spec.nominal_variant;
                let value = format_ident!("v{}", idx);
                let borrowed = self.concrete_variant_borrow_expr(&value, &branch.comb);
                quote! {
                    (#helper::#variant(inner), #type_name::#nominal_variant(#value)) =>
                        inner.length(#borrowed),
                }
            })
            .collect();

        let serialize_arms: Vec<_> = branch_specs
            .iter()
            .zip(spec.branches.iter())
            .enumerate()
            .map(|(idx, (spec, branch))| {
                let variant = &spec.variant;
                let nominal_variant = &spec.nominal_variant;
                let value = format_ident!("v{}", idx);
                let borrowed = self.concrete_variant_borrow_expr(&value, &branch.comb);
                quote! {
                    (#helper::#variant(inner), #type_name::#nominal_variant(#value)) =>
                        inner.serialize(#borrowed, data, pos),
                }
            })
            .collect();

        let wf_arms: Vec<_> = branch_specs
            .iter()
            .zip(spec.branches.iter())
            .enumerate()
            .map(|(idx, (spec, branch))| {
                let variant = &spec.variant;
                let nominal_variant = &spec.nominal_variant;
                let value = format_ident!("v{}", idx);
                let borrowed = self.concrete_variant_borrow_expr(&value, &branch.comb);
                quote! {
                    (#helper::#variant(inner), #type_name::#nominal_variant(#value)) =>
                        inner.well_formed(#borrowed),
                }
            })
            .collect();

        quote! {
            pub enum #helper<#(#branch_params = #default_branch_types),*> {
                #(#variant_defs,)*
            }

            impl<#(#branch_params),*> Combinator<[u8], Vec<u8>> for #helper<#(#branch_params),*>
            where
                #(#where_bounds,)*
            {
                type Type<'p> = #parse_type;
                type SType<'s> = #serialize_type;
                type GType = #generate_type;

                fn length<'s>(&self, v: Self::SType<'s>) -> usize
                where
                    [u8]: 's,
                {
                    match (self, v) {
                        #(#length_arms)*
                        _ => panic!("dispatch branch combinator does not match value"),
                    }
                }

                fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
                where
                    [u8]: 'p,
                {
                    match self {
                        #(#parse_arms)*
                    }
                }

                fn serialize<'s>(
                    &self,
                    v: Self::SType<'s>,
                    data: &mut Vec<u8>,
                    pos: usize,
                ) -> Result<usize, SerializeError>
                where
                    [u8]: 's,
                {
                    match (self, v) {
                        #(#serialize_arms)*
                        _ => Err(SerializeError::Other(
                            "dispatch branch combinator does not match value".into(),
                        )),
                    }
                }

                fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
                    match self {
                        #(#generate_arms)*
                    }
                }

                fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
                where
                    [u8]: 's,
                {
                    match (self, v) {
                        #(#wf_arms)*
                        _ => false,
                    }
                }
            }
        }
    }

    fn dispatch_branch_specs(
        &self,
        path: &[usize],
        branches: &[DispatchBranchIR],
        env: &BindingEnv,
    ) -> Vec<DispatchBranchTypes> {
        branches
            .iter()
            .enumerate()
            .map(|(idx, branch)| DispatchBranchTypes {
                param: format_ident!("C{}", idx),
                variant: dispatch_variant_ident(idx),
                nominal_variant: format_ident!("{}", branch.variant_name),
                default_type: self.comb_type_tokens_with_lt_inner(
                    &branch.comb,
                    env,
                    &child_path(path, idx),
                    None,
                    false,
                ),
                parse_type: self.concrete_parse_type_tokens(&branch.comb, quote! { 'p }),
                borrow_type: concrete_borrow_type_tokens(
                    &branch.comb,
                    &self.defs,
                    &self.plan.analysis,
                    &self.plan.names,
                ),
                owned_type: concrete_owned_type_tokens(
                    &branch.comb,
                    &self.defs,
                    &self.plan.analysis,
                    &self.plan.names,
                ),
            })
            .collect()
    }

    fn dep_helper_item(&self, spec: &DependentPairHelperSpec<'_>) -> TokenStream {
        let helper = self.helper_ident(&spec.path);
        let fst_type = self.comb_type_tokens_with_lt_inner(
            spec.fst,
            &spec.env,
            &child_path(&spec.path, 0),
            None,
            false,
        );
        let fst_stype = concrete_borrow_type_tokens(
            spec.fst,
            &self.defs,
            &self.plan.analysis,
            &self.plan.names,
        );
        let fst_gtype =
            concrete_owned_type_tokens(spec.fst, &self.defs, &self.plan.analysis, &self.plan.names);

        let field_defs = self.capture_field_defs(&spec.captures);
        let capture_lets = self.capture_lets(&spec.captures);
        let dep_parse_lets = self.dep_binding_lets(spec.fst_bindings);
        let dep_gen_lets = self.dep_binding_lets(spec.fst_bindings);

        let snd_expr_parse =
            self.comb_expr_tokens(spec.snd, &spec.parse_env, &child_path(&spec.path, 1));
        let snd_expr_gen =
            self.comb_expr_tokens(spec.snd, &spec.generate_env, &child_path(&spec.path, 1));
        let snd_type = self.comb_type_tokens_with_lt_inner(
            spec.snd,
            &spec.parse_env,
            &child_path(&spec.path, 1),
            None,
            false,
        );
        let snd_gen_type = self.comb_type_tokens_with_lt_inner(
            spec.snd,
            &spec.generate_env,
            &child_path(&spec.path, 1),
            Some(quote! { 'g }),
            false,
        );

        quote! {
            #[derive(Clone, Copy)]
            pub struct #helper {
                #(#field_defs,)*
            }

            impl DepCombinator<#fst_type, [u8], Vec<u8>> for #helper {
                type Out = #snd_type;
                type OutGen<'g> = #snd_gen_type;

                fn dep_snd<'s>(&self, fst: #fst_stype) -> Self::Out {
                    let fst: #fst_stype = fst;
                    #(#capture_lets)*
                    #(#dep_parse_lets)*
                    #snd_expr_parse
                }

                fn dep_snd_gen<'g>(&self, fst: &'g mut #fst_gtype) -> Self::OutGen<'g> {
                    let fst: &'g mut #fst_gtype = fst;
                    #(#capture_lets)*
                    #(#dep_gen_lets)*
                    #snd_expr_gen
                }
            }
        }
    }

    pub(super) fn pair_helper_init(
        &self,
        path: &[usize],
        fst_bindings: &[String],
        snd: &CombIR,
        outer_env: &BindingEnv,
    ) -> TokenStream {
        let helper = self.helper_ident(path);
        let capture_names = self.capture_names_for(snd, outer_env, fst_bindings);
        let field_inits = self.capture_field_inits(&capture_names, outer_env);
        quote! { #helper { #(#field_inits,)* } }
    }

    fn capture_names_for(
        &self,
        comb: &CombIR,
        env: &BindingEnv,
        current_deps: &[String],
    ) -> Vec<String> {
        helper_specs::capture_names(&helper_specs::used_names_in_comb(comb), env, current_deps)
    }

    fn capture_field_defs(&self, captures: &[CapturedValue]) -> Vec<TokenStream> {
        captures
            .iter()
            .map(|capture| {
                let ident = format_ident!("{}", capture.name);
                let ty = value_kind_type_tokens(&capture.kind, &self.plan.names);
                quote! { #ident: #ty }
            })
            .collect()
    }

    fn capture_field_inits(&self, names: &[String], env: &BindingEnv) -> Vec<TokenStream> {
        names
            .iter()
            .map(|name| {
                let ident = &env[name].ident;
                quote! { #ident: #ident }
            })
            .collect()
    }

    fn capture_lets(&self, captures: &[CapturedValue]) -> Vec<TokenStream> {
        captures
            .iter()
            .map(|capture| {
                let ident = format_ident!("{}", capture.name);
                quote! { let #ident = self.#ident; }
            })
            .collect()
    }

    fn dep_binding_lets(&self, dep_names: &[String]) -> Vec<TokenStream> {
        if dep_names.is_empty() {
            return Vec::new();
        }

        let idents: Vec<_> = dep_names
            .iter()
            .map(|name| format_ident!("{}", name))
            .collect();
        if dep_names.len() == 1 {
            let ident = &idents[0];
            vec![quote! { let #ident = fst; }]
        } else {
            let pattern = build_nested_tuple_pattern(&idents);
            vec![quote! { let #pattern = fst; }]
        }
    }

    fn concrete_parse_type_tokens(&self, comb: &CombIR, lt: TokenStream) -> TokenStream {
        if let Some(inner) = wrapper_inner_for(comb, WrapperUse::ValueShape) {
            return self.concrete_parse_type_tokens(inner, lt);
        }

        match comb {
            CombIR::UInt(uint) => uint.rust_type_tokens(),
            CombIR::Fixed { .. } | CombIR::Variable { .. } | CombIR::Tail => quote! { &#lt [u8] },
            CombIR::Struct(fields) => {
                let tys: Vec<_> = fields
                    .iter()
                    .map(|field| self.concrete_parse_type_tokens(&field.comb, lt.clone()))
                    .collect();
                super::module_emit::build_nested_pair_type(&tys)
            }
            CombIR::Seq(items) => {
                let tys: Vec<_> = items
                    .iter()
                    .map(|item| self.concrete_parse_type_tokens(item, lt.clone()))
                    .collect();
                super::module_emit::build_nested_pair_type(&tys)
            }
            CombIR::DepPair { fst, snd, .. } => {
                let fst = self.concrete_parse_type_tokens(fst, lt.clone());
                let snd = self.concrete_parse_type_tokens(snd, lt);
                super::module_emit::build_nested_pair_type(&[fst, snd])
            }
            CombIR::Opt(inner) => {
                let inner = self.concrete_parse_type_tokens(inner, lt);
                quote! { Option<#inner> }
            }
            CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
                let inner = self.concrete_parse_type_tokens(inner, lt);
                quote! { Vec<#inner> }
            }
            CombIR::Dispatch { .. } => public_parse_type_tokens(self.def_ctx, lt),
            CombIR::Enum { inner, .. } => self.concrete_parse_type_tokens(inner, lt),
            CombIR::Named { name, .. } => {
                let name_set = self.plan.names.get(name).expect("names for parse type");
                let analysis = self
                    .plan
                    .analysis
                    .get(name)
                    .expect("analysis for parse type");
                let type_name = &name_set.type_ident;
                if analysis.needs_lifetime {
                    quote! { #type_name<#lt> }
                } else {
                    quote! { #type_name }
                }
            }
            CombIR::Tag { .. } | CombIR::End | CombIR::Success | CombIR::Fail(_) => quote! { () },
            CombIR::Preceded { .. }
            | CombIR::Terminated { .. }
            | CombIR::Refined { .. }
            | CombIR::Mapped { .. }
            | CombIR::AndThen { .. }
            | CombIR::FixedLen { .. } => unreachable!("transparent wrappers handled above"),
        }
    }

    fn concrete_field_from_expr(&self, expr: TokenStream, comb: &CombIR) -> TokenStream {
        value_shape_field_expr_tokens(expr, comb, self.def_ctx.def, &self.plan.names)
    }

    fn concrete_variant_borrow_expr(&self, binding: &Ident, comb: &CombIR) -> TokenStream {
        self.field_borrow_expr(quote! { (*#binding) }, comb)
    }

    fn field_borrow_expr(&self, access: TokenStream, comb: &CombIR) -> TokenStream {
        value_shape_borrow_expr_tokens(access, comb, &self.defs, &self.plan.analysis)
    }
}
