use std::collections::HashMap;

use proc_macro2::Ident;
use quote::format_ident;

use super::CombDef;

#[derive(Debug, Clone)]
pub struct DefinitionNames {
    pub raw: String,
    pub type_ident: Ident,
    pub owned_ident: Ident,
    pub combinator_ident: Ident,
    pub alias_ident: Ident,
    pub ctor_fn_ident: Ident,
    pub parse_fn_ident: Ident,
    pub serialize_fn_ident: Ident,
    pub length_fn_ident: Ident,
    pub generate_fn_ident: Ident,
    pub mapper_ident: Ident,
}

pub type NamesMap = HashMap<String, DefinitionNames>;

impl DefinitionNames {
    pub fn for_def(name: &str) -> Self {
        let upper = snake_to_upper_camel(name);
        Self {
            raw: name.to_string(),
            type_ident: format_ident!("{}", upper),
            owned_ident: format_ident!("{}Owned", upper),
            combinator_ident: format_ident!("{}Combinator", upper),
            alias_ident: format_ident!("{}CombinatorAlias", upper),
            ctor_fn_ident: format_ident!("{}", name),
            parse_fn_ident: format_ident!("parse_{}", name),
            serialize_fn_ident: format_ident!("serialize_{}", name),
            length_fn_ident: format_ident!("{}_len", name),
            generate_fn_ident: format_ident!("generate_{}", name),
            mapper_ident: format_ident!("{}Mapper", upper),
        }
    }
}

pub fn build_name_map(defs: &[CombDef]) -> NamesMap {
    defs.iter()
        .map(|def| (def.name.clone(), DefinitionNames::for_def(&def.name)))
        .collect()
}

pub fn snake_to_upper_camel(s: &str) -> String {
    s.split('_')
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(c) => c.to_uppercase().chain(chars).collect(),
                None => String::new(),
            }
        })
        .collect()
}
