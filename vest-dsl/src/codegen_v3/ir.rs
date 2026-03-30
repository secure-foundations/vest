use std::collections::{HashMap, HashSet};

use proc_macro2::Ident;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

pub use crate::vestir::ArithOp;
pub use crate::vestir::Endianess as Endian;
pub use crate::vestir::EnumConstraint as EnumConstraintIR;
pub use crate::vestir::IntConstraint as IntConstraintIR;
pub use crate::vestir::LengthExpr as LenExpr;
pub use crate::vestir::Param as ParamRef;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UIntWidth {
    U8,
    U16,
    U24,
    U32,
    U64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UIntIR {
    pub width: UIntWidth,
    pub endian: Endian,
}

impl UIntIR {
    pub fn new(width: UIntWidth, endian: Endian) -> Self {
        Self { width, endian }
    }

    pub fn rust_type_tokens(self) -> TokenStream {
        match self.width {
            UIntWidth::U8 => quote! { u8 },
            UIntWidth::U16 => quote! { u16 },
            UIntWidth::U24 => quote! { u24 },
            UIntWidth::U32 => quote! { u32 },
            UIntWidth::U64 => quote! { u64 },
        }
    }

    pub fn combinator_type_tokens(self) -> TokenStream {
        match (self.width, self.endian) {
            (UIntWidth::U8, _) => quote! { U8 },
            (UIntWidth::U16, Endian::Little) => quote! { U16Le },
            (UIntWidth::U16, Endian::Big) => quote! { U16Be },
            (UIntWidth::U24, Endian::Little) => quote! { U24Le },
            (UIntWidth::U24, Endian::Big) => quote! { U24Be },
            (UIntWidth::U32, Endian::Little) => quote! { U32Le },
            (UIntWidth::U32, Endian::Big) => quote! { U32Be },
            (UIntWidth::U64, Endian::Little) => quote! { U64Le },
            (UIntWidth::U64, Endian::Big) => quote! { U64Be },
        }
    }

    pub fn is_u24(self) -> bool {
        matches!(self.width, UIntWidth::U24)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TagValue {
    Int(i128),
    Enum { ty: String, variant: String },
    Bytes(Vec<u8>),
    Wildcard,
}

#[derive(Debug, Clone)]
pub struct CodegenCtx {
    pub endian: Endian,
    pub static_sizes: HashMap<String, usize>,
    pub enum_types: HashSet<String>,
}

impl Default for CodegenCtx {
    fn default() -> Self {
        Self {
            endian: Endian::Little,
            static_sizes: HashMap::new(),
            enum_types: HashSet::new(),
        }
    }
}

impl From<&crate::type_check::GlobalCtx<'_>> for CodegenCtx {
    fn from(ctx: &crate::type_check::GlobalCtx<'_>) -> Self {
        Self {
            endian: Endian::Little,
            static_sizes: ctx.static_sizes.clone(),
            enum_types: ctx.enums.keys().map(|name| (*name).to_string()).collect(),
        }
    }
}

impl CodegenCtx {
    pub fn is_enum_type(&self, name: &str) -> bool {
        self.enum_types.contains(name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructFieldIR {
    pub name: String,
    pub comb: CombIR,
    pub is_const: bool,
}

impl StructFieldIR {
    pub fn new(name: impl Into<String>, comb: CombIR, is_const: bool) -> Self {
        Self {
            name: name.into(),
            comb,
            is_const,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DispatchBranchIR {
    pub tag: TagValue,
    pub comb: CombIR,
    pub variant_name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumVariantIR {
    pub name: String,
    pub value: i128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PredicateIR {
    Int(IntConstraintIR),
    Enum(EnumConstraintIR),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombIR {
    UInt(UIntIR),
    Fixed {
        len: usize,
    },
    Variable {
        len: LenExpr,
    },
    Tail,
    End,
    Success,
    Fail(String),
    Struct(Vec<StructFieldIR>),
    Seq(Vec<CombIR>),
    DepPair {
        fst: Box<CombIR>,
        fst_bindings: Vec<String>,
        snd: Box<CombIR>,
    },
    Preceded {
        prefix: Box<CombIR>,
        inner: Box<CombIR>,
    },
    Terminated {
        inner: Box<CombIR>,
        suffix: Box<CombIR>,
    },
    Dispatch {
        tag: String,
        branches: Vec<DispatchBranchIR>,
    },
    Opt(Box<CombIR>),
    RepeatN {
        inner: Box<CombIR>,
        count: LenExpr,
    },
    Repeat(Box<CombIR>),
    Refined {
        inner: Box<CombIR>,
        predicate: PredicateIR,
    },
    Mapped {
        inner: Box<CombIR>,
        mapper: String,
    },
    AndThen {
        len_comb: Box<CombIR>,
        inner: Box<CombIR>,
    },
    FixedLen {
        len: LenExpr,
        inner: Box<CombIR>,
    },
    Enum {
        inner: Box<CombIR>,
        predicate: IntConstraintIR,
        variants: Vec<EnumVariantIR>,
    },
    Tag {
        inner: Box<CombIR>,
        value: TagValue,
    },
    Named {
        name: String,
        args: Vec<ParamRef>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstDef {
    pub name: String,
    pub ty: UIntIR,
    pub value: i128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CombDef {
    pub name: String,
    pub params: Vec<ParamDef>,
    pub body: CombIR,
    pub is_const: bool,
    pub const_defs: Vec<ConstDef>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamDef {
    pub name: String,
    pub ty: CombIR,
}

pub fn variant_name_from_tag(tag: &TagValue, index: usize) -> String {
    match tag {
        TagValue::Int(_) => format!("Variant{}", index),
        TagValue::Enum { variant, .. } => variant.clone(),
        TagValue::Bytes(bytes) => format!("Bytes{:02X?}", bytes).replace(['[', ']', ',', ' '], ""),
        TagValue::Wildcard => "Default".to_string(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WrapperUse {
    /// Ignore wrappers that do not change the nominal identity of a top-level definition.
    NominalRoot,
    /// Ignore wrappers that do not change the runtime value shape/type.
    ValueShape,
}

pub fn wrapper_inner_for(comb: &CombIR, usage: WrapperUse) -> Option<&CombIR> {
    match comb {
        CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::AndThen { inner, .. }
        | CombIR::FixedLen { inner, .. } => Some(inner),
        CombIR::Preceded { inner, .. } | CombIR::Terminated { inner, .. }
            if usage == WrapperUse::ValueShape =>
        {
            Some(inner)
        }
        _ => None,
    }
}

pub fn peel_wrappers_for(mut comb: &CombIR, usage: WrapperUse) -> &CombIR {
    while let Some(inner) = wrapper_inner_for(comb, usage) {
        comb = inner;
    }
    comb
}

pub fn const_ident_for_int(def: &CombDef, value: i128) -> Option<Ident> {
    let mut matches = def
        .const_defs
        .iter()
        .filter(|const_def| const_def.value == value)
        .map(|const_def| format_ident!("{}", const_def.name));
    let first = matches.next()?;
    if matches.next().is_some() {
        None
    } else {
        Some(first)
    }
}
