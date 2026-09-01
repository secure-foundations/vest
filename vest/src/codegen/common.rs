use crate::vestir::{
    self, ArrayCombinator, ChoiceCombinator, ChoicePattern, Combinator, CombinatorInvocation,
    ConstArray, ConstCombinator, ConstraintElem, ConstraintEnumCombinator, ConstraintIntCombinator,
    Definition, Endianess, EnumCombinator, GlobalCtx, IntCombinator, LengthExpr, OptionCombinator,
    ParamDefn, RecursiveScc, SccMember, SccMemberBody, StructCombinator, StructField,
    TailCombinator, VecCombinator, WrapCombinator,
};
use heck::ToUpperCamelCase;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(crate) struct FormatNames {
    pub(crate) dsl: String,
    pub(crate) exec: String,
    pub(crate) spec: String,
    pub(crate) inner: String,
    pub(crate) fmt: String,
}

impl FormatNames {
    pub(crate) fn spec_ctor_ident(&self) -> proc_macro2::Ident {
        format_ident!("spec_inner")
    }

    pub(crate) fn wrapper_ctor_ident(&self) -> proc_macro2::Ident {
        format_ident!("spec")
    }

    pub(crate) fn wrapper_field_ident(name: &str) -> proc_macro2::Ident {
        format_ident!("{}", name)
    }

    pub(crate) fn wrapper_accessor_ident(name: &str) -> proc_macro2::Ident {
        format_ident!("{}_spec", name)
    }
}

#[derive(Debug, Clone)]
pub(crate) struct FormatInfo {
    pub(crate) names: FormatNames,
    pub(crate) needs_lifetime: bool,
    pub(crate) non_tail: bool,
    pub(crate) non_malleable: bool,
}

pub(crate) struct Analysis<'a> {
    pub(crate) defs: &'a [Definition],
    pub(crate) ctx: &'a GlobalCtx,
    pub(crate) endianness: Endianess,
    pub(crate) infos: HashMap<String, FormatInfo>,
    /// Index into `sccs` for each member of a recursive SCC.
    pub(crate) scc_of: HashMap<String, usize>,
    /// `(scc_idx, member_idx)` for each recursive SCC member.
    pub(crate) scc_member_of: HashMap<String, (usize, usize)>,
    /// Definition index in `defs` for each entry in `sccs`.
    pub(crate) scc_def_indices: Vec<usize>,
    /// Metadata for each recursive SCC, indexed by `scc_of`.
    pub(crate) sccs: Vec<SccInfo>,
}

/// Metadata about one recursive SCC, computed once in `Analysis::new`.
#[derive(Debug, Clone)]
pub(crate) struct SccInfo {
    /// Member names in source order.
    pub(crate) members: Vec<String>,
    /// Identifier for the `WhichFmt` / `WhichXxx` discriminant enum (e.g. `WhichExpr`).
    pub(crate) which_ident: String,
    /// Identifier for the `Value` union enum (e.g. `ExprListValue`).
    pub(crate) value_ident: String,
    /// Identifier for the combined `RecBody` struct (e.g. `ExprListRecBody`).
    pub(crate) rec_body_ident: String,
    /// Identifier for the `Param` type (same as `which_ident` for non-parameterized SCCs;
    /// `XxxParam` for parameterized SCCs).
    pub(crate) param_ident: String,
}

#[derive(Debug, Clone)]
pub(crate) struct BitsFieldLayout {
    pub(crate) label: String,
    pub(crate) logical_width: u8,
    pub(crate) carrier_ty: vestir::IntCombinator,
    pub(crate) mask: u64,
    pub(crate) shift: u8,
    pub(crate) is_enum: bool,
    pub(crate) is_closed_enum: bool,
    pub(crate) enum_name: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct BitsLayout {
    pub(crate) repr_int: vestir::IntCombinator,
    pub(crate) fields: Vec<BitsFieldLayout>,
}

impl BitsLayout {
    pub(crate) fn field_idents(&self) -> Vec<proc_macro2::Ident> {
        self.fields
            .iter()
            .map(|f| format_ident!("{}", f.label))
            .collect()
    }
}

pub(crate) fn bits_tuple_type_tokens(tys: &[TokenStream]) -> TokenStream {
    match tys {
        [] => quote! { () },
        [only] => quote! { #only },
        _ => quote! { (#(#tys),*) },
    }
}

pub(crate) fn bits_tuple_pattern_tokens(idents: &[proc_macro2::Ident]) -> TokenStream {
    match idents {
        [] => quote! { () },
        [only] => quote! { #only },
        _ => quote! { (#(#idents),*) },
    }
}

pub(crate) fn bits_tuple_expr_tokens(exprs: &[TokenStream]) -> TokenStream {
    match exprs {
        [] => quote! { () },
        [only] => quote! { #only },
        _ => quote! { (#(#exprs),*) },
    }
}

pub(crate) fn bits_tuple_expr_from_idents(idents: &[proc_macro2::Ident]) -> TokenStream {
    match idents {
        [] => quote! { () },
        [only] => quote! { #only },
        _ => quote! { (#(#idents),*) },
    }
}

pub(crate) fn nested_tuple_pattern_idents(idents: &[proc_macro2::Ident]) -> TokenStream {
    match idents {
        [] => quote! { () },
        [only] => quote! { #only },
        [first, rest @ ..] => {
            let rest = nested_tuple_pattern_idents(rest);
            quote! { (#first, #rest) }
        }
    }
}

pub(crate) fn nested_tuple_value_expr_idents(idents: &[proc_macro2::Ident]) -> TokenStream {
    match idents {
        [] => quote! { () },
        [only] => quote! { #only },
        [first, rest @ ..] => {
            let rest = nested_tuple_value_expr_idents(rest);
            quote! { (#first, #rest) }
        }
    }
}

pub(crate) fn tuple_index_expr(base: TokenStream, idx: usize) -> TokenStream {
    let index = proc_macro2::Literal::usize_unsuffixed(idx);
    quote! { #base.#index }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TypeMode {
    Exec,
    Spec,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Op {
    Parse,
    Serialize,
    Prepare,
}

impl<'a> Analysis<'a> {
    pub(crate) fn int_is_byte_aligned(&self, int: &IntCombinator) -> bool {
        match int {
            IntCombinator::Signed(bits) | IntCombinator::Unsigned(bits) => bits % 8 == 0,
            IntCombinator::BtcVarint | IntCombinator::ULEB128 => true,
        }
    }

    pub(crate) fn enum_is_bit_sized(&self, enum_comb: &vestir::EnumCombinator) -> bool {
        let inferred = match enum_comb {
            vestir::EnumCombinator::Exhaustive { inferred, .. }
            | vestir::EnumCombinator::NonExhaustive { inferred, .. } => inferred,
        };
        !self.int_is_byte_aligned(inferred)
    }

    pub(crate) fn direct_alias<'b>(
        &self,
        combinator: &'b Combinator,
    ) -> Option<&'b CombinatorInvocation> {
        match combinator {
            Combinator::Invocation(invocation) => Some(invocation),
            _ => None,
        }
    }

    pub(crate) fn enum_value_literals(&self, enum_name: &str) -> Vec<TokenStream> {
        let def = self
            .defs
            .iter()
            .find(|d| d.name() == Some(enum_name))
            .unwrap_or_else(|| panic!("unknown enum {}", enum_name));
        match def {
            Definition::EnumDef { combinator, .. } => {
                let (enums, inferred) = match combinator {
                    EnumCombinator::Exhaustive { enums, inferred }
                    | EnumCombinator::NonExhaustive { enums, inferred } => {
                        (enums.as_slice(), inferred)
                    }
                };
                enums
                    .iter()
                    .map(|variant| int_literal(variant.value, inferred))
                    .collect()
            }
            _ => panic!("{} is not an enum", enum_name),
        }
    }

    pub(crate) fn bits_closed_enum_pred(
        &self,
        invocation: &vestir::CombinatorInvocation,
        value: TokenStream,
    ) -> TokenStream {
        let values = self.enum_value_literals(&invocation.func);
        quote! { (#(#value == #values)||*) }
    }

    pub(crate) fn bits_raw_field_expr(
        &self,
        layout_field: &BitsFieldLayout,
        value: TokenStream,
    ) -> TokenStream {
        if layout_field.is_enum {
            let to_bits = format_ident!("{}_to_bits", layout_field.enum_name.as_ref().unwrap());
            quote! { #to_bits(#value) }
        } else {
            value
        }
    }

    pub(crate) fn bits_ctor_field_expr(
        &self,
        layout_field: &BitsFieldLayout,
        raw_value: TokenStream,
    ) -> TokenStream {
        if layout_field.is_enum {
            let from_bits = format_ident!("{}_from_bits", layout_field.enum_name.as_ref().unwrap());
            quote! { #from_bits(#raw_value) }
        } else {
            raw_value
        }
    }

    pub(crate) fn bits_ctor_fields(
        &self,
        layout: &BitsLayout,
    ) -> Vec<(proc_macro2::Ident, TokenStream)> {
        layout
            .fields
            .iter()
            .map(|field| {
                let field_ident = format_ident!("{}", field.label);
                let expr = self.bits_ctor_field_expr(field, quote! { #field_ident });
                (field_ident, expr)
            })
            .collect()
    }

    pub(crate) fn bits_raw_field_exprs(&self, layout: &BitsLayout) -> Vec<TokenStream> {
        layout
            .fields
            .iter()
            .map(|field| {
                let ident = format_ident!("{}", field.label);
                self.bits_raw_field_expr(field, quote! { #ident })
            })
            .collect()
    }

    pub(crate) fn bits_open_enum_wf_pred(
        &self,
        layout_field: &BitsFieldLayout,
        value: TokenStream,
    ) -> Option<TokenStream> {
        if layout_field.is_enum && !layout_field.is_closed_enum {
            let wf = format_ident!("{}_wf", layout_field.enum_name.as_ref().unwrap());
            Some(quote! { #wf(#value) })
        } else {
            None
        }
    }

    pub(crate) fn bits_field_refinement_pred(
        &self,
        field: &vestir::BitField,
        layout_field: &BitsFieldLayout,
        value: TokenStream,
    ) -> Option<TokenStream> {
        match field.combinator() {
            vestir::BitFieldCombinator::UInt(c) => c
                .constraint
                .as_ref()
                .map(|constraint| self.render_int_constraint(constraint, &c.combinator, value)),
            vestir::BitFieldCombinator::Enum(inv) if layout_field.is_closed_enum => {
                Some(self.bits_closed_enum_pred(inv, value))
            }
            _ => None,
        }
    }

    pub(crate) fn resolve_dep_combinator_path(
        &self,
        dep: &str,
        param_defns: &[ParamDefn],
    ) -> Option<Combinator> {
        let mut parts = dep.split('.');
        let root = parts.next()?;
        let mut current = param_defns.iter().find_map(|p| match p {
            ParamDefn::Dependent { name, combinator } if name == root => Some(combinator.clone()),
            _ => None,
        })?;

        for field_name in parts {
            loop {
                match current {
                    Combinator::Invocation(ref inv) => {
                        let def = self
                            .defs
                            .iter()
                            .find(|d| d.name() == Some(inv.func.as_str()))?;
                        current = match def {
                            vestir::Definition::StructDef { combinator, .. } => {
                                combinator.0.iter().find_map(|field| match field {
                                    StructField::Dependent { label, combinator }
                                    | StructField::Ordinary { label, combinator }
                                        if label == field_name =>
                                    {
                                        Some(combinator.clone())
                                    }
                                    _ => None,
                                })?
                            }
                            vestir::Definition::BitsDef { combinator, .. } => {
                                combinator.0.iter().find_map(|field| match field {
                                    vestir::BitField::Dependent { label, combinator }
                                    | vestir::BitField::Ordinary { label, combinator }
                                        if label == field_name =>
                                    {
                                        Some(Combinator::from(combinator))
                                    }
                                    _ => None,
                                })?
                            }
                            vestir::Definition::CombinatorDef { combinator, .. } => {
                                current = combinator.clone();
                                continue;
                            }
                            _ => return None,
                        };
                        break;
                    }
                    _ => return None,
                }
            }
        }

        Some(current)
    }

    pub(crate) fn new(defs: &'a [Definition], ctx: &'a GlobalCtx) -> Self {
        let endianness = defs
            .iter()
            .find_map(|def| match def {
                Definition::Endianess(endianness) => Some(*endianness),
                _ => None,
            })
            .unwrap_or(Endianess::Little);

        let mut this = Self {
            defs,
            ctx,
            endianness,
            infos: HashMap::new(),
            scc_of: HashMap::new(),
            scc_member_of: HashMap::new(),
            scc_def_indices: Vec::new(),
            sccs: Vec::new(),
        };
        // Pre-assign SCC indices in source (file) order so SCC numbering is stable.
        let mut scc_source_order: std::collections::HashMap<*const RecursiveScc, usize> =
            Default::default();
        let mut scc_def_index: std::collections::HashMap<*const RecursiveScc, usize> =
            Default::default();
        let mut scc_counter = 0usize;
        for (def_idx, def) in defs.iter().enumerate() {
            if let Definition::RecursiveScc(scc) = def {
                let ptr = scc as *const RecursiveScc;
                if let std::collections::hash_map::Entry::Vacant(entry) =
                    scc_source_order.entry(ptr)
                {
                    entry.insert(scc_counter);
                    scc_def_index.insert(ptr, def_idx);
                    scc_counter += 1;
                }
            }
        }
        // Process definitions in dependency (callee-before-caller) order.
        for name in this.dependency_order() {
            // If this name belongs to a recursive SCC, handle the whole SCC at once
            // when we hit its first member in dependency order.
            if this.scc_of.contains_key(&name) {
                continue; // already processed as part of its SCC
            }
            // Check if this name is an SCC member (by finding it in defs).
            if let Some(scc) = this.find_scc_for(&name) {
                // Look up source-order index for this SCC (1-based).
                let scc_n = scc_source_order
                    .get(&(scc as *const RecursiveScc))
                    .copied()
                    .unwrap_or(this.sccs.len())
                    + 1;
                // Runtime index for the sccs Vec — we still push in dep order.
                let scc_idx = this.sccs.len();
                let member_names: Vec<String> =
                    scc.members.iter().map(|m| m.name.clone()).collect();
                for (member_idx, m) in member_names.iter().enumerate() {
                    this.scc_of.insert(m.clone(), scc_idx);
                    this.scc_member_of.insert(m.clone(), (scc_idx, member_idx));
                }
                this.scc_def_indices.push(
                    *scc_def_index
                        .get(&(scc as *const RecursiveScc))
                        .expect("recursive SCC missing def index"),
                );
                // Compute shared needs_lifetime: any member with Bytes/Tail leaf
                // or out-of-SCC reference that needs lifetime.
                let nl = scc
                    .members
                    .iter()
                    .any(|m| this.scc_member_needs_lifetime(m, &member_names));
                // Detect parameterization across the whole SCC. After elaboration every SCC
                // member is a top-level format in its own right, so there is no "root" vs
                // "helper" distinction here.
                let parameterized = scc.members.iter().any(|m| {
                    m.param_defns.iter().any(|p| match p {
                        vestir::ParamDefn::Dependent { combinator, .. } => {
                            !matches!(combinator, vestir::Combinator::Invocation(_))
                        }
                    })
                });
                // Generate stable naming: SCC{n} where n = 1-based source order index.
                let (which_ident, value_ident, rec_body_ident, param_ident) =
                    scc_names(scc_n, parameterized);
                this.sccs.push(SccInfo {
                    members: member_names.clone(),
                    which_ident,
                    value_ident,
                    rec_body_ident,
                    param_ident,
                });
                // Insert FormatInfo for every member (non_tail=true, non_malleable=true).
                for m in &scc.members {
                    let names = format_names(&m.name);
                    this.infos.insert(
                        m.name.clone(),
                        FormatInfo {
                            names,
                            needs_lifetime: nl,
                            non_tail: true,
                            non_malleable: true,
                        },
                    );
                }
                continue;
            }
            // Normal non-recursive definition.
            let Some(def) = this.def_by_name(&name) else {
                continue;
            };
            let names = format_names(&name);
            let needs_lifetime = this.definition_needs_lifetime(def);
            let non_tail = this.definition_non_tail(def);
            let non_malleable = this.definition_non_malleable(def);
            this.infos.insert(
                name,
                FormatInfo {
                    names,
                    needs_lifetime,
                    non_tail,
                    non_malleable,
                },
            );
        }
        this
    }

    /// If `name` is a member of a `RecursiveScc`, return a reference to that SCC.
    fn find_scc_for(&self, name: &str) -> Option<&'a RecursiveScc> {
        for def in self.defs {
            if let Definition::RecursiveScc(scc) = def {
                if scc.members.iter().any(|m| m.name == name) {
                    return Some(scc);
                }
            }
        }
        None
    }

    /// True if a combinator references a format outside the given SCC member set
    /// that itself needs a lifetime, or directly contains Bytes/Tail.
    fn scc_member_needs_lifetime(&self, member: &SccMember, members: &[String]) -> bool {
        match &member.body {
            SccMemberBody::Struct(s) => s.0.iter().any(|f| match f {
                vestir::StructField::Const { .. } => false,
                vestir::StructField::Dependent { combinator, .. }
                | vestir::StructField::Ordinary { combinator, .. } => {
                    self.combinator_needs_lifetime_scc(combinator, members)
                }
            }),
            SccMemberBody::Choice(c) => c
                .choices
                .iter()
                .any(|(_, comb)| self.combinator_needs_lifetime_scc(comb, members)),
            SccMemberBody::Combinator(c) => self.combinator_needs_lifetime_scc(c, members),
        }
    }

    fn combinator_needs_lifetime_scc(&self, combinator: &Combinator, members: &[String]) -> bool {
        match combinator {
            Combinator::Bytes(_) | Combinator::Tail(_) => true,
            Combinator::Invocation(inv) => {
                if members.contains(&inv.func) {
                    false // in-SCC: lifetime shared; don't count it as a source here
                } else {
                    self.infos.get(&inv.func).is_some_and(|i| i.needs_lifetime)
                }
            }
            Combinator::AndThen(_, rhs) => self.combinator_needs_lifetime_scc(rhs, members),
            Combinator::Vec(vestir::VecCombinator::Vec(c))
            | Combinator::Array(vestir::ArrayCombinator { combinator: c, .. })
            | Combinator::Option(vestir::OptionCombinator(c)) => {
                self.combinator_needs_lifetime_scc(c, members)
            }
            Combinator::Wrap(vestir::WrapCombinator { combinator: c, .. }) => {
                self.combinator_needs_lifetime_scc(c, members)
            }
            _ => false,
        }
    }

    /// Look up a definition by its format name.
    pub(crate) fn def_by_name(&self, name: &str) -> Option<&'a Definition> {
        self.defs
            .iter()
            .find(|def| definition_name(def) == Some(name))
    }

    /// Names of all formats in dependency order (a format's callees come before it).
    ///
    /// This makes [`Analysis::new`] independent of the order definitions are given
    /// in. The call graph among generated formats is acyclic; if a cycle is ever
    /// encountered we fall back to the input order.
    fn dependency_order(&self) -> Vec<String> {
        use crate::utils::{tarjan_scc, VestHasherBuilder};

        // Build a name set covering both flat defs and SCC members.
        let mut names: std::collections::HashSet<String> = std::collections::HashSet::new();
        for def in self.defs {
            match def {
                Definition::RecursiveScc(scc) => {
                    for m in &scc.members {
                        names.insert(m.name.clone());
                    }
                }
                other => {
                    if let Some(n) = definition_name(other) {
                        names.insert(n.to_string());
                    }
                }
            }
        }

        // Build the full call graph.
        let mut graph: HashMap<String, Vec<String>, VestHasherBuilder> =
            HashMap::with_hasher(VestHasherBuilder);
        for def in self.defs {
            match def {
                Definition::RecursiveScc(scc) => {
                    for m in &scc.members {
                        let deps = scc_member_dependencies(m)
                            .into_iter()
                            .filter(|d| names.contains(d))
                            .collect();
                        graph.insert(m.name.clone(), deps);
                    }
                }
                other => {
                    if let Some(name) = definition_name(other) {
                        let deps = definition_dependencies(other)
                            .into_iter()
                            .filter(|d| names.contains(d.as_str()))
                            .collect();
                        graph.insert(name.to_string(), deps);
                    }
                }
            }
        }

        // Use Tarjan SCC to get callee-before-caller order; flatten.
        // Convert to standard HashMap first (tarjan_scc expects std::collections::HashMap).
        let std_graph: std::collections::HashMap<String, Vec<String>> = graph.into_iter().collect();
        tarjan_scc(&std_graph).into_iter().flatten().collect()
    }

    pub(crate) fn info(&self, name: &str) -> &FormatInfo {
        self.infos
            .get(name)
            .unwrap_or_else(|| panic!("missing format info for `{name}`"))
    }

    pub(crate) fn scc_info_for(&self, name: &str) -> Option<&SccInfo> {
        self.scc_of.get(name).map(|&idx| &self.sccs[idx])
    }

    pub(crate) fn recursive_member_for(&self, name: &str) -> Option<&'a SccMember> {
        let (scc_idx, member_idx) = *self.scc_member_of.get(name)?;
        let def_idx = *self.scc_def_indices.get(scc_idx)?;
        match &self.defs[def_idx] {
            Definition::RecursiveScc(scc) => scc.members.get(member_idx),
            _ => None,
        }
    }

    pub(crate) fn eval_const_length_expr(&self, len: &LengthExpr) -> Option<usize> {
        match &len.kind {
            vestir::LengthExprKind::Const(n) => Some(*n),
            vestir::LengthExprKind::Dependent(_) => None,
            vestir::LengthExprKind::SizeOf(name) => self.ctx.static_sizes.get(name).copied(),
            vestir::LengthExprKind::BinOp { op, left, right } => {
                let left = self.eval_const_length_expr(left)?;
                let right = self.eval_const_length_expr(right)?;
                match op {
                    vestir::ArithOp::Add => left.checked_add(right),
                    vestir::ArithOp::Sub => left.checked_sub(right),
                    vestir::ArithOp::Mul => left.checked_mul(right),
                    vestir::ArithOp::Div => left.checked_div(right),
                }
            }
        }
    }

    pub(crate) fn bits_layout(&self, bits_comb: &vestir::BitsCombinator) -> BitsLayout {
        let mut fields = Vec::new();
        let mut total_width = 0u16;
        let mut field_widths = Vec::new();
        for field in &bits_comb.0 {
            let w = self.bits_field_width(field);
            field_widths.push(w);
            total_width += w as u16;
        }
        let repr_width = match total_width {
            8 => 8,
            16 => 16,
            24 => 24,
            32 => 32,
            64 => 64,
            _ => panic!("unsupported bitfield total width {}", total_width),
        };
        let repr_int = vestir::IntCombinator::Unsigned(repr_width);
        let mut current_shift = repr_width;
        for (idx, field) in bits_comb.0.iter().enumerate() {
            let label = match field {
                vestir::BitField::Dependent { label, .. }
                | vestir::BitField::Ordinary { label, .. } => label.clone(),
            };
            let logical_width = field_widths[idx];
            current_shift -= logical_width;
            let shift = current_shift;
            let mask = if logical_width == 64 {
                u64::MAX
            } else {
                (1u64 << logical_width) - 1
            };
            let (is_enum, is_closed_enum, enum_name) = match field.combinator() {
                vestir::BitFieldCombinator::Enum(inv) => {
                    let is_closed = matches!(
                        self.defs
                            .iter()
                            .find(|d| d.name() == Some(inv.func.as_str())),
                        Some(vestir::Definition::EnumDef {
                            combinator: EnumCombinator::Exhaustive { .. },
                            ..
                        })
                    );
                    (true, is_closed, Some(inv.func.clone()))
                }
                _ => (false, false, None),
            };
            let carrier_ty = match field.combinator() {
                vestir::BitFieldCombinator::UInt(_) => {
                    vestir::IntCombinator::Unsigned(logical_width)
                }
                vestir::BitFieldCombinator::Enum(inv) => {
                    let def = self
                        .defs
                        .iter()
                        .find(|d| d.name() == Some(inv.func.as_str()))
                        .unwrap();
                    match def {
                        vestir::Definition::EnumDef { combinator, .. } => match combinator {
                            EnumCombinator::Exhaustive { inferred, .. }
                            | EnumCombinator::NonExhaustive { inferred, .. } => inferred.clone(),
                        },
                        _ => panic!("expected enum def"),
                    }
                }
            };
            fields.push(BitsFieldLayout {
                label,
                logical_width,
                carrier_ty,
                mask,
                shift,
                is_enum,
                is_closed_enum,
                enum_name,
            });
        }
        BitsLayout { repr_int, fields }
    }

    pub(crate) fn bits_field_width(&self, field: &vestir::BitField) -> u8 {
        match field.combinator() {
            vestir::BitFieldCombinator::UInt(c) => match c.combinator {
                vestir::IntCombinator::Unsigned(bits) => bits,
                _ => panic!("invalid bitfield integer {:?}", c.combinator),
            },
            vestir::BitFieldCombinator::Enum(inv) => {
                let def = self
                    .defs
                    .iter()
                    .find(|d| d.name() == Some(inv.func.as_str()))
                    .unwrap_or_else(|| panic!("unknown bitfield enum {}", inv.func));
                match def {
                    vestir::Definition::EnumDef { combinator, .. } => match combinator {
                        EnumCombinator::Exhaustive { inferred, .. }
                        | EnumCombinator::NonExhaustive { inferred, .. } => match inferred {
                            vestir::IntCombinator::Unsigned(bits) => *bits,
                            _ => panic!("bitfield enum must be unsigned"),
                        },
                    },
                    _ => panic!("bitfield member {} is not an enum", inv.func),
                }
            }
        }
    }

    pub(crate) fn render_value_type(&self, combinator: &Combinator, mode: TypeMode) -> TokenStream {
        self.render_value_type_scc(combinator, mode, &[])
    }

    /// Like `render_value_type` but boxes in-SCC references.
    pub(crate) fn render_value_type_scc(
        &self,
        combinator: &Combinator,
        mode: TypeMode,
        scc_members: &[String],
    ) -> TokenStream {
        if let Combinator::Invocation(invocation) = combinator {
            return self.render_nominal_type_scc(&invocation.func, mode, scc_members);
        }

        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(ConstraintIntCombinator { combinator, .. }) => {
                self.render_int_type(combinator)
            }
            Combinator::ConstraintEnum(ConstraintEnumCombinator { combinator, .. }) => {
                self.render_nominal_type_scc(&combinator.func, mode, scc_members)
            }
            Combinator::Wrap(WrapCombinator { combinator, .. }) => {
                self.render_value_type_scc(combinator, mode, scc_members)
            }
            Combinator::Vec(VecCombinator::Vec(combinator)) => {
                let inner_ty = self.render_value_type_scc(combinator, mode, scc_members);
                match mode {
                    TypeMode::Exec => quote! { Vec<#inner_ty> },
                    TypeMode::Spec => quote! { Seq<#inner_ty> },
                }
            }
            Combinator::Array(ArrayCombinator { combinator, len }) => {
                let inner_ty = self.render_value_type_scc(combinator, mode, scc_members);
                match (mode, self.eval_const_length_expr(len)) {
                    (TypeMode::Exec, Some(n)) => {
                        let n = syn_usize(n);
                        quote! { [#inner_ty; #n] }
                    }
                    (TypeMode::Exec, None) => quote! { Vec<#inner_ty> },
                    (TypeMode::Spec, _) => quote! { Seq<#inner_ty> },
                }
            }
            Combinator::Bytes(_) | Combinator::Tail(TailCombinator) => match mode {
                TypeMode::Exec => quote! { &'i [u8] },
                TypeMode::Spec => quote! { Seq<u8> },
            },
            Combinator::Empty => quote! { () },
            Combinator::Void(_) => quote! { Never },
            Combinator::Option(OptionCombinator(combinator)) => {
                let inner_ty = self.render_value_type_scc(combinator, mode, scc_members);
                quote! { Option<#inner_ty> }
            }
            Combinator::Invocation(invocation) => {
                self.render_nominal_type_scc(&invocation.func, mode, scc_members)
            }
            Combinator::AndThen(_, rhs) => self.render_value_type_scc(rhs, mode, scc_members),
        }
    }

    pub(crate) fn render_nominal_type(&self, dsl_name: &str, mode: TypeMode) -> TokenStream {
        self.render_nominal_type_scc(dsl_name, mode, &[])
    }

    pub(crate) fn render_nominal_type_scc(
        &self,
        dsl_name: &str,
        mode: TypeMode,
        scc_members: &[String],
    ) -> TokenStream {
        let info = self.info(dsl_name);
        let ident = match mode {
            TypeMode::Exec => format_ident!("{}", info.names.exec),
            TypeMode::Spec => format_ident!("{}", info.names.spec),
        };
        let base = if matches!(mode, TypeMode::Exec) && info.needs_lifetime {
            quote! { #ident <'i> }
        } else {
            quote! { #ident }
        };
        // Box in-SCC references to break the recursive type.
        if scc_members.contains(&dsl_name.to_string()) {
            quote! { Box< #base > }
        } else {
            base
        }
    }
    pub(crate) fn render_choice_sum_type(&self, branch_types: &[TokenStream]) -> TokenStream {
        match branch_types {
            [] => quote! { () },
            [only] => only.clone(),
            branches => {
                let middle = branches.len() / 2;
                let left = self.render_choice_sum_type(&branches[..middle]);
                let right = self.render_choice_sum_type(&branches[middle..]);
                quote! { Sum<#left, #right> }
            }
        }
    }

    pub(crate) fn render_int_type(&self, combinator: &vestir::IntCombinator) -> TokenStream {
        match combinator {
            vestir::IntCombinator::Signed(bits) => {
                let carrier: u32 = match bits {
                    1..=8 => 8,
                    9..=16 => 16,
                    17..=32 => 32,
                    33..=64 => 64,
                    _ => panic!("unsupported signed integer width {}", bits),
                };
                let ident = format_ident!("i{}", carrier);
                quote! { #ident }
            }
            vestir::IntCombinator::Unsigned(bits) => {
                let carrier: u32 = match bits {
                    1..=8 => 8,
                    9..=16 => 16,
                    17..=32 => 32,
                    33..=64 => 64,
                    _ => panic!("unsupported unsigned integer width {}", bits),
                };
                let ident = format_ident!("u{}", carrier);
                quote! { #ident }
            }
            vestir::IntCombinator::BtcVarint => quote! { u64 },
            vestir::IntCombinator::ULEB128 => quote! { u64 },
        }
    }

    pub(crate) fn render_int_combinator_ty(&self, combinator: &IntCombinator) -> TokenStream {
        match combinator {
            IntCombinator::Unsigned(8) => quote! { U8 },
            IntCombinator::Unsigned(16) => match self.endianness {
                vestir::Endianess::Little => quote! { U16Le },
                vestir::Endianess::Big => quote! { U16Be },
            },
            IntCombinator::Unsigned(24) => match self.endianness {
                vestir::Endianess::Little => quote! { U24Le },
                vestir::Endianess::Big => quote! { U24Be },
            },
            IntCombinator::Unsigned(32) => match self.endianness {
                vestir::Endianess::Little => quote! { U32Le },
                vestir::Endianess::Big => quote! { U32Be },
            },
            IntCombinator::Unsigned(64) => match self.endianness {
                vestir::Endianess::Little => quote! { U64Le },
                vestir::Endianess::Big => quote! { U64Be },
            },
            IntCombinator::BtcVarint => quote! { VarInt<true> },
            IntCombinator::ULEB128 => quote! { ULeb128<true, 10> },
            // Unsupported widths are rejected during type checking
            // (`check_int_combinator_supported`), so reaching this arm is an internal error.
            other => panic!(
                "internal error: unsupported integer combinator reached the spec emitter: {:?}",
                other
            ),
        }
    }

    pub(crate) fn render_int_combinator_expr(&self, combinator: &IntCombinator) -> TokenStream {
        match combinator {
            IntCombinator::Unsigned(8) => quote! { U8 },
            IntCombinator::Unsigned(16) => match self.endianness {
                vestir::Endianess::Little => quote! { U16Le },
                vestir::Endianess::Big => quote! { U16Be },
            },
            IntCombinator::Unsigned(24) => match self.endianness {
                vestir::Endianess::Little => quote! { U24Le },
                vestir::Endianess::Big => quote! { U24Be },
            },
            IntCombinator::Unsigned(32) => match self.endianness {
                vestir::Endianess::Little => quote! { U32Le },
                vestir::Endianess::Big => quote! { U32Be },
            },
            IntCombinator::Unsigned(64) => match self.endianness {
                vestir::Endianess::Little => quote! { U64Le },
                vestir::Endianess::Big => quote! { U64Be },
            },
            IntCombinator::BtcVarint => quote! { VarInt::<true> },
            IntCombinator::ULEB128 => quote! { ULeb128::<true, 10> },
            other => panic!(
                "unsupported integer combinator in spec emitter: {:?}",
                other
            ),
        }
    }

    pub(crate) fn render_length_expr_with<F>(
        &self,
        len: &LengthExpr,
        render_dep: &F,
        cast_ty: Option<&TokenStream>,
    ) -> TokenStream
    where
        F: Fn(&str) -> TokenStream,
    {
        match &len.kind {
            vestir::LengthExprKind::Const(n) => {
                let lit = proc_macro2::Literal::usize_unsuffixed(*n);
                quote! { #lit }
            }
            vestir::LengthExprKind::Dependent(name) => render_dep(name),
            vestir::LengthExprKind::SizeOf(name) => {
                if let Some(n) = self.ctx.static_sizes.get(name) {
                    let lit = proc_macro2::Literal::usize_unsuffixed(*n);
                    quote! { #lit }
                } else {
                    let fmt_ident = format_ident!("{}Spec", self.info(name).names.fmt);
                    quote! { <#fmt_ident as StaticByteLen>::static_byte_len() }
                }
            }
            vestir::LengthExprKind::BinOp { op, left, right } => {
                let left = self.render_length_expr_with(left, render_dep, cast_ty);
                let right = self.render_length_expr_with(right, render_dep, cast_ty);
                let expr = match op {
                    vestir::ArithOp::Add => quote! { (#left + #right) },
                    vestir::ArithOp::Sub => quote! { (#left - #right) },
                    vestir::ArithOp::Mul => quote! { (#left * #right) },
                    vestir::ArithOp::Div => quote! { (#left / #right) },
                };
                match cast_ty {
                    Some(ty) => quote! { (#expr as #ty) },
                    None => expr,
                }
            }
        }
    }

    pub(crate) fn render_const_array_expr(
        &self,
        array: &ConstArray,
        mode: TypeMode,
    ) -> TokenStream {
        match array {
            ConstArray::Char(bytes) => {
                let elems = bytes
                    .iter()
                    .map(|b| {
                        let hex_str = match mode {
                            TypeMode::Exec => format!("0x{:02x}", *b),
                            TypeMode::Spec => format!("0x{:02x}u8", *b),
                        };
                        hex_str.parse::<TokenStream>().unwrap()
                    })
                    .collect::<Vec<_>>();
                quote! { [#(#elems),*] }
            }
            ConstArray::Int(values) => {
                let elems = values
                    .iter()
                    .map(|v| {
                        if (0..=u8::MAX as i128).contains(v) {
                            let hex_str = match mode {
                                TypeMode::Exec => format!("0x{:02x}", *v as u8),
                                TypeMode::Spec => format!("0x{:02x}u8", *v as u8),
                            };
                            hex_str.parse::<TokenStream>().unwrap()
                        } else {
                            panic!("integer literal {} is too large to fit in a byte", v);
                        }
                    })
                    .collect::<Vec<_>>();
                quote! { [#(#elems),*] }
            }
            ConstArray::Repeat(value, len) => {
                let value_stream = if (0..=u8::MAX as i128).contains(value) {
                    let hex_str = match mode {
                        TypeMode::Exec => format!("0x{:02x}", *value as u8),
                        TypeMode::Spec => format!("0x{:02x}u8", *value as u8),
                    };
                    hex_str.parse::<TokenStream>().unwrap()
                } else {
                    let hex_str = if *value < 0 {
                        format!("-0x{:x}", value.abs())
                    } else {
                        format!("0x{:x}", *value)
                    };
                    hex_str.parse::<TokenStream>().unwrap()
                };
                let len_stream = syn_usize(*len);
                quote! { [#value_stream; #len_stream] }
            }
        }
    }

    pub(crate) fn render_constraint_elem_pred(
        &self,
        elem: &ConstraintElem,
        value: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        match elem {
            ConstraintElem::Single(v) => {
                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                quote! { #value == #lit }
            }
            ConstraintElem::Range { start, end } => {
                let lower = start.as_ref().map(|v| {
                    let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                    quote! { #value >= #lit }
                });
                let upper = end.as_ref().map(|v| {
                    let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                    quote! { #value <= #lit }
                });
                match (lower, upper) {
                    (Some(l), Some(u)) => quote! { #l && #u },
                    (Some(l), None) => l,
                    (None, Some(u)) => u,
                    (None, None) => quote! { true },
                }
            }
        }
    }

    pub(crate) fn render_int_constraint(
        &self,
        constraint: &vestir::IntConstraint,
        int_ty: &IntCombinator,
        value: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        match constraint {
            vestir::IntConstraint::Single(elem) => {
                self.render_constraint_elem_with_ty(elem, int_ty, value)
            }
            vestir::IntConstraint::Set(elems) => {
                let parts = elems
                    .iter()
                    .map(|elem| self.render_constraint_elem_with_ty(elem, int_ty, value.clone()))
                    .collect::<Vec<_>>();
                quote! { #(#parts)||* }
            }
            vestir::IntConstraint::Neg(inner) => {
                let inner = self.render_int_constraint(inner, int_ty, value);
                quote! { !(#inner) }
            }
        }
    }

    fn render_constraint_elem_with_ty(
        &self,
        elem: &ConstraintElem,
        int_ty: &IntCombinator,
        value: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        match elem {
            ConstraintElem::Single(v) => {
                let lit = int_literal(*v, int_ty);
                quote! { #value == #lit }
            }
            ConstraintElem::Range { start, end } => {
                let lower = start.as_ref().map(|v| {
                    let lit = int_literal(*v, int_ty);
                    quote! { #value >= #lit }
                });
                let upper = end.as_ref().map(|v| {
                    let lit = int_literal(*v, int_ty);
                    quote! { #value <= #lit }
                });
                match (lower, upper) {
                    (Some(l), Some(u)) => quote! { #l && #u },
                    (Some(l), None) => l,
                    (None, Some(u)) => u,
                    (None, None) => quote! { true },
                }
            }
        }
    }

    pub(crate) fn render_enum_constraint(
        &self,
        constraint: &vestir::EnumConstraint,
        enum_ty: &proc_macro2::TokenStream,
        value: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        match constraint {
            vestir::EnumConstraint::Single(name) => {
                let variant = format_ident!("{}", name);
                quote! { #value == #enum_ty::#variant }
            }
            vestir::EnumConstraint::Set(names) => {
                let parts = names.iter().map(|name| {
                    let variant = format_ident!("{}", name);
                    quote! { #value == #enum_ty::#variant }
                });
                quote! { #(#parts)||* }
            }
            vestir::EnumConstraint::Neg(inner) => {
                let inner = self.render_enum_constraint(inner, enum_ty, value);
                quote! { !(#inner) }
            }
        }
    }

    pub(crate) fn render_constraint_elem_pat(
        &self,
        elem: &ConstraintElem,
    ) -> proc_macro2::TokenStream {
        match elem {
            ConstraintElem::Single(v) => {
                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                quote! { #lit }
            }
            ConstraintElem::Range {
                start: Some(start),
                end: Some(end),
            } => {
                let start = proc_macro2::Literal::i128_unsuffixed(*start);
                let end = proc_macro2::Literal::i128_unsuffixed(*end);
                quote! { #start ..= #end }
            }
            _ => {
                let cond = self.render_constraint_elem_pred(elem, quote! { x });
                quote! { x if #cond }
            }
        }
    }

    pub(crate) fn choice_variant_names(&self, choice_comb: &ChoiceCombinator) -> Vec<String> {
        choice_comb
            .choices
            .iter()
            .enumerate()
            .map(|(idx, (pat, _))| match pat {
                ChoicePattern::Enum(name) => name.clone(),
                ChoicePattern::Int(_) => format!("Variant{}", idx + 1),
                ChoicePattern::Array(_) => format!("Variant{}", idx + 1),
                ChoicePattern::Wildcard => "Default".to_string(),
            })
            .collect()
    }

    pub(crate) fn wrapper_generics(&self, param_defns: &[ParamDefn]) -> TokenStream {
        if param_defns.iter().any(|p| self.param_needs_lifetime(p)) {
            quote! { <'i> }
        } else {
            quote! {}
        }
    }

    pub(crate) fn wrapper_spec_call_args(&self, param_defns: &[ParamDefn]) -> Vec<TokenStream> {
        param_defns
            .iter()
            .map(|param| match param {
                ParamDefn::Dependent { name, .. } => {
                    let accessor = FormatNames::wrapper_accessor_ident(name);
                    quote! { self.#accessor() }
                }
            })
            .collect()
    }

    pub(crate) fn param_needs_lifetime(&self, param: &ParamDefn) -> bool {
        match param {
            ParamDefn::Dependent { combinator, .. } => self.combinator_needs_lifetime(combinator),
        }
    }

    pub(crate) fn param_defns_for(&self, name: &str) -> &'a [ParamDefn] {
        if let Some(member) = self.recursive_member_for(name) {
            &member.param_defns
        } else if let Some(def) = self.definition_for(name) {
            def.param_defns()
        } else {
            &[]
        }
    }

    fn definition_for(&self, name: &str) -> Option<&'a Definition> {
        self.defs
            .iter()
            .find(|def| definition_name(def).is_some_and(|def_name| def_name == name))
    }

    fn choice_branches<'b>(&self, choice: &'b ChoiceCombinator) -> Vec<&'b Combinator> {
        choice
            .choices
            .iter()
            .map(|(_, combinator)| combinator)
            .collect()
    }

    fn definition_needs_lifetime(&self, def: &Definition) -> bool {
        match def {
            Definition::StructDef { combinator, .. } => self.struct_needs_lifetime(combinator),
            Definition::BitsDef { .. } => false,
            Definition::ChoiceDef { combinator, .. } => self.choice_needs_lifetime(combinator),
            Definition::EnumDef { .. } => false,
            Definition::CombinatorDef { combinator, .. } => {
                self.combinator_needs_lifetime(combinator)
            }
            Definition::ConstCombinatorDef {
                const_combinator, ..
            } => self.const_needs_lifetime(const_combinator),
            Definition::Endianess(_) | Definition::RecursiveScc(_) => false,
        }
    }

    fn combinator_needs_lifetime(&self, combinator: &Combinator) -> bool {
        match combinator {
            Combinator::AndThen(_, rhs) => self.combinator_needs_lifetime(rhs),
            _ => self.inner_needs_lifetime(combinator),
        }
    }

    fn inner_needs_lifetime(&self, inner: &Combinator) -> bool {
        match self.ctx.resolve_alias(inner) {
            Combinator::ConstraintInt(_)
            | Combinator::ConstraintEnum(_)
            | Combinator::Empty
            | Combinator::Void(_) => false,
            Combinator::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
            }) => {
                prior.iter().any(|c| self.const_needs_lifetime(c))
                    || self.combinator_needs_lifetime(combinator)
                    || post.iter().any(|c| self.const_needs_lifetime(c))
            }
            Combinator::Vec(VecCombinator::Vec(combinator)) => {
                self.combinator_needs_lifetime(combinator)
            }
            Combinator::Array(ArrayCombinator { combinator, .. }) => {
                self.combinator_needs_lifetime(combinator)
            }
            Combinator::Bytes(_) | Combinator::Tail(_) => true,
            Combinator::Option(OptionCombinator(combinator)) => {
                self.combinator_needs_lifetime(combinator)
            }
            Combinator::Invocation(invocation) => self.info(&invocation.func).needs_lifetime,
            Combinator::AndThen(_, rhs) => self.combinator_needs_lifetime(rhs),
        }
    }

    fn struct_needs_lifetime(&self, struct_comb: &StructCombinator) -> bool {
        struct_comb.0.iter().any(|field| match field {
            StructField::Const { combinator, .. } => self.const_needs_lifetime(combinator),
            StructField::Dependent { combinator, .. }
            | StructField::Ordinary { combinator, .. } => {
                self.combinator_needs_lifetime(combinator)
            }
        })
    }

    fn choice_needs_lifetime(&self, choice: &ChoiceCombinator) -> bool {
        self.choice_branches(choice)
            .into_iter()
            .any(|branch| self.combinator_needs_lifetime(branch))
    }

    fn const_needs_lifetime(&self, combinator: &ConstCombinator) -> bool {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(_) => false,
            ConstCombinator::ConstInt(_) | ConstCombinator::ConstEnum(_) => false,
            ConstCombinator::ConstCombinatorInvocation(name) => self.info(name).needs_lifetime,
        }
    }

    /// Whether the specification rendered for `name` contains a literal
    /// `AndThen<Tail, _>` whose consistency proof needs the broadcast bridge.
    pub(crate) fn prepare_needs_tail_and_then_lemma(&self, name: &str) -> bool {
        self.def_by_name(name)
            .is_some_and(|def| self.definition_contains_tail_and_then(def))
    }

    fn definition_contains_tail_and_then(&self, def: &Definition) -> bool {
        match def {
            Definition::StructDef { combinator, .. } => {
                combinator.0.iter().any(|field| match field {
                    StructField::Const { .. } => false,
                    StructField::Dependent { combinator, .. }
                    | StructField::Ordinary { combinator, .. } => {
                        self.struct_field_contains_tail_and_then(combinator)
                    }
                })
            }
            Definition::ChoiceDef { combinator, .. } => self
                .choice_branches(combinator)
                .into_iter()
                .any(|branch| self.combinator_contains_tail_and_then(branch)),
            Definition::CombinatorDef { combinator, .. } => {
                self.combinator_contains_tail_and_then(combinator)
            }
            Definition::EnumDef { .. }
            | Definition::BitsDef { .. }
            | Definition::ConstCombinatorDef { .. }
            | Definition::Endianess(_)
            | Definition::RecursiveScc(_) => false,
        }
    }

    fn struct_field_contains_tail_and_then(&self, combinator: &Combinator) -> bool {
        if !matches!(combinator, Combinator::AndThen(_, _)) {
            match self.ctx.resolve_alias(combinator) {
                Combinator::Option(OptionCombinator(inner))
                | Combinator::Vec(VecCombinator::Vec(inner)) => {
                    return self.combinator_contains_tail_and_then(inner);
                }
                _ => {}
            }
        }
        self.combinator_contains_tail_and_then(combinator)
    }

    fn combinator_contains_tail_and_then(&self, combinator: &Combinator) -> bool {
        match combinator {
            Combinator::AndThen(lhs, rhs) => {
                if matches!(self.ctx.resolve_alias(lhs), Combinator::Bytes(_)) {
                    // This is rendered as ExactLen, so the outer AndThen disappears.
                    return self.combinator_contains_tail_and_then(rhs);
                }
                matches!(lhs.as_ref(), Combinator::Tail(_))
                    || self.combinator_contains_tail_and_then(lhs)
                    || self.combinator_contains_tail_and_then(rhs)
            }
            Combinator::Wrap(WrapCombinator { combinator, .. })
            | Combinator::Array(ArrayCombinator { combinator, .. })
            | Combinator::Option(OptionCombinator(combinator))
            | Combinator::Vec(VecCombinator::Vec(combinator)) => {
                self.combinator_contains_tail_and_then(combinator)
            }
            // Invocation specs stay behind their named format boundary.
            Combinator::Invocation(_)
            | Combinator::ConstraintInt(_)
            | Combinator::ConstraintEnum(_)
            | Combinator::Bytes(_)
            | Combinator::Tail(_)
            | Combinator::Empty
            | Combinator::Void(_) => false,
        }
    }

    fn definition_non_tail(&self, def: &Definition) -> bool {
        match def {
            Definition::StructDef { combinator, .. } => self.struct_non_tail_at(combinator, true),
            Definition::BitsDef { .. } => true,
            Definition::ChoiceDef { combinator, .. } => self.choice_non_tail_at(combinator, true),
            Definition::EnumDef { .. } => true,
            Definition::CombinatorDef { combinator, .. } => {
                self.combinator_non_tail_at(combinator, true)
            }
            Definition::ConstCombinatorDef {
                const_combinator, ..
            } => self.const_non_tail(const_combinator),
            Definition::Endianess(_) | Definition::RecursiveScc(_) => true,
        }
    }

    fn combinator_non_tail(&self, combinator: &Combinator) -> bool {
        self.combinator_non_tail_at(combinator, false)
    }

    fn combinator_non_tail_at(&self, combinator: &Combinator, tail_position: bool) -> bool {
        if let Combinator::AndThen(lhs, rhs) = combinator {
            return match self.ctx.resolve_alias(lhs) {
                Combinator::Bytes(_) => true,
                _ => self.combinator_non_tail_at(rhs, tail_position),
            };
        }
        match self.ctx.resolve_alias(combinator) {
            Combinator::Tail(_) => false,
            Combinator::ConstraintInt(_)
            | Combinator::ConstraintEnum(_)
            | Combinator::Bytes(_)
            | Combinator::Empty
            | Combinator::Void(_) => true,
            Combinator::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
            }) => {
                prior.iter().all(|c| self.const_non_tail(c))
                    && self.combinator_non_tail_at(combinator, tail_position)
                    && post.iter().all(|c| self.const_non_tail(c))
            }
            Combinator::Array(ArrayCombinator { combinator, .. }) => {
                self.combinator_non_tail(combinator)
            }
            Combinator::Option(OptionCombinator(combinator))
            | Combinator::Vec(VecCombinator::Vec(combinator)) => {
                !tail_position && self.combinator_non_tail(combinator)
            }
            Combinator::Invocation(invocation) => self.info(&invocation.func).non_tail,
            Combinator::AndThen(_, _) => unreachable!(),
        }
    }

    fn struct_non_tail_at(&self, struct_comb: &StructCombinator, tail_position: bool) -> bool {
        let mut at_tail = tail_position;
        for field in struct_comb.0.iter().rev() {
            let ok = match field {
                StructField::Const { combinator, .. } => self.const_non_tail(combinator),
                StructField::Dependent { combinator, .. }
                | StructField::Ordinary { combinator, .. } => {
                    self.combinator_non_tail_at(combinator, at_tail)
                }
            };
            if !ok {
                return false;
            }
            at_tail = false;
        }
        true
    }

    fn choice_non_tail_at(&self, choice: &ChoiceCombinator, tail_position: bool) -> bool {
        self.choice_branches(choice)
            .into_iter()
            .all(|branch| self.combinator_non_tail_at(branch, tail_position))
    }

    fn const_non_tail(&self, combinator: &ConstCombinator) -> bool {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(_)
            | ConstCombinator::ConstInt(_)
            | ConstCombinator::ConstEnum(_) => true,
            ConstCombinator::ConstCombinatorInvocation(name) => self.info(name).non_tail,
        }
    }

    fn definition_non_malleable(&self, def: &Definition) -> bool {
        match def {
            Definition::StructDef { combinator, .. } => self.struct_non_malleable(combinator),
            Definition::BitsDef { .. } => true,
            Definition::ChoiceDef { combinator, .. } => self.choice_non_malleable(combinator),
            Definition::EnumDef { .. } => true,
            Definition::CombinatorDef { combinator, .. } => {
                self.combinator_non_malleable(combinator)
            }
            Definition::ConstCombinatorDef {
                const_combinator, ..
            } => self.const_non_malleable(const_combinator),
            Definition::Endianess(_) | Definition::RecursiveScc(_) => true,
        }
    }

    fn combinator_non_malleable(&self, combinator: &Combinator) -> bool {
        if let Combinator::AndThen(_, rhs) = combinator {
            return self.combinator_non_malleable(rhs);
        }
        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(_)
            | Combinator::ConstraintEnum(_)
            | Combinator::Bytes(_)
            | Combinator::Empty
            | Combinator::Void(_) => true,
            Combinator::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
            }) => {
                prior.iter().all(|c| self.const_non_malleable(c))
                    && self.combinator_non_malleable(combinator)
                    && post.iter().all(|c| self.const_non_malleable(c))
            }
            Combinator::Tail(_) => true,
            Combinator::Vec(VecCombinator::Vec(combinator)) => {
                self.combinator_non_malleable(combinator)
            }
            Combinator::Array(ArrayCombinator { combinator, .. }) => {
                self.combinator_non_malleable(combinator)
            }
            Combinator::Option(OptionCombinator(combinator)) => {
                self.combinator_non_malleable(combinator)
            }
            Combinator::Invocation(invocation) => self.info(&invocation.func).non_malleable,
            Combinator::AndThen(_, _) => unreachable!(),
        }
    }

    fn struct_non_malleable(&self, struct_comb: &StructCombinator) -> bool {
        struct_comb.0.iter().all(|field| match field {
            StructField::Const { combinator, .. } => self.const_non_malleable(combinator),
            StructField::Dependent { combinator, .. }
            | StructField::Ordinary { combinator, .. } => self.combinator_non_malleable(combinator),
        })
    }

    fn choice_non_malleable(&self, choice: &ChoiceCombinator) -> bool {
        self.choice_branches(choice)
            .into_iter()
            .all(|branch| self.combinator_non_malleable(branch))
    }

    fn const_non_malleable(&self, combinator: &ConstCombinator) -> bool {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(_)
            | ConstCombinator::ConstInt(_)
            | ConstCombinator::ConstEnum(_) => true,
            ConstCombinator::ConstCombinatorInvocation(name) => self.info(name).non_malleable,
        }
    }

    pub(crate) fn is_copyable(&self, name: &str) -> bool {
        let def = self.defs.iter().find(|d| d.name() == Some(name));
        match def {
            Some(Definition::StructDef { combinator, .. }) => {
                combinator.0.iter().all(|field| match field {
                    StructField::Const { .. } => true,
                    StructField::Dependent { combinator, .. }
                    | StructField::Ordinary { combinator, .. } => {
                        self.combinator_is_copyable(combinator)
                    }
                })
            }
            Some(Definition::BitsDef { .. }) => true,
            Some(Definition::ChoiceDef { combinator, .. }) => combinator
                .choices
                .iter()
                .all(|(_, comb)| self.combinator_is_copyable(comb)),
            Some(Definition::EnumDef { .. }) => true,
            Some(Definition::CombinatorDef { combinator, .. }) => {
                self.combinator_is_copyable(combinator)
            }
            Some(Definition::ConstCombinatorDef { .. }) => true,
            _ => true,
        }
    }

    pub(crate) fn combinator_is_copyable(&self, combinator: &Combinator) -> bool {
        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(_) => true,
            Combinator::ConstraintEnum(_) => true,
            Combinator::Wrap(wrap) => self.combinator_is_copyable(&wrap.combinator),
            Combinator::Vec(_) => false,
            Combinator::Array(arr) => {
                self.eval_const_length_expr(&arr.len).is_some()
                    && self.combinator_is_copyable(&arr.combinator)
            }
            Combinator::Bytes(_) | Combinator::Tail(_) => true,
            Combinator::Empty | Combinator::Void(_) => true,
            Combinator::Option(OptionCombinator(inner)) => self.combinator_is_copyable(inner),
            Combinator::Invocation(invocation) => self.is_copyable(&invocation.func),
            Combinator::AndThen(_, rhs) => self.combinator_is_copyable(rhs),
        }
    }

    pub(crate) fn is_selfview(&self, name: &str) -> bool {
        let def = self.defs.iter().find(|d| d.name() == Some(name));
        match def {
            // Generated structs and choices deliberately use distinct, generic spec datatypes.
            // This keeps a child's concrete datatype definition behind its nominal format
            // boundary instead of recursively expanding it in enclosing mapper obligations.
            Some(Definition::StructDef { .. }) => false,
            Some(Definition::BitsDef { .. }) => true,
            Some(Definition::ChoiceDef { .. }) => false,
            Some(Definition::EnumDef { .. }) => true,
            Some(Definition::CombinatorDef { combinator, .. }) => {
                self.combinator_is_selfview(combinator)
            }
            Some(Definition::ConstCombinatorDef {
                const_combinator, ..
            }) => self.const_combinator_is_selfview(const_combinator),
            _ => true,
        }
    }

    pub(crate) fn combinator_is_selfview(&self, combinator: &Combinator) -> bool {
        if !self.combinator_is_copyable(combinator) {
            return false;
        }
        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(_) => true,
            Combinator::ConstraintEnum(_) => true,
            Combinator::Wrap(wrap) => self.combinator_is_selfview(&wrap.combinator),
            Combinator::Vec(_) => false,
            Combinator::Array(arr) => {
                self.eval_const_length_expr(&arr.len).is_some()
                    && self.combinator_is_selfview(&arr.combinator)
            }
            Combinator::Bytes(_) | Combinator::Tail(_) => false,
            Combinator::Empty | Combinator::Void(_) => true,
            Combinator::Option(OptionCombinator(inner)) => self.combinator_is_selfview(inner),
            Combinator::Invocation(invocation) => self.is_selfview(&invocation.func),
            Combinator::AndThen(_, rhs) => self.combinator_is_selfview(rhs),
        }
    }

    pub(crate) fn const_combinator_is_selfview(&self, combinator: &ConstCombinator) -> bool {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(_) => false,
            ConstCombinator::ConstInt(_) | ConstCombinator::ConstEnum(_) => true,
            ConstCombinator::ConstCombinatorInvocation(name) => self.is_selfview(name),
        }
    }
}

pub(crate) fn definition_name(def: &Definition) -> Option<&str> {
    match def {
        Definition::StructDef { name, .. }
        | Definition::BitsDef { name, .. }
        | Definition::ChoiceDef { name, .. }
        | Definition::EnumDef { name, .. }
        | Definition::CombinatorDef { name, .. }
        | Definition::ConstCombinatorDef { name, .. } => Some(name),
        Definition::Endianess(_) | Definition::RecursiveScc(_) => None,
    }
}

/// Names of the formats directly invoked by `def` (a superset of the formats whose
/// [`FormatInfo`] is queried while analysing `def`). Used to order analysis so that
/// callees are processed before callers.
pub(crate) fn definition_dependencies(def: &Definition) -> Vec<String> {
    let mut out = Vec::new();
    match def {
        Definition::StructDef { combinator, .. } => {
            collect_struct_invocations(combinator, &mut out)
        }
        Definition::ChoiceDef { combinator, .. } => {
            collect_choice_invocations(combinator, &mut out)
        }
        Definition::BitsDef { combinator, .. } => collect_bits_invocations(combinator, &mut out),
        Definition::CombinatorDef { combinator, .. } => {
            collect_combinator_invocations(combinator, &mut out)
        }
        Definition::ConstCombinatorDef {
            const_combinator, ..
        } => collect_const_invocations(const_combinator, &mut out),
        Definition::EnumDef { .. } | Definition::Endianess(_) | Definition::RecursiveScc(_) => {}
    }
    out
}

fn collect_combinator_invocations(combinator: &Combinator, out: &mut Vec<String>) {
    match combinator {
        Combinator::ConstraintInt(_)
        | Combinator::Bytes(_)
        | Combinator::Tail(_)
        | Combinator::Empty
        | Combinator::Void(_) => {}
        Combinator::ConstraintEnum(ce) => out.push(ce.combinator.func.clone()),
        Combinator::Wrap(WrapCombinator {
            prior,
            combinator,
            post,
        }) => {
            prior.iter().for_each(|c| collect_const_invocations(c, out));
            collect_combinator_invocations(combinator, out);
            post.iter().for_each(|c| collect_const_invocations(c, out));
        }
        Combinator::Vec(VecCombinator::Vec(inner)) => collect_combinator_invocations(inner, out),
        Combinator::Array(ArrayCombinator { combinator, .. }) => {
            collect_combinator_invocations(combinator, out)
        }
        Combinator::Option(OptionCombinator(inner)) => collect_combinator_invocations(inner, out),
        Combinator::Invocation(inv) => out.push(inv.func.clone()),
        Combinator::AndThen(lhs, rhs) => {
            collect_combinator_invocations(lhs, out);
            collect_combinator_invocations(rhs, out);
        }
    }
}

fn collect_const_invocations(const_combinator: &ConstCombinator, out: &mut Vec<String>) {
    match const_combinator {
        ConstCombinator::ConstBytes(_) | ConstCombinator::ConstInt(_) => {}
        ConstCombinator::ConstEnum(ce) => out.push(ce.combinator.func.clone()),
        ConstCombinator::ConstCombinatorInvocation(name) => out.push(name.clone()),
    }
}

fn collect_struct_invocations(struct_comb: &StructCombinator, out: &mut Vec<String>) {
    for field in &struct_comb.0 {
        match field {
            StructField::Dependent { combinator, .. }
            | StructField::Ordinary { combinator, .. } => {
                collect_combinator_invocations(combinator, out)
            }
            StructField::Const { combinator, .. } => collect_const_invocations(combinator, out),
        }
    }
}

fn collect_choice_invocations(choice: &ChoiceCombinator, out: &mut Vec<String>) {
    for (_, combinator) in &choice.choices {
        collect_combinator_invocations(combinator, out);
    }
}

fn collect_bits_invocations(bits_comb: &vestir::BitsCombinator, out: &mut Vec<String>) {
    for field in &bits_comb.0 {
        if let vestir::BitFieldCombinator::Enum(inv) = field.combinator() {
            out.push(inv.func.clone());
        }
    }
}

/// Dependencies of a single SCC member (same logic as `definition_dependencies` for its body).
pub(crate) fn scc_member_dependencies(member: &SccMember) -> Vec<String> {
    let mut out = Vec::new();
    match &member.body {
        SccMemberBody::Struct(s) => collect_struct_invocations(s, &mut out),
        SccMemberBody::Choice(c) => collect_choice_invocations(c, &mut out),
        SccMemberBody::Combinator(c) => collect_combinator_invocations(c, &mut out),
    }
    out
}

/// Derive stable identifiers for an SCC from its 1-based index.
/// Returns `(which_ident, value_ident, rec_body_ident, param_ident)`.
pub(crate) fn scc_names(n: usize, _parameterized: bool) -> (String, String, String, String) {
    let which = format!("SCC{}Which", n);
    let value = format!("SCC{}", n);
    let rec_body = format!("SCC{}RecBody", n);
    let param = format!("SCC{}Param", n);
    (which, value, rec_body, param)
}

pub(crate) fn format_names(name: &str) -> FormatNames {
    let camel = name.to_upper_camel_case();
    FormatNames {
        dsl: name.to_string(),
        exec: camel.clone(),
        spec: format!("{camel}Spec"),
        inner: format!("{camel}Inner"),
        fmt: format!("{camel}Fmt"),
    }
}

pub(crate) fn tuple_chain(types: &[TokenStream]) -> TokenStream {
    match types {
        [] => quote! { () },
        [only] => only.clone(),
        [first, rest @ ..] => {
            let rest = tuple_chain(rest);
            quote! { (#first, #rest) }
        }
    }
}

pub(crate) fn type_needs_exec_lifetime(ty: &TokenStream) -> bool {
    ty.to_string().contains("'i")
}

pub(crate) fn syn_usize(n: usize) -> TokenStream {
    let lit = proc_macro2::Literal::usize_unsuffixed(n);
    quote! { #lit }
}

pub(crate) fn int_literal(value: i128, combinator: &vestir::IntCombinator) -> TokenStream {
    match combinator {
        vestir::IntCombinator::Unsigned(bits) if (1..=8).contains(bits) => {
            let lit = proc_macro2::Literal::u8_unsuffixed(value as u8);
            quote! { #lit }
        }
        vestir::IntCombinator::Unsigned(bits) if (9..=16).contains(bits) => {
            let lit = proc_macro2::Literal::u16_unsuffixed(value as u16);
            quote! { #lit }
        }
        vestir::IntCombinator::Unsigned(bits) if (17..=32).contains(bits) => {
            let lit = proc_macro2::Literal::u32_unsuffixed(value as u32);
            quote! { #lit }
        }
        vestir::IntCombinator::Unsigned(bits) if (33..=64).contains(bits) => {
            let lit = proc_macro2::Literal::u64_unsuffixed(value as u64);
            quote! { #lit }
        }
        vestir::IntCombinator::BtcVarint | vestir::IntCombinator::ULEB128 => {
            let lit = proc_macro2::Literal::u64_unsuffixed(value as u64);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(bits) if (1..=8).contains(bits) => {
            let lit = proc_macro2::Literal::i8_unsuffixed(value as i8);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(bits) if (9..=16).contains(bits) => {
            let lit = proc_macro2::Literal::i16_unsuffixed(value as i16);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(bits) if (17..=32).contains(bits) => {
            let lit = proc_macro2::Literal::i32_unsuffixed(value as i32);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(bits) if (33..=64).contains(bits) => {
            let lit = proc_macro2::Literal::i64_unsuffixed(value as i64);
            quote! { #lit }
        }
        other => panic!("unsupported integer literal combinator: {:?}", other),
    }
}

pub(crate) fn sum_pattern(idx: usize, total: usize, leaf_pat: TokenStream) -> TokenStream {
    assert!(idx < total, "sum branch index must be in bounds");
    if total == 1 {
        leaf_pat
    } else {
        let middle = total / 2;
        if idx < middle {
            let nested = sum_pattern(idx, middle, leaf_pat);
            quote! { L(#nested) }
        } else {
            let nested = sum_pattern(idx - middle, total - middle, leaf_pat);
            quote! { R(#nested) }
        }
    }
}

pub(crate) fn is_combinator_in_scc(c: &Combinator, members: &[String]) -> bool {
    matches!(c, Combinator::Invocation(inv) if members.contains(&inv.func))
}

pub(crate) fn get_invocation_name(c: &Combinator) -> &str {
    match c {
        Combinator::Invocation(inv) => &inv.func,
        _ => panic!("expected Invocation"),
    }
}
