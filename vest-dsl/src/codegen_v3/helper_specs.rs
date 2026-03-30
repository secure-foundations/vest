use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use proc_macro2::Ident;
use quote::format_ident;

use super::analysis::value_kind_for_comb;
use super::{AnalysisMap, CombDef, CombIR, DispatchBranchIR, ParamRef, ValType};

#[derive(Clone)]
pub(super) struct ValueBinding {
    pub ident: Ident,
    pub kind: ValType,
    pub mode: BindingUse,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum BindingUse {
    Plain,
    GenerateRef,
    ConstructorParam,
}

impl ValueBinding {
    pub fn uses_lifetime(&self) -> bool {
        matches!(self.mode, BindingUse::GenerateRef)
    }

    pub fn can_forward_generate_arg(&self) -> bool {
        !matches!(self.mode, BindingUse::Plain)
    }
}

pub(super) type BindingEnv = BTreeMap<String, ValueBinding>;

#[derive(Clone)]
pub(super) struct CapturedValue {
    pub name: String,
    pub kind: ValType,
}

#[derive(Clone)]
pub(super) struct DependentPairHelperSpec<'a> {
    pub path: Vec<usize>,
    pub fst: &'a CombIR,
    pub fst_bindings: &'a [String],
    pub snd: &'a CombIR,
    pub env: BindingEnv,
    pub captures: Vec<CapturedValue>,
    pub parse_env: BindingEnv,
    pub generate_env: BindingEnv,
}

#[derive(Clone)]
pub(super) struct DispatchEnumHelperSpec<'a> {
    pub path: Vec<usize>,
    pub branches: &'a [DispatchBranchIR],
    pub env: BindingEnv,
}

#[derive(Clone)]
pub(super) enum HelperSpec<'a> {
    Dep(DependentPairHelperSpec<'a>),
    Dispatch(DispatchEnumHelperSpec<'a>),
}

pub(super) struct CollectedHelperSpecs<'a> {
    ordered: Vec<HelperSpec<'a>>,
}

impl<'a> CollectedHelperSpecs<'a> {
    pub fn ordered(&self) -> &[HelperSpec<'a>] {
        &self.ordered
    }
}

pub(super) fn collect_helper_specs<'ir, 'defs, 'analysis>(
    comb: &'ir CombIR,
    env: &BindingEnv,
    defs: &'defs HashMap<String, &'ir CombDef>,
    analysis: &'analysis AnalysisMap,
) -> CollectedHelperSpecs<'ir> {
    let mut collector = HelperSpecCollector {
        defs,
        analysis,
        ordered: Vec::new(),
        seen_dep: HashSet::new(),
        seen_dispatch: HashSet::new(),
    };
    collector.visit(comb, env, &[]);
    CollectedHelperSpecs {
        ordered: collector.ordered,
    }
}

pub(super) fn scoped_helper_ident(prefix: &str, path: &[usize]) -> Ident {
    if path.is_empty() {
        format_ident!("{}", prefix)
    } else {
        let suffix = path
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join("_");
        format_ident!("{}{}", prefix, suffix)
    }
}

pub(super) fn child_path(path: &[usize], index: usize) -> Vec<usize> {
    let mut child = path.to_vec();
    child.push(index);
    child
}

pub(super) fn capture_names(
    used_names: &BTreeSet<String>,
    env: &BindingEnv,
    current_deps: &[String],
) -> Vec<String> {
    used_names
        .iter()
        .filter(|name| !current_deps.contains(name) && env.contains_key(*name))
        .cloned()
        .collect()
}

pub(super) fn used_names_in_comb(comb: &CombIR) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_used_names(comb, &mut names);
    names
}

struct HelperSpecCollector<'ir, 'defs, 'analysis> {
    defs: &'defs HashMap<String, &'ir CombDef>,
    analysis: &'analysis AnalysisMap,
    ordered: Vec<HelperSpec<'ir>>,
    seen_dep: HashSet<String>,
    seen_dispatch: HashSet<String>,
}

impl<'ir, 'defs, 'analysis> HelperSpecCollector<'ir, 'defs, 'analysis> {
    fn visit(&mut self, comb: &'ir CombIR, env: &BindingEnv, path: &[usize]) {
        match comb {
            CombIR::Struct(fields) => {
                for (idx, field) in fields.iter().enumerate() {
                    self.visit(&field.comb, env, &child_path(path, idx));
                }
            }
            CombIR::Seq(items) => {
                for (idx, item) in items.iter().enumerate() {
                    self.visit(item, env, &child_path(path, idx));
                }
            }
            CombIR::DepPair {
                fst,
                fst_bindings,
                snd,
            } => {
                let key = format!("dep_{}", helper_key(path));
                if self.seen_dep.insert(key) {
                    self.ordered.push(HelperSpec::Dep(self.dep_spec(
                        path.to_vec(),
                        fst,
                        fst_bindings,
                        snd,
                        env,
                    )));
                }

                self.visit(fst, env, &child_path(path, 0));

                let captures = captured_bindings(snd, env, fst_bindings);
                let mut parse_env = captured_env(&captures);
                bind_dep_names(
                    fst,
                    fst_bindings,
                    &mut parse_env,
                    self.defs,
                    self.analysis,
                    BindingUse::Plain,
                );
                self.visit(snd, &parse_env, &child_path(path, 1));
            }
            CombIR::Preceded { prefix, inner } => {
                self.visit(prefix, env, &child_path(path, 0));
                self.visit(inner, env, &child_path(path, 1));
            }
            CombIR::Terminated { inner, suffix } => {
                self.visit(inner, env, &child_path(path, 0));
                self.visit(suffix, env, &child_path(path, 1));
            }
            CombIR::Dispatch { branches, .. } => {
                let key = dispatch_helper_key(path);
                if self.seen_dispatch.insert(key) {
                    self.ordered
                        .push(HelperSpec::Dispatch(DispatchEnumHelperSpec {
                            path: path.to_vec(),
                            branches,
                            env: env.clone(),
                        }));
                }

                for (idx, branch) in branches.iter().enumerate() {
                    self.visit(&branch.comb, env, &child_path(path, idx));
                }
            }
            CombIR::Opt(inner)
            | CombIR::Repeat(inner)
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::Enum { inner, .. }
            | CombIR::Tag { inner, .. } => self.visit(inner, env, &child_path(path, 0)),
            CombIR::RepeatN { inner, .. } | CombIR::FixedLen { inner, .. } => {
                self.visit(inner, env, &child_path(path, 0));
            }
            CombIR::AndThen { len_comb, inner } => {
                self.visit(len_comb, env, &child_path(path, 0));
                self.visit(inner, env, &child_path(path, 1));
            }
            CombIR::UInt(_)
            | CombIR::Fixed { .. }
            | CombIR::Variable { .. }
            | CombIR::Tail
            | CombIR::Named { .. }
            | CombIR::End
            | CombIR::Success
            | CombIR::Fail(_) => {}
        }
    }

    fn dep_spec(
        &self,
        path: Vec<usize>,
        fst: &'ir CombIR,
        fst_bindings: &'ir [String],
        snd: &'ir CombIR,
        env: &BindingEnv,
    ) -> DependentPairHelperSpec<'ir> {
        let captures = captured_bindings(snd, env, fst_bindings);
        let mut parse_env = captured_env(&captures);
        bind_dep_names(
            fst,
            fst_bindings,
            &mut parse_env,
            self.defs,
            self.analysis,
            BindingUse::Plain,
        );
        let mut generate_env = captured_env(&captures);
        bind_dep_names(
            fst,
            fst_bindings,
            &mut generate_env,
            self.defs,
            self.analysis,
            BindingUse::GenerateRef,
        );

        DependentPairHelperSpec {
            path,
            fst,
            fst_bindings,
            snd,
            env: env.clone(),
            captures,
            parse_env,
            generate_env,
        }
    }
}

fn captured_bindings(
    comb: &CombIR,
    env: &BindingEnv,
    current_deps: &[String],
) -> Vec<CapturedValue> {
    capture_names(&used_names_in_comb(comb), env, current_deps)
        .into_iter()
        .map(|name| {
            let binding = &env[&name];
            CapturedValue {
                name,
                kind: binding.kind.clone(),
            }
        })
        .collect()
}

fn captured_env(captures: &[CapturedValue]) -> BindingEnv {
    captures
        .iter()
        .map(|capture| {
            (
                capture.name.clone(),
                ValueBinding {
                    ident: format_ident!("{}", capture.name),
                    kind: capture.kind.clone(),
                    mode: BindingUse::Plain,
                },
            )
        })
        .collect()
}

fn bind_dep_names(
    fst: &CombIR,
    dep_names: &[String],
    env: &mut BindingEnv,
    defs: &HashMap<String, &CombDef>,
    analysis: &AnalysisMap,
    mode: BindingUse,
) {
    if dep_names.is_empty() {
        return;
    }

    let dep_kinds = match fst {
        CombIR::Struct(fields) if dep_names.len() > 1 => fields
            .iter()
            .map(|field| value_kind_for_comb(&field.comb, defs, analysis))
            .collect::<Vec<_>>(),
        CombIR::Seq(items) if dep_names.len() > 1 => items
            .iter()
            .map(|item| value_kind_for_comb(item, defs, analysis))
            .collect::<Vec<_>>(),
        _ => vec![last_bound_kind(fst, defs, analysis)],
    };

    for (idx, name) in dep_names.iter().enumerate() {
        let kind = dep_kinds
            .get(idx)
            .cloned()
            .unwrap_or_else(|| last_bound_kind(fst, defs, analysis));
        env.insert(
            name.clone(),
            ValueBinding {
                ident: format_ident!("{}", name),
                kind,
                mode,
            },
        );
    }
}

fn last_bound_kind(
    comb: &CombIR,
    defs: &HashMap<String, &CombDef>,
    analysis: &AnalysisMap,
) -> ValType {
    match comb {
        CombIR::Struct(fields) if !fields.is_empty() => last_bound_kind(
            &fields.last().expect("non-empty struct").comb,
            defs,
            analysis,
        ),
        CombIR::Seq(items) if !items.is_empty() => {
            last_bound_kind(items.last().expect("non-empty seq"), defs, analysis)
        }
        CombIR::Struct(_) | CombIR::Seq(_) => ValType::Unit,
        other => value_kind_for_comb(other, defs, analysis),
    }
}

fn helper_key(path: &[usize]) -> String {
    if path.is_empty() {
        "root".to_string()
    } else {
        path.iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join("_")
    }
}

fn dispatch_helper_key(path: &[usize]) -> String {
    format!("dispatch_{}", helper_key(path))
}

fn collect_used_names(comb: &CombIR, names: &mut BTreeSet<String>) {
    match comb {
        CombIR::Variable { len } => collect_len_names(len, names),
        CombIR::Struct(fields) => {
            for field in fields {
                collect_used_names(&field.comb, names);
            }
        }
        CombIR::Seq(items) => {
            for item in items {
                collect_used_names(item, names);
            }
        }
        CombIR::DepPair { fst, snd, .. } => {
            collect_used_names(fst, names);
            collect_used_names(snd, names);
        }
        CombIR::Preceded { prefix, inner } => {
            collect_used_names(prefix, names);
            collect_used_names(inner, names);
        }
        CombIR::Terminated { inner, suffix } => {
            collect_used_names(inner, names);
            collect_used_names(suffix, names);
        }
        CombIR::Dispatch { tag, branches } => {
            names.insert(tag.clone());
            for branch in branches {
                collect_used_names(&branch.comb, names);
            }
        }
        CombIR::Opt(inner)
        | CombIR::Repeat(inner)
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::Enum { inner, .. }
        | CombIR::Tag { inner, .. } => collect_used_names(inner, names),
        CombIR::RepeatN { inner, count } => {
            collect_len_names(count, names);
            collect_used_names(inner, names);
        }
        CombIR::AndThen { len_comb, inner } => {
            collect_used_names(len_comb, names);
            collect_used_names(inner, names);
        }
        CombIR::FixedLen { len, inner } => {
            collect_len_names(len, names);
            collect_used_names(inner, names);
        }
        CombIR::Named { args, .. } => {
            for arg in args {
                let ParamRef::Dependent(name) = arg;
                names.insert(name.clone());
            }
        }
        CombIR::UInt(_)
        | CombIR::Fixed { .. }
        | CombIR::Tail
        | CombIR::End
        | CombIR::Success
        | CombIR::Fail(_) => {}
    }
}

fn collect_len_names(len: &crate::vestir::LengthExpr, names: &mut BTreeSet<String>) {
    match len {
        crate::vestir::LengthExpr::Const(_) | crate::vestir::LengthExpr::SizeOf(_) => {}
        crate::vestir::LengthExpr::Dependent(name) => {
            names.insert(name.clone());
        }
        crate::vestir::LengthExpr::BinOp { left, right, .. } => {
            collect_len_names(left, names);
            collect_len_names(right, names);
        }
    }
}
