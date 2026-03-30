use std::collections::{HashMap, HashSet};

use super::{peel_wrappers_for, wrapper_inner_for, CombDef, CombIR, UIntWidth, WrapperUse};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Analysis {
    pub needs_lifetime: bool,
    pub borrow_by_value: bool,
    pub emits_mapper: bool,
    pub value_kind: ValType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValType {
    UInt(UIntWidth),
    ByteSlice,
    Named(String),
    Unit,
    Tuple(Vec<ValType>),
    Option(Box<ValType>),
    Vec(Box<ValType>),
}

pub type AnalysisMap = HashMap<String, Analysis>;

pub fn analyze_definitions(defs: &[CombDef]) -> AnalysisMap {
    let def_map: HashMap<String, &CombDef> =
        defs.iter().map(|def| (def.name.clone(), def)).collect();

    defs.iter()
        .map(|def| (def.name.clone(), analyze_definition(def, &def_map)))
        .collect()
}

fn analyze_definition(def: &CombDef, def_map: &HashMap<String, &CombDef>) -> Analysis {
    let emits_mapper = comb_emits_mapper(&def.body);
    let is_dispatch = matches!(
        peel_wrappers_for(&def.body, WrapperUse::NominalRoot),
        CombIR::Dispatch { .. }
    );
    Analysis {
        needs_lifetime: comb_needs_lifetime(&def.body, def_map),
        borrow_by_value: comb_borrow_by_value(&def.body, def_map),
        emits_mapper,
        value_kind: if emits_mapper || is_dispatch {
            ValType::Named(def.name.clone())
        } else {
            analyzed_value_kind_for_comb(&def.body, def_map)
        },
    }
}

pub(crate) fn value_kind_for_comb(
    comb: &CombIR,
    def_map: &HashMap<String, &CombDef>,
    analysis: &AnalysisMap,
) -> ValType {
    value_kind_of_comb_inner(
        comb,
        def_map,
        Some(analysis),
        &mut HashSet::new(),
        CycleMode::Named,
    )
}

fn comb_needs_lifetime(comb: &CombIR, def_map: &HashMap<String, &CombDef>) -> bool {
    match comb {
        CombIR::Fixed { .. } | CombIR::Variable { .. } | CombIR::Tail => true,
        CombIR::Struct(fields) => fields
            .iter()
            .any(|field| comb_needs_lifetime(&field.comb, def_map)),
        CombIR::Seq(items) => items.iter().any(|item| comb_needs_lifetime(item, def_map)),
        CombIR::DepPair { fst, snd, .. } => {
            comb_needs_lifetime(fst, def_map) || comb_needs_lifetime(snd, def_map)
        }
        CombIR::Preceded { inner, .. } | CombIR::Terminated { inner, .. } => {
            comb_needs_lifetime(inner, def_map)
        }
        CombIR::Opt(inner)
        | CombIR::Repeat(inner)
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::AndThen { inner, .. }
        | CombIR::FixedLen { inner, .. }
        | CombIR::Enum { inner, .. }
        | CombIR::Tag { inner, .. } => comb_needs_lifetime(inner, def_map),
        CombIR::RepeatN { inner, .. } => comb_needs_lifetime(inner, def_map),
        CombIR::Dispatch { branches, .. } => branches
            .iter()
            .any(|branch| comb_needs_lifetime(&branch.comb, def_map)),
        CombIR::Named { name, .. } => def_map
            .get(name)
            .map(|def| comb_needs_lifetime(&def.body, def_map))
            .unwrap_or(false),
        CombIR::UInt(_) | CombIR::End | CombIR::Success | CombIR::Fail(_) => false,
    }
}

fn comb_borrow_by_value(comb: &CombIR, def_map: &HashMap<String, &CombDef>) -> bool {
    match comb {
        CombIR::UInt(_)
        | CombIR::Fixed { .. }
        | CombIR::Variable { .. }
        | CombIR::Tail
        | CombIR::End
        | CombIR::Success
        | CombIR::Fail(_) => true,
        CombIR::Struct(fields) => fields
            .iter()
            .all(|field| comb_borrow_by_value(&field.comb, def_map)),
        CombIR::Seq(items) => items.iter().all(|item| comb_borrow_by_value(item, def_map)),
        CombIR::Opt(inner) => comb_borrow_by_value(inner, def_map),
        CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
            comb_borrow_by_value(inner, def_map)
        }
        CombIR::Preceded { .. }
        | CombIR::Terminated { .. }
        | CombIR::Refined { .. }
        | CombIR::Mapped { .. }
        | CombIR::AndThen { .. }
        | CombIR::FixedLen { .. } => comb_borrow_by_value(
            wrapper_inner_for(comb, WrapperUse::ValueShape).expect("transparent wrapper"),
            def_map,
        ),
        CombIR::Tag { inner, .. } => comb_borrow_by_value(inner, def_map),
        CombIR::Enum { .. } => true,
        CombIR::Named { name, .. } => def_map
            .get(name)
            .map(|def| comb_borrow_by_value(&def.body, def_map))
            .unwrap_or(false),
        CombIR::DepPair { .. } | CombIR::Dispatch { .. } => false,
    }
}

fn comb_emits_mapper(comb: &CombIR) -> bool {
    match comb {
        CombIR::Struct(fields) => !fields.is_empty(),
        CombIR::Seq(items) => !items.is_empty(),
        CombIR::DepPair { .. } | CombIR::Enum { .. } => true,
        CombIR::Dispatch { .. } => false,
        CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::FixedLen { inner, .. }
        | CombIR::AndThen { inner, .. } => comb_emits_mapper(inner),
        _ => false,
    }
}

fn analyzed_value_kind_for_comb(comb: &CombIR, def_map: &HashMap<String, &CombDef>) -> ValType {
    value_kind_of_comb_inner(comb, def_map, None, &mut HashSet::new(), CycleMode::Panic)
}

#[derive(Clone, Copy)]
enum CycleMode {
    Panic,
    Named,
}

fn value_kind_of_comb_inner(
    comb: &CombIR,
    def_map: &HashMap<String, &CombDef>,
    analysis: Option<&AnalysisMap>,
    seen: &mut HashSet<String>,
    cycle_mode: CycleMode,
) -> ValType {
    match comb {
        CombIR::UInt(uint) => ValType::UInt(uint.width),
        CombIR::Fixed { .. } | CombIR::Variable { .. } | CombIR::Tail => ValType::ByteSlice,
        CombIR::Struct(fields) => ValType::Tuple(
            fields
                .iter()
                .map(|field| {
                    value_kind_of_comb_inner(&field.comb, def_map, analysis, seen, cycle_mode)
                })
                .collect(),
        ),
        CombIR::Seq(items) => ValType::Tuple(
            items
                .iter()
                .map(|item| value_kind_of_comb_inner(item, def_map, analysis, seen, cycle_mode))
                .collect(),
        ),
        CombIR::DepPair { fst, snd, .. } => ValType::Tuple(vec![
            value_kind_of_comb_inner(fst, def_map, analysis, seen, cycle_mode),
            value_kind_of_comb_inner(snd, def_map, analysis, seen, cycle_mode),
        ]),
        CombIR::Preceded { inner, .. }
        | CombIR::Terminated { inner, .. }
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::Enum { inner, .. }
        | CombIR::AndThen { inner, .. }
        | CombIR::FixedLen { inner, .. } => {
            value_kind_of_comb_inner(inner, def_map, analysis, seen, cycle_mode)
        }
        CombIR::Dispatch { branches, .. } => branches
            .first()
            .map(|branch| {
                value_kind_of_comb_inner(&branch.comb, def_map, analysis, seen, cycle_mode)
            })
            .unwrap_or(ValType::Unit),
        CombIR::Opt(inner) => ValType::Option(Box::new(value_kind_of_comb_inner(
            inner, def_map, analysis, seen, cycle_mode,
        ))),
        CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => ValType::Vec(Box::new(
            value_kind_of_comb_inner(inner, def_map, analysis, seen, cycle_mode),
        )),
        CombIR::Tag { .. } | CombIR::End | CombIR::Success | CombIR::Fail(_) => ValType::Unit,
        CombIR::Named { name, .. } => {
            if !seen.insert(name.clone()) {
                return match cycle_mode {
                    CycleMode::Panic => panic!(
                        "recursive named combinator value analysis is not supported for {}",
                        name
                    ),
                    CycleMode::Named => ValType::Named(name.clone()),
                };
            }
            let value = def_map
                .get(name)
                .map(|def| {
                    if named_def_uses_nominal_value(name, def, analysis) {
                        ValType::Named(name.clone())
                    } else {
                        value_kind_of_comb_inner(&def.body, def_map, analysis, seen, cycle_mode)
                    }
                })
                .unwrap_or_else(|| ValType::Named(name.clone()));
            seen.remove(name);
            value
        }
    }
}

fn named_def_uses_nominal_value(name: &str, def: &CombDef, analysis: Option<&AnalysisMap>) -> bool {
    analysis
        .and_then(|map| map.get(name))
        .map(|info| info.emits_mapper || matches!(info.value_kind, ValType::Named(_)))
        .unwrap_or_else(|| {
            matches!(
                peel_wrappers_for(&def.body, WrapperUse::NominalRoot),
                CombIR::Struct(_) | CombIR::Dispatch { .. } | CombIR::Enum { .. }
            ) || comb_emits_mapper(&def.body)
        })
}
