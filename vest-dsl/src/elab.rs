use std::collections::{HashMap, HashSet};

use crate::{ast::*, utils::topological_sort};

/// Elaborate the AST:
/// - expand the macro invocations
/// - expand the inlined, anonymous combinator definitions
/// - reorder the definitions according to the call graph (topological sort of the invocations)
pub fn elaborate(ast: &mut Vec<Definition>) {
    // expand the macro invocations
    expand_macros(ast);
    // for defn in ast.iter() {
    //     println!("{}", defn);
    // }

    // expand the inlined, anonymous combinator definitions
    expand_definitions(ast);

    // build the call graph
    let call_graph = build_call_graph(ast);
    // topo sort the call graph
    topological_sort(&call_graph)
        .map(|sorted| {
            // reorder the definitions
            ast.sort_by_cached_key(|defn| {
                // skip the endianness definition
                if let Definition::Endianess(_) = defn {
                    0
                } else {
                    sorted
                        .iter()
                        .position(|name_| match defn {
                            Definition::Combinator { name, .. } => name == name_,
                            Definition::ConstCombinator { name, .. } => name == name_,
                            _ => false,
                        })
                        .unwrap()
                }
            });
        })
        .unwrap_or_else(|e| {
            panic!("Cycle detected in the format definitions: {:?}", e);
        });
    // println!("Number of definitions: {}", ast.len());
}

pub struct ElabCtx<'ast> {
    pub dependencies: Vec<(String, CombinatorInner<'ast>)>,
}

impl<'ast> ElabCtx<'ast> {
    pub fn new() -> Self {
        Self {
            dependencies: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        self.dependencies.clear();
    }
}

type MacroDefn<'ast> = (Vec<String>, Combinator<'ast>);

/// Expand the macro invocations
fn expand_macros(ast: &mut Vec<Definition>) {
    // collect the macro definitions
    let mut macro_defns = HashMap::<String, MacroDefn>::new();
    for defn in ast.iter() {
        if let Definition::MacroDefn { name, params, body } = defn {
            macro_defns.insert(name.to_owned(), (params.clone(), body.clone()));
        }
    }
    // remove the macro definitions
    ast.retain(|defn| !matches!(defn, Definition::MacroDefn { .. }));
    // traverse the AST and expand the macro invocations "in-place"
    for defn in ast.iter_mut() {
        expand_macros_in_defn(defn, &macro_defns);
    }
}

fn expand_macros_in_defn<'ast>(
    defn: &mut Definition<'ast>,
    macro_defns: &HashMap<String, MacroDefn<'ast>>,
) {
    match defn {
        Definition::Combinator { combinator, .. } => {
            expand_macros_in_combinator(combinator, macro_defns);
        }
        Definition::ConstCombinator { .. } => {
            // TODO: we don't support top-level const definition rn; may add support in the future
        }
        _ => {}
    }
}

/// Expand the macro invocations in the combinator with the given macro definitions
fn expand_macros_in_combinator<'ast>(
    combinator: &mut Combinator<'ast>,
    macro_defns: &HashMap<String, MacroDefn<'ast>>,
) {
    if let Some(and_then) = &mut combinator.and_then {
        expand_macros_in_combinator(and_then, macro_defns);
    }
    expand_macros_in_combinator_inner(&mut combinator.inner, macro_defns);
}

fn expand_macros_in_combinator_inner<'ast>(
    combinator_inner: &mut CombinatorInner<'ast>,
    macro_defns: &HashMap<String, MacroDefn<'ast>>,
) {
    match combinator_inner {
        // base case
        CombinatorInner::MacroInvocation { name, args } => {
            if let Some((params, body)) = macro_defns.get(name) {
                let mut body_expanded = body.clone();
                for (param, arg) in std::iter::zip(params, args) {
                    substitute_in_combinator(&mut body_expanded, param, arg.to_owned());
                }
                *combinator_inner = body_expanded.inner;
            }
        } // recursive cases
        CombinatorInner::Struct(StructCombinator { fields, .. }) => {
            for field in fields {
                match field {
                    StructField::Ordinary { combinator, .. }
                    | StructField::Dependent { combinator, .. } => {
                        expand_macros_in_combinator(combinator, macro_defns);
                    }
                    StructField::Const { .. } => {
                        // TODO: skip const fields for now
                    }
                    _ => {}
                }
            }
        }
        CombinatorInner::Wrap(WrapCombinator {
            prior,
            combinator,
            post,
            ..
        }) => {
            for _combinator in prior {}
            expand_macros_in_combinator(combinator, macro_defns);
            for _combinator in post {}
        }
        CombinatorInner::Choice(ChoiceCombinator { choices, .. }) => match choices {
            Choices::Enums(enums) => {
                for (_, combinator) in enums {
                    expand_macros_in_combinator(combinator, macro_defns);
                }
            }
            Choices::Ints(ints) => {
                for (_, combinator) in ints {
                    expand_macros_in_combinator(combinator, macro_defns);
                }
            }
            Choices::Arrays(arrays) => {
                for (_, combinator) in arrays {
                    expand_macros_in_combinator(combinator, macro_defns);
                }
            }
        },
        CombinatorInner::Vec(combinator) => match combinator {
            VecCombinator::Vec(combinator) | VecCombinator::Vec1(combinator) => {
                expand_macros_in_combinator(combinator, macro_defns);
            }
        },
        CombinatorInner::Array(ArrayCombinator { combinator, .. }) => {
            expand_macros_in_combinator(combinator, macro_defns);
        }
        CombinatorInner::Option(OptionCombinator(combinator)) => {
            expand_macros_in_combinator(combinator, macro_defns);
        }
        _ => {}
    }
}

/// Substitute all occurrences of `param` in `body` with `arg`
/// - `param` implicitly refers to the `CombinatorInvocation`s with the same name
fn substitute_in_combinator<'ast>(
    body: &mut Combinator<'ast>,
    param: &str,
    arg: CombinatorInner<'ast>,
) {
    if let Some(and_then) = &mut body.and_then {
        substitute_in_combinator(and_then, param, arg.clone());
    }
    substitute_in_combinator_inner(&mut body.inner, param, arg);
}

fn substitute_in_combinator_inner<'ast>(
    body: &mut CombinatorInner<'ast>,
    param: &str,
    arg: CombinatorInner<'ast>,
) {
    match body {
        // base case
        CombinatorInner::Invocation(CombinatorInvocation { func, .. }) => {
            if func == param {
                *body = arg;
            }
        }
        // recursive cases
        CombinatorInner::Struct(StructCombinator { fields, .. }) => {
            for field in fields {
                match field {
                    StructField::Ordinary { combinator, .. }
                    | StructField::Dependent { combinator, .. } => {
                        substitute_in_combinator(combinator, param, arg.clone());
                    }
                    StructField::Const { .. } => {
                        // TODO: skip const fields for now
                    }
                    _ => {}
                }
            }
        }
        CombinatorInner::Wrap(WrapCombinator {
            prior,
            combinator,
            post,
            ..
        }) => {
            for _combinator in prior {
                // TODO: skip const fields for now
            }
            substitute_in_combinator(combinator, param, arg.clone());
            for _combinator in post {
                // TODO: skip const fields for now
            }
        }
        CombinatorInner::Choice(ChoiceCombinator { choices, .. }) => match choices {
            Choices::Enums(enums) => {
                for (_, combinator) in enums {
                    substitute_in_combinator(combinator, param, arg.clone());
                }
            }
            Choices::Ints(ints) => {
                for (_, combinator) in ints {
                    substitute_in_combinator(combinator, param, arg.clone());
                }
            }
            Choices::Arrays(arrays) => {
                for (_, combinator) in arrays {
                    substitute_in_combinator(combinator, param, arg.clone());
                }
            }
        },
        CombinatorInner::Vec(combinator) => match combinator {
            VecCombinator::Vec(combinator) | VecCombinator::Vec1(combinator) => {
                substitute_in_combinator(combinator, param, arg.clone());
            }
        },
        CombinatorInner::Array(ArrayCombinator { combinator, .. }) => {
            substitute_in_combinator(combinator, param, arg.clone());
        }
        CombinatorInner::Option(OptionCombinator(combinator)) => {
            substitute_in_combinator(combinator, param, arg.clone());
        }
        _ => {}
    }
}

fn expand_definitions(ast: &mut Vec<Definition>) {
    let mut expanded = Vec::new();
    let mut elab_ctx = ElabCtx::new();
    for defn in ast.iter_mut() {
        elab_ctx.reset();
        match defn {
            Definition::Combinator {
                name,
                combinator,
                param_defns,
                ..
            } => {
                param_defns.iter().for_each(|param_defn| {
                    if let ParamDefn::Dependent {
                        name, combinator, ..
                    } = param_defn
                    {
                        elab_ctx
                            .dependencies
                            .push((name.to_owned(), combinator.clone()));
                    }
                });
                expand_combinator(name, combinator, &mut expanded, &mut elab_ctx);
            }
            Definition::ConstCombinator { .. } => {}
            _ => {}
        }
    }
    ast.extend(expanded);
}

#[allow(clippy::single_match)]
/// for now only expand struct fields containing choices
fn expand_combinator<'ast>(
    name: &str,
    combinator: &mut Combinator<'ast>,
    expanded: &mut Vec<Definition<'ast>>,
    elab_ctx: &mut ElabCtx<'ast>,
) {
    match &mut combinator.inner {
        CombinatorInner::Struct(StructCombinator { fields, .. }) => {
            for field in fields {
                match field {
                    StructField::Ordinary {
                        label,
                        combinator,
                        span,
                    } => {
                        if matches!(&combinator.inner, CombinatorInner::Choice(_))
                            || (matches!(
                                &combinator.inner,
                                CombinatorInner::Bytes(_) | CombinatorInner::Tail(_)
                            ) && combinator.and_then.is_some()
                                && matches!(
                                    &combinator.and_then.as_ref().unwrap().inner,
                                    CombinatorInner::Choice(_)
                                ))
                        {
                            let params: HashSet<Param> = collect_params(combinator);
                            let param_defns: Vec<ParamDefn> = params
                                .iter()
                                .map(|param| match param {
                                    Param::Dependent(name) => ParamDefn::Dependent {
                                        name: name.to_owned(),
                                        combinator: elab_ctx
                                            .dependencies
                                            .iter()
                                            .find_map(|(dep_name, dep_combinator)| {
                                                if dep_name == name {
                                                    Some(dep_combinator.clone())
                                                } else {
                                                    None
                                                }
                                            })
                                            .unwrap_or_else(|| {
                                                panic!("Dependent combinator not found: {}", name)
                                            }),
                                        span: *span,
                                    },
                                    _ => unreachable!(),
                                })
                                .collect();
                            let generated_name = name.to_owned() + "_" + label;
                            let new_defn = Definition::Combinator {
                                name: generated_name.clone(),
                                combinator: combinator.clone(),
                                param_defns,
                                span: span.clone(),
                            };
                            *combinator = Combinator {
                                inner: CombinatorInner::Invocation(CombinatorInvocation {
                                    func: generated_name,
                                    args: params.into_iter().collect(),
                                    span: *span,
                                }),
                                and_then: None,
                                span: *span,
                            };
                            expanded.push(new_defn);
                            // expand_definitions(expanded);
                        }
                    }
                    StructField::Dependent {
                        label, combinator, ..
                    } => {
                        elab_ctx
                            .dependencies
                            .push((label.to_owned(), combinator.inner.clone()));
                        // TODO: do we care `and_then` here?
                        // NOTE: don't expand dependent fields for now
                    }
                    StructField::Const { .. } => {}
                    _ => {}
                }
            }
        }
        // CombinatorInner::Choice(ChoiceCombinator { depend_id, choices }) =>
        // CombinatorInner::Bytes(BytesCombinator { len }) =>
        // CombinatorInner::Tail(TailCombinator) =>
        // CombinatorInner::ConstraintInt(..) => {}
        // CombinatorInner::Wrap(..) => {}
        // CombinatorInner::Enum(..) => {}
        // CombinatorInner::SepBy(SepByCombinator { combinator, sep }) =>
        // CombinatorInner::Vec(VecCombinator::Vec(combinator)) =>
        // CombinatorInner::Vec(VecCombinator::Vec1(combinator)) =>
        // CombinatorInner::Array(ArrayCombinator { combinator, len }) =>
        // CombinatorInner::Apply(ApplyCombinator { stream, combinator }) =>
        // CombinatorInner::Option(OptionCombinator(combinator)) =>
        // CombinatorInner::Invocation(CombinatorInvocation { func, args }) =>
        _ => {}
    }
}

fn collect_params(combinator: &Combinator) -> HashSet<Param> {
    let mut params = HashSet::new();
    match &combinator.inner {
        CombinatorInner::Choice(ChoiceCombinator {
            depend_id, choices, ..
        }) => {
            if let Some(depend_id) = depend_id {
                params.insert(Param::Dependent(depend_id.to_owned()));
            }
            match choices {
                Choices::Enums(enums) => {
                    for (_, combinator) in enums {
                        params.extend(collect_params(combinator));
                    }
                }
                Choices::Ints(ints) => {
                    for (_, combinator) in ints {
                        params.extend(collect_params(combinator));
                    }
                }
                Choices::Arrays(arrays) => {
                    for (_, combinator) in arrays {
                        params.extend(collect_params(combinator));
                    }
                }
            }
        }
        CombinatorInner::Array(ArrayCombinator {
            combinator, len, ..
        }) => {
            if let LengthSpecifier::Dependent(name) = len {
                params.insert(Param::Dependent(name.to_owned()));
            }
            params.extend(collect_params(combinator));
        }
        CombinatorInner::Bytes(BytesCombinator { len, .. }) => {
            if let LengthSpecifier::Dependent(name) = len {
                params.insert(Param::Dependent(name.to_owned()));
            }
            if let Some(and_then) = &combinator.and_then {
                params.extend(collect_params(and_then));
            }
        }
        CombinatorInner::Tail(..) => {
            if let Some(and_then) = &combinator.and_then {
                params.extend(collect_params(and_then));
            }
        }
        CombinatorInner::Invocation(CombinatorInvocation { args, .. }) => {
            for arg in args {
                if let Param::Dependent(name) = arg {
                    params.insert(Param::Dependent(name.to_owned()));
                }
            }
        }
        CombinatorInner::Vec(VecCombinator::Vec1(combinator) | VecCombinator::Vec(combinator)) => {
            params.extend(collect_params(combinator));
        }
        CombinatorInner::SepBy(SepByCombinator {
            combinator: VecCombinator::Vec(combinator) | VecCombinator::Vec1(combinator),
            ..
        }) => {
            params.extend(collect_params(combinator));
        }
        CombinatorInner::Wrap(WrapCombinator { combinator, .. }) => {
            params.extend(collect_params(combinator));
        }
        CombinatorInner::Struct(StructCombinator { fields, .. }) => {
            for field in fields {
                match field {
                    StructField::Ordinary { combinator, .. }
                    | StructField::Dependent { combinator, .. } => {
                        params.extend(collect_params(combinator));
                    }
                    _ => {}
                }
            }
        }
        CombinatorInner::Option(OptionCombinator(combinator)) => {
            params.extend(collect_params(combinator));
        }
        CombinatorInner::Enum(..)
        | CombinatorInner::ConstraintInt(..)
        | CombinatorInner::Apply(..) => {}

        CombinatorInner::MacroInvocation { .. } => {
            unreachable!("macro invocation should be resolved by now")
        }
    }
    params
}

pub fn build_call_graph(ast: &[Definition]) -> HashMap<String, Vec<String>> {
    ast.iter()
        .filter_map(|defn| match defn {
            Definition::Combinator {
                name, combinator, ..
            } => {
                let mut invocations = Vec::new();
                collect_invocations(combinator, &mut invocations);
                Some((name.to_owned(), invocations))
            }
            Definition::ConstCombinator {
                name,
                const_combinator,
                ..
            } => {
                let invocations = collect_const_invocations(const_combinator);
                Some((name.to_owned(), invocations))
            }
            _ => None,
        })
        .collect()
}

fn collect_invocations(combinator: &Combinator, invocations: &mut Vec<String>) {
    if let Some(and_then) = &combinator.and_then {
        collect_invocations(and_then, invocations);
    }
    collect_invocations_inner(&combinator.inner, invocations);
}

fn collect_invocations_inner(combinator_inner: &CombinatorInner, invocations: &mut Vec<String>) {
    match combinator_inner {
        // base case: combinator invocation
        CombinatorInner::Invocation(CombinatorInvocation { func, .. }) => {
            invocations.push(func.to_owned());
        }
        // recursive cases
        CombinatorInner::Struct(StructCombinator { fields, .. }) => {
            for field in fields {
                match field {
                    StructField::Ordinary { combinator, .. }
                    | StructField::Dependent { combinator, .. } => {
                        collect_invocations(combinator, invocations);
                    }
                    StructField::Const { .. } => {}
                    _ => {}
                }
            }
        }
        CombinatorInner::Wrap(WrapCombinator { combinator, .. }) => {
            collect_invocations(combinator, invocations);
        }
        CombinatorInner::Choice(ChoiceCombinator { choices, .. }) => match choices {
            Choices::Enums(enums) => {
                for (_, combinator) in enums {
                    collect_invocations(combinator, invocations);
                }
            }
            Choices::Ints(ints) => {
                for (_, combinator) in ints {
                    collect_invocations(combinator, invocations);
                }
            }
            Choices::Arrays(arrays) => {
                for (_, combinator) in arrays {
                    collect_invocations(combinator, invocations);
                }
            }
        },
        CombinatorInner::Vec(VecCombinator::Vec(combinator) | VecCombinator::Vec1(combinator)) => {
            collect_invocations(combinator, invocations);
        }
        CombinatorInner::Array(ArrayCombinator { combinator, .. }) => {
            collect_invocations(combinator, invocations);
        }
        CombinatorInner::Option(OptionCombinator(combinator)) => {
            collect_invocations(combinator, invocations);
        }
        CombinatorInner::Enum(..) => {}
        CombinatorInner::ConstraintInt(..) => {}
        CombinatorInner::Bytes(..) => {}
        CombinatorInner::Tail(..) => {}
        CombinatorInner::Apply(..) => {}
        CombinatorInner::SepBy(..) => {}
        CombinatorInner::MacroInvocation { .. } => {}
    }
}

fn collect_const_invocations(const_combinator: &ConstCombinator) -> Vec<String> {
    let mut invocations = Vec::new();
    match const_combinator {
        ConstCombinator::ConstStruct(ConstStructCombinator(fields)) => {
            for field in fields {
                if let ConstCombinator::ConstCombinatorInvocation(invocation) = field {
                    invocations.push(invocation.to_owned());
                }
            }
        }
        ConstCombinator::ConstChoice(ConstChoiceCombinator(choices)) => {
            for ConstChoice { combinator, .. } in choices {
                if let ConstCombinator::ConstCombinatorInvocation(invocation) = combinator {
                    invocations.push(invocation.to_owned());
                }
            }
        }
        ConstCombinator::ConstCombinatorInvocation(invocation) => {
            invocations.push(invocation.to_owned());
        }
        ConstCombinator::Vec(combinator) => {
            if let ConstCombinator::ConstCombinatorInvocation(invocation) = combinator.as_ref() {
                invocations.push(invocation.to_owned());
            }
        }
        _ => {}
    }
    invocations
}
