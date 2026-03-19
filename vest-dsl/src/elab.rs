use std::collections::{HashMap, HashSet};

use crate::{ast::*, utils::topological_sort, utils::VestHasherBuilder};

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
                            Definition::Combinator { name, .. } => name.name == *name_,
                            Definition::ConstCombinator { name, .. } => name.name == *name_,
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
    let mut macro_defns = HashMap::with_hasher(VestHasherBuilder);
    for defn in ast.iter() {
        if let Definition::MacroDefn { name, params, body } = defn {
            macro_defns.insert(name.name.clone(), (params.clone(), body.clone()));
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
    macro_defns: &HashMap<String, MacroDefn<'ast>, VestHasherBuilder>,
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
    macro_defns: &HashMap<String, MacroDefn<'ast>, VestHasherBuilder>,
) {
    if let Some(and_then) = &mut combinator.and_then {
        expand_macros_in_combinator(and_then, macro_defns);
    }
    expand_macros_in_combinator_inner(&mut combinator.inner, macro_defns);
}

fn expand_macros_in_combinator_inner<'ast>(
    combinator_inner: &mut CombinatorInner<'ast>,
    macro_defns: &HashMap<String, MacroDefn<'ast>, VestHasherBuilder>,
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
                    StructField::Const { .. } => {}
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
        CombinatorInner::Vec(VecCombinator::Vec(combinator)) => {
            expand_macros_in_combinator(combinator, macro_defns);
        }
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
            if func.name == param {
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
                    StructField::Const { .. } => {}
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
        CombinatorInner::Vec(VecCombinator::Vec(combinator)) => {
            substitute_in_combinator(combinator, param, arg.clone());
        }
        CombinatorInner::Array(ArrayCombinator { combinator, .. }) => {
            substitute_in_combinator(combinator, param, arg.clone());
        }
        CombinatorInner::Option(OptionCombinator(combinator)) => {
            substitute_in_combinator(combinator, param, arg.clone());
        }
        CombinatorInner::ConstraintEnum(..) => {}
        _ => {}
    }
}

fn expand_definitions(ast: &mut Vec<Definition>) {
    let mut expanded = Vec::new();
    let mut used_names: HashSet<String> = ast
        .iter()
        .filter_map(|defn| match defn {
            Definition::Combinator { name, .. } | Definition::ConstCombinator { name, .. } => {
                Some(name.name.clone())
            }
            _ => None,
        })
        .collect();
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
                    let ParamDefn::Dependent {
                        name, combinator, ..
                    } = param_defn;
                    elab_ctx
                        .dependencies
                        .push((name.name.to_owned(), combinator.clone()));
                });
                expand_combinator(
                    name.name.as_str(),
                    combinator,
                    &mut expanded,
                    &mut elab_ctx,
                    &mut used_names,
                );
            }
            Definition::ConstCombinator { .. } => {}
            _ => {}
        }
    }
    ast.extend(expanded);
}

fn expand_combinator<'ast>(
    name: &str,
    combinator: &mut Combinator<'ast>,
    expanded: &mut Vec<Definition<'ast>>,
    elab_ctx: &mut ElabCtx<'ast>,
    used_names: &mut HashSet<String>,
) {
    if let Some(and_then) = &mut combinator.and_then {
        expand_child_combinator(
            &child_generated_name(name, "inner"),
            and_then,
            expanded,
            elab_ctx,
            used_names,
        );
    }

    match &mut combinator.inner {
        CombinatorInner::Struct(StructCombinator { fields, .. }) => {
            for field in fields {
                match field {
                    StructField::Ordinary {
                        label, combinator, ..
                    } => {
                        expand_child_combinator(
                            &child_generated_name(name, &generated_segment(&label.name)),
                            combinator,
                            expanded,
                            elab_ctx,
                            used_names,
                        );
                    }
                    StructField::Dependent {
                        label, combinator, ..
                    } => {
                        expand_child_combinator(
                            &child_generated_name(name, &generated_segment(&label.name)),
                            combinator,
                            expanded,
                            elab_ctx,
                            used_names,
                        );
                        elab_ctx
                            .dependencies
                            .push((label.name.to_owned(), combinator.inner.clone()));
                    }
                    StructField::Const { .. } => {}
                }
            }
        }
        CombinatorInner::Choice(ChoiceCombinator { choices, .. }) => match choices {
            Choices::Enums(enums) => {
                for (variant, combinator) in enums {
                    expand_child_combinator(
                        &child_generated_name(name, &generated_segment(&variant.name)),
                        combinator,
                        expanded,
                        elab_ctx,
                        used_names,
                    );
                }
            }
            Choices::Ints(ints) => {
                for (idx, (_, combinator)) in ints.iter_mut().enumerate() {
                    expand_child_combinator(
                        &child_generated_name(name, &format!("choice{idx}")),
                        combinator,
                        expanded,
                        elab_ctx,
                        used_names,
                    );
                }
            }
            Choices::Arrays(arrays) => {
                for (idx, (_, combinator)) in arrays.iter_mut().enumerate() {
                    expand_child_combinator(
                        &child_generated_name(name, &format!("choice{idx}")),
                        combinator,
                        expanded,
                        elab_ctx,
                        used_names,
                    );
                }
            }
        },
        CombinatorInner::Wrap(WrapCombinator { combinator, .. }) => {
            expand_child_combinator(
                &child_generated_name(name, "inner"),
                combinator,
                expanded,
                elab_ctx,
                used_names,
            );
        }
        CombinatorInner::Vec(VecCombinator::Vec(combinator))
        | CombinatorInner::Array(ArrayCombinator { combinator, .. })
        | CombinatorInner::Option(OptionCombinator(combinator)) => {
            expand_child_combinator(
                &child_generated_name(name, "item"),
                combinator,
                expanded,
                elab_ctx,
                used_names,
            );
        }
        _ => {}
    }
}

fn expand_child_combinator<'ast>(
    generated_base: &str,
    combinator: &mut Combinator<'ast>,
    expanded: &mut Vec<Definition<'ast>>,
    elab_ctx: &mut ElabCtx<'ast>,
    used_names: &mut HashSet<String>,
) {
    if contains_anonymous_format(combinator) {
        *combinator =
            lift_anonymous_combinator(generated_base, combinator, expanded, elab_ctx, used_names);
    } else {
        expand_combinator(generated_base, combinator, expanded, elab_ctx, used_names);
    }
}

fn lift_anonymous_combinator<'ast>(
    generated_base: &str,
    combinator: &Combinator<'ast>,
    expanded: &mut Vec<Definition<'ast>>,
    elab_ctx: &ElabCtx<'ast>,
    used_names: &mut HashSet<String>,
) -> Combinator<'ast> {
    let generated_name = fresh_generated_name(generated_base, used_names);
    let mut lifted = combinator.clone();
    let mut lifted_ctx = ElabCtx {
        dependencies: elab_ctx.dependencies.clone(),
    };
    let params = sorted_params(&lifted);
    let param_defns = build_param_defns(&params, &lifted_ctx.dependencies, lifted.span);

    expand_combinator(
        generated_name.as_str(),
        &mut lifted,
        expanded,
        &mut lifted_ctx,
        used_names,
    );

    expanded.push(Definition::Combinator {
        name: Identifier {
            name: generated_name.clone(),
            span: combinator.span,
        },
        param_defns,
        combinator: lifted,
        span: combinator.span,
    });

    Combinator {
        inner: CombinatorInner::Invocation(CombinatorInvocation {
            func: Identifier {
                name: generated_name,
                span: combinator.span,
            },
            args: params,
            span: combinator.span,
        }),
        and_then: None,
        span: combinator.span,
    }
}

fn build_param_defns<'ast>(
    params: &[Param<'ast>],
    dependencies: &[(String, CombinatorInner<'ast>)],
    span: Span<'ast>,
) -> Vec<ParamDefn<'ast>> {
    params
        .iter()
        .map(|param| match param {
            Param::Dependent(name) => ParamDefn::Dependent {
                name: name.to_owned(),
                combinator: dependencies
                    .iter()
                    .find_map(|(dep_name, dep_combinator)| {
                        if *dep_name == name.name {
                            Some(dep_combinator.clone())
                        } else {
                            None
                        }
                    })
                    .unwrap_or_else(|| panic!("Dependent combinator not found: {}", name)),
                span,
            },
        })
        .collect()
}

fn sorted_params<'ast>(combinator: &Combinator<'ast>) -> Vec<Param<'ast>> {
    let mut params: Vec<_> = collect_params(combinator).into_iter().collect();
    params.sort_by(|lhs, rhs| match (lhs, rhs) {
        (Param::Dependent(lhs), Param::Dependent(rhs)) => lhs.name.cmp(&rhs.name),
    });
    params
}

fn contains_anonymous_format(combinator: &Combinator) -> bool {
    if let Some(and_then) = &combinator.and_then {
        if contains_anonymous_format(and_then) {
            return true;
        }
    }

    match &combinator.inner {
        CombinatorInner::Struct(..) | CombinatorInner::Choice(..) => true,
        CombinatorInner::Wrap(WrapCombinator { combinator, .. })
        | CombinatorInner::Vec(VecCombinator::Vec(combinator))
        | CombinatorInner::Array(ArrayCombinator { combinator, .. })
        | CombinatorInner::Option(OptionCombinator(combinator)) => {
            contains_anonymous_format(combinator)
        }
        _ => false,
    }
}

fn generated_segment(segment: &str) -> String {
    let mut generated = String::new();
    for ch in segment.chars() {
        if ch.is_ascii_alphanumeric() {
            generated.push(ch.to_ascii_lowercase());
        } else {
            generated.push('_');
        }
    }
    if generated.is_empty() {
        "anon".to_string()
    } else {
        generated
    }
}

fn child_generated_name(parent: &str, segment: &str) -> String {
    format!("{parent}_anon_{segment}")
}

fn fresh_generated_name(base: &str, used_names: &mut HashSet<String>) -> String {
    if used_names.insert(base.to_string()) {
        return base.to_string();
    }

    let mut idx = 0usize;
    loop {
        let candidate = format!("{base}_{idx}");
        if used_names.insert(candidate.clone()) {
            return candidate;
        }
        idx += 1;
    }
}

fn collect_params<'ast>(combinator: &Combinator<'ast>) -> HashSet<Param<'ast>> {
    collect_params_with_bound(combinator, &HashSet::new())
}

fn collect_params_with_bound<'ast>(
    combinator: &Combinator<'ast>,
    bound: &HashSet<String>,
) -> HashSet<Param<'ast>> {
    let mut params = HashSet::new();
    match &combinator.inner {
        CombinatorInner::Choice(ChoiceCombinator {
            depend_id, choices, ..
        }) => {
            if let Some(depend_id) = depend_id {
                if !bound.contains(&depend_id.name) {
                    params.insert(Param::Dependent(depend_id.to_owned()));
                }
            }
            match choices {
                Choices::Enums(enums) => {
                    for (_, combinator) in enums {
                        params.extend(collect_params_with_bound(combinator, bound));
                    }
                }
                Choices::Ints(ints) => {
                    for (_, combinator) in ints {
                        params.extend(collect_params_with_bound(combinator, bound));
                    }
                }
                Choices::Arrays(arrays) => {
                    for (_, combinator) in arrays {
                        params.extend(collect_params_with_bound(combinator, bound));
                    }
                }
            }
        }
        CombinatorInner::Array(ArrayCombinator {
            combinator, len, ..
        }) => {
            for dep_id in len.collect_dependent_ids() {
                let ident = dep_id.to_identifier();
                if !bound.contains(&ident.name) {
                    params.insert(Param::Dependent(ident));
                }
            }
            params.extend(collect_params_with_bound(combinator, bound));
        }
        CombinatorInner::Bytes(BytesCombinator { len, .. }) => {
            for dep_id in len.collect_dependent_ids() {
                let ident = dep_id.to_identifier();
                if !bound.contains(&ident.name) {
                    params.insert(Param::Dependent(ident));
                }
            }
            if let Some(and_then) = &combinator.and_then {
                params.extend(collect_params_with_bound(and_then, bound));
            }
        }
        CombinatorInner::Tail(..) => {
            if let Some(and_then) = &combinator.and_then {
                params.extend(collect_params_with_bound(and_then, bound));
            }
        }
        CombinatorInner::Invocation(CombinatorInvocation { args, .. }) => {
            for arg in args {
                let Param::Dependent(name) = arg;
                if !bound.contains(&name.name) {
                    params.insert(Param::Dependent(name.to_owned()));
                }
            }
        }
        CombinatorInner::Vec(VecCombinator::Vec(combinator)) => {
            params.extend(collect_params_with_bound(combinator, bound));
        }
        CombinatorInner::Wrap(WrapCombinator { combinator, .. }) => {
            params.extend(collect_params_with_bound(combinator, bound));
        }
        CombinatorInner::Struct(StructCombinator { fields, .. }) => {
            let mut locally_bound = bound.clone();
            for field in fields {
                match field {
                    StructField::Ordinary { combinator, .. }
                    | StructField::Dependent { combinator, .. } => {
                        params.extend(collect_params_with_bound(combinator, &locally_bound));
                    }
                    StructField::Const { .. } => {}
                }
                if let StructField::Dependent { label, .. } = field {
                    locally_bound.insert(label.name.clone());
                }
            }
        }
        CombinatorInner::Option(OptionCombinator(combinator)) => {
            params.extend(collect_params_with_bound(combinator, bound));
        }
        CombinatorInner::Enum(..)
        | CombinatorInner::ConstraintInt(..)
        | CombinatorInner::ConstraintEnum(..) => {}

        CombinatorInner::MacroInvocation { .. } => {
            unreachable!("macro invocation should be resolved by now")
        }
    }
    params
}

pub fn build_call_graph(ast: &[Definition]) -> HashMap<String, Vec<String>, VestHasherBuilder> {
    ast.iter()
        .filter_map(|defn| match defn {
            Definition::Combinator {
                name, combinator, ..
            } => {
                let mut invocations = Vec::new();
                collect_invocations(combinator, &mut invocations);
                Some((name.name.to_owned(), invocations))
            }
            Definition::ConstCombinator {
                name,
                const_combinator,
                ..
            } => {
                let invocations = collect_const_invocations(const_combinator);
                Some((name.name.to_owned(), invocations))
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
            invocations.push(func.name.to_owned());
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
        CombinatorInner::Vec(VecCombinator::Vec(combinator)) => {
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
        CombinatorInner::ConstraintEnum(ConstraintEnumCombinator { combinator, .. }) => {
            invocations.push(combinator.func.name.to_owned());
            for arg in &combinator.args {
                let Param::Dependent(name) = arg;
                let _ = name; // no invocations inside params
            }
        }
        CombinatorInner::Bytes(..) => {}
        CombinatorInner::Tail(..) => {}
        CombinatorInner::MacroInvocation { .. } => {}
    }
}

fn collect_const_invocations(const_combinator: &ConstCombinator) -> Vec<String> {
    match const_combinator {
        ConstCombinator::ConstCombinatorInvocation {
            name: invocation, ..
        } => vec![invocation.name.to_owned()],
        _ => Vec::new(),
    }
}
