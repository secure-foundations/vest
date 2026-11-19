use std::collections::{HashMap, HashSet};

use crate::ast::*;

pub fn elaborate(ast: &mut Vec<Definition>) -> BuildResult<HashSet<String>> {
    expand_macros(ast)?;
    // Keep source order, appending any named helpers for anonymous formats.
    expand_definitions(ast)
}

#[derive(Default)]
struct ElabCtx<'ast> {
    dependencies: Vec<(String, CombinatorInner<'ast>)>,
}

type MacroDefn<'ast> = (Vec<String>, Combinator<'ast>);

fn expand_macros(ast: &mut Vec<Definition>) -> BuildResult<()> {
    let mut macros = HashMap::new();
    for def in ast.iter() {
        if let Definition::MacroDefn { name, params, body } = def {
            if params.iter().collect::<HashSet<_>>().len() != params.len() {
                return Err(invalid_token(name.span, "duplicate macro parameter"));
            }
            if macros
                .insert(name.name.clone(), (params.clone(), body.clone()))
                .is_some()
            {
                return Err(invalid_token(name.span, "duplicate macro definition"));
            }
        }
    }
    ast.retain(|def| !matches!(def, Definition::MacroDefn { .. }));
    let mut expander = MacroExpander {
        macros,
        active: vec![],
    };
    for def in ast {
        if let Definition::Combinator {
            combinator,
            param_defns,
            ..
        } = def
        {
            for ParamDefn::Dependent { combinator, .. } in param_defns {
                expander.expand_inner(combinator)?;
            }
            expander.expand(combinator)?;
        }
    }
    Ok(())
}

/// The two macro passes share this traversal so that adding a child-
/// bearing AST node cannot make substitution and expansion disagree.
fn visit_children<'i>(
    inner: &mut CombinatorInner<'i>,
    mut visit: impl FnMut(&mut Combinator<'i>) -> BuildResult<()>,
) -> BuildResult<()> {
    match inner {
        CombinatorInner::Struct(s) => {
            for field in &mut s.fields {
                if let StructField::Ordinary { combinator, .. }
                | StructField::Dependent { combinator, .. } = field
                {
                    visit(combinator)?;
                }
            }
        }
        CombinatorInner::Choice(c) => match &mut c.choices {
            Choices::Enums(branches) => {
                for (_, body) in branches {
                    visit(body)?;
                }
            }
            Choices::Ints(branches) => {
                for (_, body) in branches {
                    visit(body)?;
                }
            }
            Choices::Arrays(branches) => {
                for (_, body) in branches {
                    visit(body)?;
                }
            }
        },
        CombinatorInner::Wrap(WrapCombinator { combinator, .. })
        | CombinatorInner::Vec(VecCombinator::Vec(combinator))
        | CombinatorInner::Array(ArrayCombinator { combinator, .. })
        | CombinatorInner::Option(OptionCombinator(combinator)) => visit(combinator)?,
        CombinatorInner::Bits(_)
        | CombinatorInner::ConstraintInt(_)
        | CombinatorInner::ConstraintEnum(_)
        | CombinatorInner::Enum(_)
        | CombinatorInner::Bytes(_)
        | CombinatorInner::Tail(_)
        | CombinatorInner::Nothing(_)
        | CombinatorInner::Never(_)
        | CombinatorInner::Invocation(_)
        | CombinatorInner::MacroInvocation { .. } => {}
    }
    Ok(())
}

struct MacroExpander<'i> {
    macros: HashMap<String, MacroDefn<'i>>,
    active: Vec<String>,
}

impl<'i> MacroExpander<'i> {
    fn expand(&mut self, comb: &mut Combinator<'i>) -> BuildResult<()> {
        if let Some(next) = &mut comb.and_then {
            self.expand(next)?;
        }
        if let Some(mut expanded) = self.invocation(&mut comb.inner)? {
            let mut end = &mut expanded.and_then;
            while let Some(next) = end {
                end = &mut next.and_then;
            }
            *end = comb.and_then.take();
            comb.inner = expanded.inner;
            comb.and_then = expanded.and_then;
        } else {
            visit_children(&mut comb.inner, |child| self.expand(child))?;
        }
        Ok(())
    }

    fn expand_inner(&mut self, inner: &mut CombinatorInner<'i>) -> BuildResult<()> {
        if let Some(expanded) = self.invocation(inner)? {
            if expanded.and_then.is_some() {
                return Err(invalid_token(
                    inner.as_span(),
                    "a macro expanding to a >>= chain is not supported in this position",
                ));
            }
            *inner = expanded.inner;
        } else {
            visit_children(inner, |child| self.expand(child))?;
        }
        Ok(())
    }

    fn invocation(
        &mut self,
        inner: &mut CombinatorInner<'i>,
    ) -> BuildResult<Option<Combinator<'i>>> {
        let CombinatorInner::MacroInvocation { name, args, span } = inner else {
            return Ok(None);
        };
        let Some((params, mut body)) = self.macros.get(name).cloned() else {
            return Err(invalid_token(*span, format!("undefined macro `{name}!`")));
        };
        if params.len() != args.len() {
            return Err(invalid_token(
                *span,
                format!(
                    "macro `{name}!` expects {} arguments, got {}",
                    params.len(),
                    args.len(),
                ),
            ));
        }
        for arg in args.iter_mut() {
            self.expand_inner(arg)?;
        }
        if self.active.contains(name) {
            return Err(invalid_token(
                *span,
                format!("recursive expansion of macro `{name}!`"),
            ));
        }
        let replacements = params
            .iter()
            .zip(args.iter())
            .map(|(p, a)| (p.as_str(), a))
            .collect();
        substitute(&mut body, &replacements)?;
        self.active.push(name.clone());
        let result = self.expand(&mut body);
        self.active.pop();
        result.map(|()| Some(body))
    }
}

fn substitute<'i>(
    comb: &mut Combinator<'i>,
    replacements: &HashMap<&str, &CombinatorInner<'i>>,
) -> BuildResult<()> {
    substitute_inner(&mut comb.inner, replacements)?;
    if let Some(next) = &mut comb.and_then {
        substitute(next, replacements)?;
    }
    Ok(())
}

fn substitute_inner<'i>(
    inner: &mut CombinatorInner<'i>,
    replacements: &HashMap<&str, &CombinatorInner<'i>>,
) -> BuildResult<()> {
    match inner {
        CombinatorInner::Invocation(inv) => {
            if let Some(replacement) = replacements.get(inv.func.name.as_str()) {
                if !inv.args.is_empty() {
                    return Err(invalid_token(
                        inv.span,
                        "macro parameters do not take arguments",
                    ));
                }
                *inner = (*replacement).clone();
            }
        }
        CombinatorInner::MacroInvocation { args, .. } => {
            for arg in args {
                substitute_inner(arg, replacements)?;
            }
        }
        _ => visit_children(inner, |child| substitute(child, replacements))?,
    }
    Ok(())
}

fn expand_definitions(ast: &mut Vec<Definition>) -> BuildResult<HashSet<String>> {
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
    let mut elab_ctx = ElabCtx::default();
    for defn in ast.iter_mut() {
        elab_ctx.dependencies.clear();
        match defn {
            Definition::Combinator {
                name,
                combinator,
                param_defns,
                ..
            } => {
                for param_defn in param_defns {
                    let ParamDefn::Dependent {
                        name: param,
                        combinator,
                        ..
                    } = param_defn;
                    let mut parameter_format = Combinator {
                        inner: combinator.clone(),
                        and_then: None,
                        span: combinator.as_span(),
                    };
                    expand_child_combinator(
                        &child_generated_name(
                            &name.name,
                            &format!("param_{}", generated_segment(&param.name)),
                        ),
                        &mut parameter_format,
                        &mut expanded,
                        &mut elab_ctx,
                        &mut used_names,
                    )?;
                    *combinator = parameter_format.inner;
                    elab_ctx
                        .dependencies
                        .push((param.name.to_owned(), combinator.clone()));
                }
                expand_combinator(
                    name.name.as_str(),
                    combinator,
                    &mut expanded,
                    &mut elab_ctx,
                    &mut used_names,
                )?;
            }
            Definition::ConstCombinator { .. } => {}
            _ => {}
        }
    }
    let lifted = expanded
        .iter()
        .filter_map(|defn| match defn {
            Definition::Combinator { name, .. } => Some(name.name.clone()),
            _ => None,
        })
        .collect();
    ast.extend(expanded);
    Ok(lifted)
}

fn expand_combinator<'ast>(
    name: &str,
    combinator: &mut Combinator<'ast>,
    expanded: &mut Vec<Definition<'ast>>,
    elab_ctx: &mut ElabCtx<'ast>,
    used_names: &mut HashSet<String>,
) -> BuildResult<()> {
    if let Some(and_then) = &mut combinator.and_then {
        expand_child_combinator(name, and_then, expanded, elab_ctx, used_names)?;
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
                        )?;
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
                        )?;
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
                    )?;
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
                    )?;
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
                    )?;
                }
            }
        },
        CombinatorInner::Wrap(WrapCombinator { combinator, .. }) => {
            expand_child_combinator(
                &child_generated_name(name, "anon"),
                combinator,
                expanded,
                elab_ctx,
                used_names,
            )?;
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
            )?;
        }
        CombinatorInner::Bits(_) => {}
        _ => {}
    }
    Ok(())
}

fn expand_child_combinator<'ast>(
    generated_base: &str,
    combinator: &mut Combinator<'ast>,
    expanded: &mut Vec<Definition<'ast>>,
    elab_ctx: &mut ElabCtx<'ast>,
    used_names: &mut HashSet<String>,
) -> BuildResult<()> {
    if contains_anonymous_format(combinator) {
        *combinator =
            lift_anonymous_combinator(generated_base, combinator, expanded, elab_ctx, used_names)?;
    } else {
        expand_combinator(generated_base, combinator, expanded, elab_ctx, used_names)?;
    }
    Ok(())
}

fn lift_anonymous_combinator<'ast>(
    generated_base: &str,
    combinator: &Combinator<'ast>,
    expanded: &mut Vec<Definition<'ast>>,
    elab_ctx: &ElabCtx<'ast>,
    used_names: &mut HashSet<String>,
) -> BuildResult<Combinator<'ast>> {
    let generated_name = fresh_generated_name(generated_base, used_names);
    let mut lifted = combinator.clone();
    let mut lifted_ctx = ElabCtx {
        dependencies: elab_ctx.dependencies.clone(),
    };
    let params = sorted_params(&lifted);
    let param_defns = build_param_defns(&params, &lifted_ctx.dependencies, lifted.span)?;

    expand_combinator(
        generated_name.as_str(),
        &mut lifted,
        expanded,
        &mut lifted_ctx,
        used_names,
    )?;

    expanded.push(Definition::Combinator {
        name: Identifier {
            name: generated_name.clone(),
            span: combinator.span,
        },
        param_defns,
        combinator: lifted,
        span: combinator.span,
    });

    Ok(Combinator {
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
    })
}

fn build_param_defns<'ast>(
    params: &[Param<'ast>],
    dependencies: &[(String, CombinatorInner<'ast>)],
    span: Span<'ast>,
) -> BuildResult<Vec<ParamDefn<'ast>>> {
    params
        .iter()
        .map(|param| match param {
            Param::Dependent(name) => Ok(ParamDefn::Dependent {
                name: name.to_owned(),
                combinator: dependencies
                    .iter()
                    .rev()
                    .find_map(|(dep_name, dep_combinator)| {
                        if *dep_name == name.name {
                            Some(dep_combinator.clone())
                        } else {
                            None
                        }
                    })
                    .ok_or_else(|| invalid_token(name.span, format!("unbound field `@{name}`")))?,
                span,
            }),
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
    match &combinator.inner {
        CombinatorInner::Struct(..)
        | CombinatorInner::Choice(..)
        | CombinatorInner::Enum(..)
        | CombinatorInner::Bits(..) => true,
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
    format!("{parent}_{segment}")
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
                let root_name = depend_id.name.split('.').next().unwrap().to_string();
                if !bound.contains(&root_name) {
                    let mut root_ident = depend_id.to_owned();
                    root_ident.name = root_name;
                    params.insert(Param::Dependent(root_ident));
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
                let root_name = name.name.split('.').next().unwrap().to_string();
                if !bound.contains(&root_name) {
                    let mut root_ident = name.to_owned();
                    root_ident.name = root_name;
                    params.insert(Param::Dependent(root_ident));
                }
            }
        }
        CombinatorInner::Vec(VecCombinator::Vec(combinator)) => {
            params.extend(collect_params_with_bound(combinator, bound));
        }
        CombinatorInner::Wrap(WrapCombinator { combinator, .. }) => {
            params.extend(collect_params_with_bound(combinator, bound));
        }
        CombinatorInner::Bits(..) => {}
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
        | CombinatorInner::ConstraintEnum(..)
        | CombinatorInner::Nothing(..)
        | CombinatorInner::Never(..) => {}

        CombinatorInner::MacroInvocation { .. } => {
            unreachable!("macro invocation should be resolved by now")
        }
    }
    params
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::from_str;

    #[test]
    fn test_lift_anonymous_bind() {
        let source = r#"
        capture_outer_and_local = {
            @frame_len: u8 | { 1.. },
            payload: [u8; @frame_len] >>= {
                @tag: u8,
                body: choose(@tag) {
                    0 => [u8; @frame_len - |u8|],
                    _ => {
                        @count: u8,
                        items: [u8; @count],
                    },
                },
            },
        }
        "#;

        let mut ast = from_str(source).unwrap();
        expand_definitions(&mut ast).unwrap();
        println!("Elaborated AST:");
        for defn in &ast {
            println!("{}", defn);
        }

        // We expect:
        // Helper1 (for the choose `_` branch)
        // Helper2 (for the `choose` body)
        // Helper3 (for the `and_then` struct body)
        // capture_outer_and_local (the original combinator)
        assert_eq!(ast.len(), 4);
    }
}
