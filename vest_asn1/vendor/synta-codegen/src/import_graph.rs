//! Import dependency graph and circular-import detection.
//!
//! Given a set of parsed [`Module`]s, this module builds a directed dependency
//! graph where each edge `A → B` means "module A imports symbols from module B".
//! It then runs a depth-first search to detect back-edges (cycles) and returns
//! each cycle as an [`ImportCycle`].
//!
//! Only edges between modules that are present in the provided slice are
//! considered; imports from modules that were not provided are ignored.

use crate::ast::Module;
use std::collections::{HashMap, HashSet};

/// A circular import chain detected among a set of modules.
///
/// [`modules`][ImportCycle::modules] contains the module names involved in the
/// cycle.  The first and last elements are the same module to make the cycle
/// easy to read, e.g. `["A", "B", "C", "A"]` means A imports from B, B from
/// C, and C back from A.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportCycle {
    /// Module names forming the cycle (first == last to show closure).
    pub modules: Vec<String>,
}

impl ImportCycle {
    /// Return a human-readable representation of the cycle, e.g.
    /// `"A → B → C → A"`.
    pub fn display(&self) -> String {
        self.modules.join(" → ")
    }
}

/// Detect circular imports among a slice of parsed modules.
///
/// Returns one [`ImportCycle`] per distinct cycle found.  The same cycle is
/// never reported more than once regardless of which node the DFS enters it
/// from.  An empty `Vec` means no cycles were detected.
///
/// # Example
///
/// ```
/// use synta_codegen::{parse, import_graph::detect_cycles};
///
/// let a = parse("ModA DEFINITIONS ::= BEGIN IMPORTS Foo FROM ModB; END").unwrap();
/// let b = parse("ModB DEFINITIONS ::= BEGIN IMPORTS Bar FROM ModA; END").unwrap();
///
/// let cycles = detect_cycles(&[a, b]);
/// assert_eq!(cycles.len(), 1);
/// ```
pub fn detect_cycles(modules: &[Module]) -> Vec<ImportCycle> {
    // Set of module names present in the input slice.
    let known: HashSet<&str> = modules.iter().map(|m| m.name.as_str()).collect();

    // Adjacency list: module name → list of module names it imports from
    // (restricted to modules present in the input slice).
    let mut adj: HashMap<&str, Vec<&str>> = HashMap::new();
    for m in modules {
        let deps: Vec<&str> = m
            .imports
            .iter()
            .filter_map(|imp| {
                let n = imp.module_name.as_str();
                if known.contains(n) {
                    Some(n)
                } else {
                    None
                }
            })
            .collect();
        adj.insert(m.name.as_str(), deps);
    }

    let mut globally_visited: HashSet<&str> = HashSet::new();
    let mut path: Vec<&str> = Vec::new();
    let mut path_set: HashSet<&str> = HashSet::new();
    let mut cycles: Vec<ImportCycle> = Vec::new();
    // Canonical forms of already-reported cycles to avoid duplicates.
    let mut seen: HashSet<Vec<String>> = HashSet::new();

    for m in modules {
        let name = m.name.as_str();
        if !globally_visited.contains(name) {
            dfs(
                name,
                &adj,
                &mut globally_visited,
                &mut path,
                &mut path_set,
                &mut cycles,
                &mut seen,
            );
        }
    }

    cycles
}

/// Compute a topological generation order for a set of modules.
///
/// Returns the indices into `modules` in the order they should be generated:
/// a module that is imported by another always appears **before** the module
/// that imports it (leaf/dependency modules first).
///
/// If there are no inter-module edges among the provided modules the original
/// slice order is preserved.  Callers should run [`detect_cycles`] first;
/// any cycle causes the involved modules to be appended in input order after
/// all acyclic modules.
///
/// # Example
///
/// ```
/// use synta_codegen::{parse, import_graph::topological_order};
///
/// // B is a dependency of A.
/// let a = parse("ModA DEFINITIONS ::= BEGIN IMPORTS X FROM ModB; END").unwrap();
/// let b = parse("ModB DEFINITIONS ::= BEGIN END").unwrap();
///
/// let order = topological_order(&[a, b]);
/// // ModB (index 1) must be generated before ModA (index 0).
/// assert_eq!(order, vec![1, 0]);
/// ```
pub fn topological_order(modules: &[Module]) -> Vec<usize> {
    // Map module name → index in the slice.
    let name_to_idx: HashMap<&str, usize> = modules
        .iter()
        .enumerate()
        .map(|(i, m)| (m.name.as_str(), i))
        .collect();

    // in_degree[i] = number of known modules that module i depends on.
    let mut in_degree = vec![0usize; modules.len()];
    // rev_adj[j] = modules that depend on j (they will be unblocked when j is done).
    let mut rev_adj: Vec<Vec<usize>> = vec![Vec::new(); modules.len()];

    for (i, m) in modules.iter().enumerate() {
        for imp in &m.imports {
            if let Some(&j) = name_to_idx.get(imp.module_name.as_str()) {
                // Module i depends on module j.
                in_degree[i] += 1;
                rev_adj[j].push(i);
            }
        }
    }

    // Kahn's BFS: start with all nodes that have no unresolved dependencies.
    let mut queue: std::collections::VecDeque<usize> = in_degree
        .iter()
        .enumerate()
        .filter(|(_, &d)| d == 0)
        .map(|(i, _)| i)
        .collect();

    let mut order = Vec::with_capacity(modules.len());
    while let Some(idx) = queue.pop_front() {
        order.push(idx);
        for &dependent in &rev_adj[idx] {
            in_degree[dependent] -= 1;
            if in_degree[dependent] == 0 {
                queue.push_back(dependent);
            }
        }
    }

    // Append modules involved in cycles (only possible if detect_cycles was not called
    // before this function; callers that do call detect_cycles first will never reach
    // this branch because cyclic modules never reach in_degree == 0 in Kahn's BFS).
    if order.len() < modules.len() {
        let emitted: HashSet<usize> = order.iter().copied().collect();
        for i in 0..modules.len() {
            if !emitted.contains(&i) {
                order.push(i);
            }
        }
    }

    order
}

/// Recursive DFS helper.
///
/// * `globally_visited` — nodes whose entire subtree has been explored (BLACK).
/// * `path` / `path_set` — current DFS path from the root (GRAY).
fn dfs<'a>(
    node: &'a str,
    adj: &HashMap<&'a str, Vec<&'a str>>,
    globally_visited: &mut HashSet<&'a str>,
    path: &mut Vec<&'a str>,
    path_set: &mut HashSet<&'a str>,
    cycles: &mut Vec<ImportCycle>,
    seen: &mut HashSet<Vec<String>>,
) {
    if path_set.contains(node) {
        // Back-edge: node is already on the current path → cycle found.
        let start = path.iter().position(|&n| n == node).unwrap();
        let raw: Vec<&str> = path[start..].to_vec();

        // Normalise: rotate so the lexicographically smallest name is first,
        // then append that name again to close the cycle.
        let min_pos = raw
            .iter()
            .enumerate()
            .min_by_key(|(_, &s)| s)
            .map(|(i, _)| i)
            .unwrap_or(0);
        let mut canonical: Vec<String> = raw[min_pos..]
            .iter()
            .chain(raw[..min_pos].iter())
            .map(|&s| s.to_string())
            .collect();
        canonical.push(canonical[0].clone()); // close the cycle

        if seen.insert(canonical.clone()) {
            cycles.push(ImportCycle { modules: canonical });
        }
        return;
    }

    if globally_visited.contains(node) {
        // Already fully explored — no new cycles reachable from here.
        return;
    }

    // Mark node as currently being explored (GRAY).
    path.push(node);
    path_set.insert(node);

    if let Some(neighbors) = adj.get(node) {
        for &neighbor in neighbors {
            dfs(
                neighbor,
                adj,
                globally_visited,
                path,
                path_set,
                cycles,
                seen,
            );
        }
    }

    // Mark node as fully explored (BLACK).
    path.pop();
    path_set.remove(node);
    globally_visited.insert(node);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;

    fn make_module(name: &str, imports_from: &[&str]) -> Module {
        let import_block = if imports_from.is_empty() {
            String::new()
        } else {
            let clauses: Vec<String> = imports_from
                .iter()
                .map(|m| format!("Dummy FROM {}", m))
                .collect();
            format!("IMPORTS {};", clauses.join(", "))
        };
        let src = format!("{} DEFINITIONS ::= BEGIN {} END", name, import_block);
        parse(&src).unwrap()
    }

    #[test]
    fn test_no_cycles_single_module() {
        let m = make_module("Alpha", &[]);
        assert!(detect_cycles(&[m]).is_empty());
    }

    #[test]
    fn test_no_cycles_linear_chain() {
        // A → B → C (no cycle)
        let a = make_module("Alpha", &["Beta"]);
        let b = make_module("Beta", &["Gamma"]);
        let c = make_module("Gamma", &[]);
        assert!(detect_cycles(&[a, b, c]).is_empty());
    }

    #[test]
    fn test_direct_cycle_two_modules() {
        // A → B → A
        let a = make_module("Alpha", &["Beta"]);
        let b = make_module("Beta", &["Alpha"]);
        let cycles = detect_cycles(&[a, b]);
        assert_eq!(cycles.len(), 1);
        // Normalised: Alpha → Beta → Alpha (Alpha < Beta lexicographically)
        assert_eq!(cycles[0].modules, vec!["Alpha", "Beta", "Alpha"]);
    }

    #[test]
    fn test_three_module_cycle() {
        // A → B → C → A
        let a = make_module("Alpha", &["Beta"]);
        let b = make_module("Beta", &["Gamma"]);
        let c = make_module("Gamma", &["Alpha"]);
        let cycles = detect_cycles(&[a, b, c]);
        assert_eq!(cycles.len(), 1);
        assert_eq!(cycles[0].modules, vec!["Alpha", "Beta", "Gamma", "Alpha"]);
    }

    #[test]
    fn test_unknown_import_ignored() {
        // A imports from Unknown (not in the slice) — not a cycle.
        let a = make_module("Alpha", &["Unknown"]);
        assert!(detect_cycles(&[a]).is_empty());
    }

    #[test]
    fn test_self_import_is_cycle() {
        // A → A
        let a = make_module("Alpha", &["Alpha"]);
        let cycles = detect_cycles(&[a]);
        assert_eq!(cycles.len(), 1);
        assert_eq!(cycles[0].modules, vec!["Alpha", "Alpha"]);
    }

    #[test]
    fn test_display_format() {
        let cycle = ImportCycle {
            modules: vec!["Alpha".to_string(), "Beta".to_string(), "Alpha".to_string()],
        };
        assert_eq!(cycle.display(), "Alpha → Beta → Alpha");
    }

    #[test]
    fn test_cycle_reported_once() {
        // Same two-node cycle entered from different starting points — must
        // appear exactly once in the output.
        let a = make_module("Alpha", &["Beta"]);
        let b = make_module("Beta", &["Alpha"]);
        // Provide them in both orderings.
        let cycles1 = detect_cycles(&[a.clone(), b.clone()]);
        let cycles2 = detect_cycles(&[b.clone(), a.clone()]);
        assert_eq!(cycles1.len(), 1);
        assert_eq!(cycles2.len(), 1);
        assert_eq!(cycles1[0].modules, cycles2[0].modules);
    }

    // ── topological_order tests ───────────────────────────────────────────────

    #[test]
    fn test_topo_single_module() {
        let m = make_module("Alpha", &[]);
        assert_eq!(topological_order(&[m]), vec![0]);
    }

    #[test]
    fn test_topo_linear_chain() {
        // A imports from B, B imports from C → order should be C, B, A.
        let a = make_module("Alpha", &["Beta"]);
        let b = make_module("Beta", &["Gamma"]);
        let c = make_module("Gamma", &[]);
        let order = topological_order(&[a, b, c]);
        // Gamma (2) before Beta (1) before Alpha (0).
        assert_eq!(order, vec![2, 1, 0]);
    }

    #[test]
    fn test_topo_multiple_independent_leaves() {
        // Two independent leaf modules (Beta, Gamma) feed into Alpha;
        // expressed as a chain: Alpha→Beta, Gamma is independent.
        // Ordering must put Beta before Alpha; Gamma can be anywhere.
        let a = make_module("Alpha", &["Beta"]);
        let b = make_module("Beta", &[]);
        let c = make_module("Gamma", &[]);
        let order = topological_order(&[a, b, c]);
        let alpha_pos = order.iter().position(|&i| i == 0).unwrap();
        let beta_pos = order.iter().position(|&i| i == 1).unwrap();
        assert!(beta_pos < alpha_pos, "Beta must be generated before Alpha");
    }

    #[test]
    fn test_topo_no_cross_deps() {
        // Two independent modules — original order is preserved.
        let a = make_module("Alpha", &[]);
        let b = make_module("Beta", &[]);
        let order = topological_order(&[a, b]);
        assert_eq!(order, vec![0, 1]);
    }
}
