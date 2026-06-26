use std::collections::{HashMap, HashSet};
use std::hash::DefaultHasher;
use std::hash::Hash;

#[derive(Default, Clone)]
pub struct VestHasherBuilder;

impl std::hash::BuildHasher for VestHasherBuilder {
    type Hasher = DefaultHasher;

    fn build_hasher(&self) -> Self::Hasher {
        DefaultHasher::new()
    }
}

#[derive(Debug, PartialEq)]
pub enum TopoSortError<E> {
    CycleDetected(E),
}

pub fn topological_sort<K, V>(
    graph: &HashMap<K, V, VestHasherBuilder>,
) -> Result<Vec<K>, TopoSortError<K>>
where
    K: Eq + Hash + Clone,
    V: AsRef<[K]>,
{
    let mut visited = HashSet::with_hasher(VestHasherBuilder);
    let mut visiting = HashSet::with_hasher(VestHasherBuilder);
    let mut sorted = Vec::new();

    for node in graph.keys() {
        if !visited.contains(node) {
            dfs(
                node.clone(),
                graph,
                &mut visited,
                &mut visiting,
                &mut sorted,
            )?;
        }
    }

    Ok(sorted)
}

fn dfs<K, V>(
    node: K,
    graph: &HashMap<K, V, VestHasherBuilder>,
    visited: &mut HashSet<K, VestHasherBuilder>,
    visiting: &mut HashSet<K, VestHasherBuilder>,
    sorted: &mut Vec<K>,
) -> Result<(), TopoSortError<K>>
where
    K: Eq + Hash + Clone,
    V: AsRef<[K]>,
{
    if visiting.contains(&node) {
        return Err(TopoSortError::CycleDetected(node));
    }

    if !visited.contains(&node) {
        visiting.insert(node.clone());

        if let Some(neighbors) = graph.get(&node) {
            for neighbor in neighbors.as_ref() {
                dfs(neighbor.clone(), graph, visited, visiting, sorted)?;
            }
        }

        visiting.remove(&node);
        visited.insert(node.clone());
        sorted.push(node);
    }

    Ok(())
}

/// Compute SCCs via Tarjan's algorithm.
/// Returns SCCs in reverse-topological order (callee SCCs before caller SCCs).
/// Each SCC is a `Vec<String>`; single-node SCCs with no self-edge are non-recursive.
pub fn tarjan_scc(graph: &HashMap<String, Vec<String>>) -> Vec<Vec<String>> {
    struct State {
        index_counter: usize,
        stack: Vec<String>,
        on_stack: HashSet<String>,
        index: HashMap<String, usize>,
        lowlink: HashMap<String, usize>,
        sccs: Vec<Vec<String>>,
    }

    fn strongconnect(v: &str, graph: &HashMap<String, Vec<String>>, s: &mut State) {
        s.index.insert(v.to_string(), s.index_counter);
        s.lowlink.insert(v.to_string(), s.index_counter);
        s.index_counter += 1;
        s.stack.push(v.to_string());
        s.on_stack.insert(v.to_string());

        if let Some(neighbors) = graph.get(v) {
            for w in neighbors {
                if !s.index.contains_key(w.as_str()) {
                    strongconnect(w, graph, s);
                    let ll_w = s.lowlink[w.as_str()];
                    let ll_v = s.lowlink[v];
                    s.lowlink.insert(v.to_string(), ll_v.min(ll_w));
                } else if s.on_stack.contains(w.as_str()) {
                    let idx_w = s.index[w.as_str()];
                    let ll_v = s.lowlink[v];
                    s.lowlink.insert(v.to_string(), ll_v.min(idx_w));
                }
            }
        }

        if s.lowlink[v] == s.index[v] {
            let mut scc = Vec::new();
            loop {
                let w = s.stack.pop().unwrap();
                s.on_stack.remove(&w);
                scc.push(w.clone());
                if w == v {
                    break;
                }
            }
            s.sccs.push(scc);
        }
    }

    let mut state = State {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: HashSet::new(),
        index: HashMap::new(),
        lowlink: HashMap::new(),
        sccs: Vec::new(),
    };

    // Iterate in sorted order for determinism.
    let mut nodes: Vec<&str> = graph.keys().map(|s| s.as_str()).collect();
    nodes.sort_unstable();
    for v in nodes {
        if !state.index.contains_key(v) {
            strongconnect(v, graph, &mut state);
        }
    }

    state.sccs
}

/// Returns true if an SCC is recursive (size > 1, or a singleton with a self-edge).
pub fn scc_is_recursive(scc: &[String], graph: &HashMap<String, Vec<String>>) -> bool {
    if scc.len() > 1 {
        return true;
    }
    let name = &scc[0];
    graph.get(name).map_or(false, |deps| deps.contains(name))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_topological_sort() {
        let mut graph = HashMap::with_hasher(VestHasherBuilder);
        graph.insert("A", vec!["B", "C"]);
        graph.insert("B", vec!["C"]);
        graph.insert("C", vec!["D"]);
        graph.insert("D", vec!["A"]);

        // Cycle exists; the specific node detected depends on traversal order
        assert!(topological_sort(&graph).is_err());
    }

    #[test]
    fn test_topological_sort_2() {
        let mut graph = HashMap::with_hasher(VestHasherBuilder);
        graph.insert("D", vec![]);
        graph.insert("B", vec!["C"]);
        graph.insert("C", vec!["D"]);
        graph.insert("A", vec!["B", "C"]);

        let sorted = topological_sort(&graph).unwrap();

        assert!(matches!(
            sorted.as_slice(),
            ["D", "C", "B", "A"] | ["D", "B", "C", "A"]
        ))
    }

    #[test]
    fn test_topological_sort_3() {
        let mut graph = HashMap::with_hasher(VestHasherBuilder);
        graph.insert("A", vec!["B", "C"]);
        graph.insert("B", vec!["C"]);
        graph.insert("C", vec!["D"]);
        graph.insert("D", vec![]);

        let sorted = topological_sort(&graph).unwrap();

        assert_eq!(sorted, ["D", "C", "B", "A"]);
    }

    fn mk_graph(edges: &[(&str, &[&str])]) -> HashMap<String, Vec<String>> {
        edges
            .iter()
            .map(|(k, vs)| (k.to_string(), vs.iter().map(|s| s.to_string()).collect()))
            .collect()
    }

    #[test]
    fn test_tarjan_self_loop() {
        let g = mk_graph(&[("a", &["a"])]);
        let sccs = tarjan_scc(&g);
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], vec!["a".to_string()]);
        assert!(scc_is_recursive(&sccs[0], &g));
    }

    #[test]
    fn test_tarjan_2_cycle() {
        let g = mk_graph(&[("expr", &["list"]), ("list", &["expr"])]);
        let sccs = tarjan_scc(&g);
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0].len(), 2);
        assert!(scc_is_recursive(&sccs[0], &g));
    }

    #[test]
    fn test_tarjan_acyclic() {
        let g = mk_graph(&[("a", &["b"]), ("b", &["c"]), ("c", &[])]);
        let sccs = tarjan_scc(&g);
        assert_eq!(sccs.len(), 3);
        for scc in &sccs {
            assert!(!scc_is_recursive(scc, &g));
        }
    }

    #[test]
    fn test_tarjan_5member_cycle() {
        let g = mk_graph(&[
            ("expr", &["expr_v"]),
            ("expr_v", &["list"]),
            ("list", &["list_v"]),
            ("list_v", &["list_v_cons"]),
            ("list_v_cons", &["expr", "list"]),
        ]);
        let sccs = tarjan_scc(&g);
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0].len(), 5);
        assert!(scc_is_recursive(&sccs[0], &g));
    }

    #[test]
    fn test_tarjan_mixed() {
        // enum_kind is non-recursive; expr/list form a 2-cycle
        let g = mk_graph(&[
            ("expr_kind", &[]),
            ("list_kind", &[]),
            ("expr", &["expr_kind", "list"]),
            ("list", &["list_kind", "expr"]),
        ]);
        let sccs = tarjan_scc(&g);
        // 4 SCCs: {expr_kind}, {list_kind}, {expr,list}
        let recursive: Vec<_> = sccs.iter().filter(|s| scc_is_recursive(s, &g)).collect();
        assert_eq!(recursive.len(), 1);
        assert_eq!(recursive[0].len(), 2);
    }
}
