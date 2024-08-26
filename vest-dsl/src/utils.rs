use std::collections::{HashMap, HashSet};
use std::hash::Hash;

#[derive(Debug, PartialEq)]
pub enum TopoSortError {
    CycleDetected,
}

pub fn topological_sort<K, V>(graph: &HashMap<K, V>) -> Result<Vec<K>, TopoSortError>
where
    K: Eq + Hash + Clone,
    V: AsRef<[K]>,
{
    let mut visited = HashSet::new();
    let mut visiting = HashSet::new();
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
    graph: &HashMap<K, V>,
    visited: &mut HashSet<K>,
    visiting: &mut HashSet<K>,
    sorted: &mut Vec<K>,
) -> Result<(), TopoSortError>
where
    K: Eq + Hash + Clone,
    V: AsRef<[K]>,
{
    if visiting.contains(&node) {
        return Err(TopoSortError::CycleDetected);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_topological_sort() {
        let mut graph = HashMap::new();
        graph.insert("A", vec!["B", "C"]);
        graph.insert("B", vec!["C"]);
        graph.insert("C", vec!["D"]);
        graph.insert("D", vec!["A"]);

        assert_eq!(topological_sort(&graph), Err(TopoSortError::CycleDetected));
    }

    #[test]
    fn test_topological_sort_2() {
        let mut graph = HashMap::new();
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
        let mut graph = HashMap::new();
        graph.insert("A", vec!["B", "C"]);
        graph.insert("B", vec!["C"]);
        graph.insert("C", vec!["D"]);
        graph.insert("D", vec![]);

        let sorted = topological_sort(&graph).unwrap();

        assert_eq!(sorted, ["D", "C", "B", "A"]);
    }
}
