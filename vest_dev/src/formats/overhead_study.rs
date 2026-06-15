use crate::combinators::recursive::exec::{ParserRecBody, PrepareRecBody, SerializerRecBody};
use crate::combinators::recursive::spec::{BundledSpecs, ParamRecSpecs, SpecRecBody};
use crate::combinators::recursive::{FixWith, StrictRecBody};
use crate::combinators::*;
use crate::core::exec::input::InputBuf;
use crate::core::exec::parser::{PResult, Parser};
use crate::core::exec::serializer::{ComplianceErrorKind, PreSerializeError, Prepare, Serializer};
use crate::core::exec::ParseError;
/// Overhead isolation experiment for mutually recursive parse/serialize.
///
/// Format: a binary tree where each branch node has exactly two children.
///
/// ```vest
/// tree = { @t: u8, v: choose(@t) { 0x10 => u8, 0x11 => node } }
/// node = { left: tree, right: tree }
/// ```
///
/// Three handrolled variants isolate individual overhead sources:
///
///   A. `handrolled`        — direct mutual recursion, no tagging/wrapping
///   B. `handrolled_tagged` — same logic but wraps into a unified enum before
///                            each recursive call (mirrors the ValueRef cost)
///   C. vest FixWith        — the actual verified combinator
///
/// A vs B   →  cost of ValueRef-style wrapping alone
/// B vs C   →  remaining FixWith framework overhead (gas closure, etc.)
/// A vs C   →  total overhead
use vstd::prelude::*;

verus! {
// ── Data types ────────────────────────────────────────────────────────────────

#[derive(Debug, PartialEq, Eq)]
#[verifier::ext_equal]
pub enum Tree {
    Leaf(u8),
    Branch(Box<Node>),
}

#[derive(Debug, PartialEq, Eq)]
#[verifier::ext_equal]
pub struct Node {
    pub left: Tree,
    pub right: Tree,
}

pub type TreeSpec = Tree;
pub type NodeSpec = Node;

impl DeepView for Tree {
    type V = TreeSpec;
    open spec fn deep_view(&self) -> Self::V { *self }
}

impl DeepView for Node {
    type V = NodeSpec;
    open spec fn deep_view(&self) -> Self::V { *self }
}

// ── Unified value and ref types for mutual recursion ─────────────────────────

#[derive(Debug, PartialEq, Eq)]
pub enum TreeNodeValue {
    IsTree { tree: Tree },
    IsNode { node: Node },
}

pub type TreeNodeValueSpec = TreeNodeValue;

impl DeepView for TreeNodeValue {
    type V = TreeNodeValueSpec;
    open spec fn deep_view(&self) -> Self::V { *self }
}

pub enum TreeNodeValueRef<'a> {
    IsTree { tree: &'a Tree },
    IsNode { node: &'a Node },
}

impl DeepView for TreeNodeValueRef<'_> {
    type V = TreeNodeValueSpec;
    open spec fn deep_view(&self) -> Self::V {
        match self {
            TreeNodeValueRef::IsTree { tree } =>
                TreeNodeValueSpec::IsTree { tree: tree.deep_view() },
            TreeNodeValueRef::IsNode { node } =>
                TreeNodeValueSpec::IsNode { node: node.deep_view() },
        }
    }
}

// ── Param ─────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum WhichFmt { TREE, NODE }

impl DeepView for WhichFmt {
    type V = Self;
    open spec fn deep_view(&self) -> Self::V { *self }
}

// ── SpecRecBody Stubs ───────────────────────────────────────────────────────────────

pub struct TreeNodeRecBody;

impl SpecRecBody for TreeNodeRecBody {
    type Param = WhichFmt;
    type T     = TreeNodeValueSpec;
    type Body  = BundledSpecs<TreeNodeValueSpec>;

    open spec fn spec_body(
        _which: Self::Param,
        _rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        arbitrary()
    }
}

impl StrictRecBody for TreeNodeRecBody {
    #[verifier::external_body]
    proof fn lemma_body_all_inv_preservation(
        _param: Self::Param,
        _rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {}
}

// ── Parser ────────────────────────────────────────────────────────────────────

impl<'i> ParserRecBody<&'i [u8]> for TreeNodeRecBody {
    type EP = WhichFmt;
    type O  = TreeNodeValue;

    #[verifier::external_body]
    fn parse_body<Exec>(
        &self,
        which: &WhichFmt,
        Ghost(_spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        ibuf: &&'i [u8],
    ) -> PResult<Self::O>
    where
        Exec: Fn(&WhichFmt, &&'i [u8]) -> PResult<Self::O>,
    {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        let _ = ibuf.len();

        match which {
            WhichFmt::TREE => {
                let (n1, tag) = U8.parse(ibuf)?;
                let rest = ibuf.skip(n1);
                match tag {
                    0x10u8 => {
                        let (n2, leaf) = U8.parse(&rest)?;
                        Ok((n1 + n2, TreeNodeValue::IsTree { tree: Tree::Leaf(leaf) }))
                    }
                    0x11u8 => {
                        let (n, inner) = exec_rec(&WhichFmt::NODE, &rest)?;
                        match inner {
                            TreeNodeValue::IsNode { node } =>
                                Ok((n1 + n, TreeNodeValue::IsTree {
                                    tree: Tree::Branch(Box::new(node)),
                                })),
                            _ => Err(ParseError::cond_rejected()),
                        }
                    }
                    _ => Err(ParseError::invalid_tag()),
                }
            }
            WhichFmt::NODE => {
                let (nl, lv) = exec_rec(&WhichFmt::TREE, ibuf)?;
                let rest = ibuf.skip(nl);
                let (nr, rv) = exec_rec(&WhichFmt::TREE, &rest)?;
                match (lv, rv) {
                    (TreeNodeValue::IsTree { tree: left },
                     TreeNodeValue::IsTree { tree: right }) =>
                        Ok((nl + nr, TreeNodeValue::IsNode {
                            node: Node { left, right },
                        })),
                    _ => Err(ParseError::cond_rejected()),
                }
            }
        }
    }
}

// ── Serializer ────────────────────────────────────────────────────────────────

impl<'a> SerializerRecBody<TreeNodeValueRef<'a>> for TreeNodeRecBody {
    type EP = WhichFmt;

    #[verifier::external_body]
    fn serialize_body<Exec>(
        &self,
        _which: &WhichFmt,
        Ghost(_spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &TreeNodeValueRef<'a>,
        obuf: &mut Vec<u8>,
    )
    where
        Exec: Fn(&WhichFmt, &TreeNodeValueRef<'a>, &mut Vec<u8>),
    {
        match v {
            TreeNodeValueRef::IsTree { tree: Tree::Leaf(b) } => {
                U8.serialize(&0x10u8, obuf);
                U8.serialize(b, obuf);
            }
            TreeNodeValueRef::IsTree { tree: Tree::Branch(node) } => {
                U8.serialize(&0x11u8, obuf);
                let child = TreeNodeValueRef::IsNode { node };
                exec_rec(&WhichFmt::NODE, &child, obuf);
            }
            TreeNodeValueRef::IsNode { node } => {
                let lc = TreeNodeValueRef::IsTree { tree: &node.left };
                let rc = TreeNodeValueRef::IsTree { tree: &node.right };
                exec_rec(&WhichFmt::TREE, &lc, obuf);
                exec_rec(&WhichFmt::TREE, &rc, obuf);
            }
        }
    }
}

// ── Prepare ───────────────────────────────────────────────────────────────────

impl<'a> PrepareRecBody<TreeNodeValueRef<'a>> for TreeNodeRecBody {
    type EP = WhichFmt;

    #[verifier::external_body]
    fn prepare_body<Exec>(
        &self,
        _which: &WhichFmt,
        Ghost(_spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &TreeNodeValueRef<'a>,
    ) -> Result<usize, PreSerializeError>
    where
        Exec: Fn(&WhichFmt, &TreeNodeValueRef<'a>) -> Result<usize, PreSerializeError>,
    {
        match v {
            TreeNodeValueRef::IsTree { tree: Tree::Leaf(_) } => Ok(2),
            TreeNodeValueRef::IsTree { tree: Tree::Branch(node) } => {
                let child = TreeNodeValueRef::IsNode { node };
                Ok(1 + exec_rec(&WhichFmt::NODE, &child)?)
            }
            TreeNodeValueRef::IsNode { node } => {
                let lc = TreeNodeValueRef::IsTree { tree: &node.left };
                let rc = TreeNodeValueRef::IsTree { tree: &node.right };
                let l = exec_rec(&WhichFmt::TREE, &lc)?;
                let r = exec_rec(&WhichFmt::TREE, &rc)?;
                l.checked_add(r).ok_or_else(|| PreSerializeError::length_too_large())
            }
        }
    }
}

} // verus!

// ── Runtime-only helpers (no Verus) ──────────────────────────────────────────

pub const BENCH_RECURSION_LIMIT: usize = 512;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HError {
    UnexpectedEof,
    InvalidTag,
    RecursionLimitExceeded,
    Overflow,
}

// ────────────────────────────────────────────────────────────────────────────
// Variant A: plain handrolled mutual recursion, no wrapping
// ────────────────────────────────────────────────────────────────────────────

pub fn handrolled_parse_tree(input: &[u8]) -> Result<(usize, Tree), HError> {
    parse_tree_gas(BENCH_RECURSION_LIMIT, input)
}

fn parse_tree_gas(gas: usize, input: &[u8]) -> Result<(usize, Tree), HError> {
    let Some((&tag, rest)) = input.split_first() else {
        return Err(HError::UnexpectedEof);
    };
    match tag {
        0x10 => {
            let Some((&b, _)) = rest.split_first() else {
                return Err(HError::UnexpectedEof);
            };
            Ok((2, Tree::Leaf(b)))
        }
        0x11 => {
            if gas == 0 {
                return Err(HError::RecursionLimitExceeded);
            }
            let (n, node) = parse_node_gas(gas - 1, rest)?;
            Ok((1 + n, Tree::Branch(Box::new(node))))
        }
        _ => Err(HError::InvalidTag),
    }
}

fn parse_node_gas(gas: usize, input: &[u8]) -> Result<(usize, Node), HError> {
    if gas == 0 {
        return Err(HError::RecursionLimitExceeded);
    }
    let (nl, left) = parse_tree_gas(gas - 1, input)?;
    let (nr, right) = parse_tree_gas(gas - 1, &input[nl..])?;
    Ok((nl + nr, Node { left, right }))
}

pub fn handrolled_serialize_tree(v: &Tree, obuf: &mut Vec<u8>) -> Result<(), HError> {
    serialize_tree_gas(BENCH_RECURSION_LIMIT, v, obuf)
}

fn serialize_tree_gas(gas: usize, v: &Tree, obuf: &mut Vec<u8>) -> Result<(), HError> {
    match v {
        Tree::Leaf(b) => {
            obuf.push(0x10);
            obuf.push(*b);
            Ok(())
        }
        Tree::Branch(node) => {
            obuf.push(0x11);
            if gas == 0 {
                return Err(HError::RecursionLimitExceeded);
            }
            serialize_node_gas(gas - 1, node, obuf)
        }
    }
}

fn serialize_node_gas(gas: usize, v: &Node, obuf: &mut Vec<u8>) -> Result<(), HError> {
    if gas == 0 {
        return Err(HError::RecursionLimitExceeded);
    }
    // Two sequential recursive calls: NOT tail-recursive
    serialize_tree_gas(gas - 1, &v.left, obuf)?;
    serialize_tree_gas(gas - 1, &v.right, obuf)
}

pub fn handrolled_prepare_tree(v: &Tree) -> Result<usize, HError> {
    prepare_tree_gas(BENCH_RECURSION_LIMIT, v)
}

fn prepare_tree_gas(gas: usize, v: &Tree) -> Result<usize, HError> {
    match v {
        Tree::Leaf(_) => Ok(2),
        Tree::Branch(node) => {
            if gas == 0 {
                return Err(HError::RecursionLimitExceeded);
            }
            Ok(1 + prepare_node_gas(gas - 1, node)?)
        }
    }
}

fn prepare_node_gas(gas: usize, v: &Node) -> Result<usize, HError> {
    if gas == 0 {
        return Err(HError::RecursionLimitExceeded);
    }
    let l = prepare_tree_gas(gas - 1, &v.left)?;
    let r = prepare_tree_gas(gas - 1, &v.right)?;
    l.checked_add(r).ok_or(HError::Overflow)
}

// ────────────────────────────────────────────────────────────────────────────
// Variant B: handrolled with explicit TaggedValue wrapping (mirrors ValueRef)
// ────────────────────────────────────────────────────────────────────────────

pub enum TaggedValue<'a> {
    IsTree { tree: &'a Tree },
    IsNode { node: &'a Node },
}

pub enum TaggedOwned {
    IsTree { tree: Tree },
    IsNode { node: Node },
}

pub fn handrolled_tagged_parse_tree(input: &[u8]) -> Result<(usize, Tree), HError> {
    match tagged_parse_gas(BENCH_RECURSION_LIMIT, false, input)? {
        (n, TaggedOwned::IsTree { tree }) => Ok((n, tree)),
        _ => Err(HError::InvalidTag),
    }
}

fn tagged_parse_gas(
    gas: usize,
    is_node: bool,
    input: &[u8],
) -> Result<(usize, TaggedOwned), HError> {
    if !is_node {
        let Some((&tag, rest)) = input.split_first() else {
            return Err(HError::UnexpectedEof);
        };
        match tag {
            0x10 => {
                let Some((&b, _)) = rest.split_first() else {
                    return Err(HError::UnexpectedEof);
                };
                Ok((
                    2,
                    TaggedOwned::IsTree {
                        tree: Tree::Leaf(b),
                    },
                ))
            }
            0x11 => {
                if gas == 0 {
                    return Err(HError::RecursionLimitExceeded);
                }
                match tagged_parse_gas(gas - 1, true, rest)? {
                    (n, TaggedOwned::IsNode { node }) => Ok((
                        1 + n,
                        TaggedOwned::IsTree {
                            tree: Tree::Branch(Box::new(node)),
                        },
                    )),
                    _ => Err(HError::InvalidTag),
                }
            }
            _ => Err(HError::InvalidTag),
        }
    } else {
        if gas == 0 {
            return Err(HError::RecursionLimitExceeded);
        }
        let (nl, lv) = tagged_parse_gas(gas - 1, false, input)?;
        let (nr, rv) = tagged_parse_gas(gas - 1, false, &input[nl..])?;
        match (lv, rv) {
            (TaggedOwned::IsTree { tree: left }, TaggedOwned::IsTree { tree: right }) => Ok((
                nl + nr,
                TaggedOwned::IsNode {
                    node: Node { left, right },
                },
            )),
            _ => Err(HError::InvalidTag),
        }
    }
}

pub fn handrolled_tagged_serialize_tree(v: &Tree, obuf: &mut Vec<u8>) -> Result<(), HError> {
    tagged_serialize_gas(
        BENCH_RECURSION_LIMIT,
        &TaggedValue::IsTree { tree: v },
        obuf,
    )
}

fn tagged_serialize_gas<'a>(
    gas: usize,
    v: &TaggedValue<'a>,
    obuf: &mut Vec<u8>,
) -> Result<(), HError> {
    match v {
        TaggedValue::IsTree {
            tree: Tree::Leaf(b),
        } => {
            obuf.push(0x10);
            obuf.push(*b);
            Ok(())
        }
        TaggedValue::IsTree {
            tree: Tree::Branch(node),
        } => {
            obuf.push(0x11);
            if gas == 0 {
                return Err(HError::RecursionLimitExceeded);
            }
            tagged_serialize_gas(gas - 1, &TaggedValue::IsNode { node }, obuf)
        }
        TaggedValue::IsNode { node } => {
            if gas == 0 {
                return Err(HError::RecursionLimitExceeded);
            }
            tagged_serialize_gas(gas - 1, &TaggedValue::IsTree { tree: &node.left }, obuf)?;
            tagged_serialize_gas(gas - 1, &TaggedValue::IsTree { tree: &node.right }, obuf)
        }
    }
}

pub fn handrolled_tagged_prepare_tree(v: &Tree) -> Result<usize, HError> {
    tagged_prepare_gas(BENCH_RECURSION_LIMIT, &TaggedValue::IsTree { tree: v })
}

fn tagged_prepare_gas(gas: usize, v: &TaggedValue<'_>) -> Result<usize, HError> {
    match v {
        TaggedValue::IsTree {
            tree: Tree::Leaf(_),
        } => Ok(2),
        TaggedValue::IsTree {
            tree: Tree::Branch(node),
        } => {
            if gas == 0 {
                return Err(HError::RecursionLimitExceeded);
            }
            Ok(1 + tagged_prepare_gas(gas - 1, &TaggedValue::IsNode { node })?)
        }
        TaggedValue::IsNode { node } => {
            if gas == 0 {
                return Err(HError::RecursionLimitExceeded);
            }
            let l = tagged_prepare_gas(gas - 1, &TaggedValue::IsTree { tree: &node.left })?;
            let r = tagged_prepare_gas(gas - 1, &TaggedValue::IsTree { tree: &node.right })?;
            l.checked_add(r).ok_or(HError::Overflow)
        }
    }
}

// ── Corpus generation ─────────────────────────────────────────────────────────

fn bench_byte(seed: usize) -> u8 {
    ((seed.wrapping_mul(31).wrapping_add(11)) % 251) as u8
}

/// Balanced binary tree: depth=0 → Leaf, depth=k → Branch{left,right} each depth k-1.
pub fn bench_tree(seed: usize, depth: usize) -> Tree {
    if depth == 0 {
        Tree::Leaf(bench_byte(seed))
    } else {
        Tree::Branch(Box::new(Node {
            left: bench_tree(seed.wrapping_mul(2).wrapping_add(1), depth - 1),
            right: bench_tree(seed.wrapping_mul(3).wrapping_add(7), depth - 1),
        }))
    }
}

/// 96 trees with depths 2–7 (matches mutual_fix corpus sizing).
pub fn benchmark_tree_values() -> Vec<Tree> {
    (0..96usize)
        .map(|seed| bench_tree(seed, (seed % 6) + 2))
        .collect()
}
