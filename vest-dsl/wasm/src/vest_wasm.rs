#![allow(warnings)]
#![allow(unused)]
use std::marker::PhantomData;
use vstd::prelude::*;
use vest::regular::modifier::*;
use vest::regular::bytes;
use vest::regular::variant::*;
use vest::regular::sequence::*;
use vest::regular::repetition::*;
use vest::regular::disjoint::DisjointFrom;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vest::utils::*;
use vest::properties::*;
use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::regular::leb128::*;
verus!{
pub type SpecElemidx = u64;
pub type Elemidx = u64;


pub struct SpecElemidxCombinator(SpecElemidxCombinatorAlias);

impl SpecCombinator for SpecElemidxCombinator {
    type Type = SpecElemidx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemidxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecElemidxCombinatorAlias = UnsignedLEB128;

pub struct ElemidxCombinator(ElemidxCombinatorAlias);

impl View for ElemidxCombinator {
    type V = SpecElemidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemidxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ElemidxCombinator {
    type Type = Elemidx;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ElemidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_elemidx() -> SpecElemidxCombinator {
    SpecElemidxCombinator(UnsignedLEB128)
}

                
pub fn elemidx() -> (o: ElemidxCombinator)
    ensures o@ == spec_elemidx(),
{
    ElemidxCombinator(UnsignedLEB128)
}

                
pub type SpecTableidx = u64;
pub type Tableidx = u64;


pub struct SpecTableidxCombinator(SpecTableidxCombinatorAlias);

impl SpecCombinator for SpecTableidxCombinator {
    type Type = SpecTableidx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableidxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTableidxCombinatorAlias = UnsignedLEB128;

pub struct TableidxCombinator(TableidxCombinatorAlias);

impl View for TableidxCombinator {
    type V = SpecTableidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableidxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TableidxCombinator {
    type Type = Tableidx;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TableidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_tableidx() -> SpecTableidxCombinator {
    SpecTableidxCombinator(UnsignedLEB128)
}

                
pub fn tableidx() -> (o: TableidxCombinator)
    ensures o@ == spec_tableidx(),
{
    TableidxCombinator(UnsignedLEB128)
}

                

pub struct SpecTableInit {
    pub y: SpecElemidx,
    pub x: SpecTableidx,
}

pub type SpecTableInitInner = (SpecElemidx, SpecTableidx);
impl SpecFrom<SpecTableInit> for SpecTableInitInner {
    open spec fn spec_from(m: SpecTableInit) -> SpecTableInitInner {
        (m.y, m.x)
    }
}
impl SpecFrom<SpecTableInitInner> for SpecTableInit {
    open spec fn spec_from(m: SpecTableInitInner) -> SpecTableInit {
        let (y, x) = m;
        SpecTableInit { y, x }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TableInit {
    pub y: Elemidx,
    pub x: Tableidx,
}

impl View for TableInit {
    type V = SpecTableInit;

    open spec fn view(&self) -> Self::V {
        SpecTableInit {
            y: self.y@,
            x: self.x@,
        }
    }
}
pub type TableInitInner = (Elemidx, Tableidx);
impl From<TableInit> for TableInitInner {
    fn ex_from(m: TableInit) -> TableInitInner {
        (m.y, m.x)
    }
}
impl From<TableInitInner> for TableInit {
    fn ex_from(m: TableInitInner) -> TableInit {
        let (y, x) = m;
        TableInit { y, x }
    }
}

pub struct TableInitMapper;
impl TableInitMapper {
    pub closed spec fn spec_new() -> Self {
        TableInitMapper
    }
    pub fn new() -> Self {
        TableInitMapper
    }
}
impl View for TableInitMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TableInitMapper {
    type Src = SpecTableInitInner;
    type Dst = SpecTableInit;
}
impl SpecIsoProof for TableInitMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for TableInitMapper {
    type Src = TableInitInner;
    type Dst = TableInit;
}

pub struct SpecTableInitCombinator(SpecTableInitCombinatorAlias);

impl SpecCombinator for SpecTableInitCombinator {
    type Type = SpecTableInit;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableInitCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableInitCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTableInitCombinatorAlias = Mapped<(SpecElemidxCombinator, SpecTableidxCombinator), TableInitMapper>;

pub struct TableInitCombinator(TableInitCombinatorAlias);

impl View for TableInitCombinator {
    type V = SpecTableInitCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableInitCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TableInitCombinator {
    type Type = TableInit;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TableInitCombinatorAlias = Mapped<(ElemidxCombinator, TableidxCombinator), TableInitMapper>;


pub closed spec fn spec_table_init() -> SpecTableInitCombinator {
    SpecTableInitCombinator(
    Mapped {
        inner: (spec_elemidx(), spec_tableidx()),
        mapper: TableInitMapper::spec_new(),
    })
}

                
pub fn table_init() -> (o: TableInitCombinator)
    ensures o@ == spec_table_init(),
{
    TableInitCombinator(
    Mapped {
        inner: (elemidx(), tableidx()),
        mapper: TableInitMapper::new(),
    })
}

                
pub type SpecElemDrop = SpecElemidx;
pub type ElemDrop = Elemidx;


pub struct SpecElemDropCombinator(SpecElemDropCombinatorAlias);

impl SpecCombinator for SpecElemDropCombinator {
    type Type = SpecElemDrop;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemDropCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemDropCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecElemDropCombinatorAlias = SpecElemidxCombinator;

pub struct ElemDropCombinator(ElemDropCombinatorAlias);

impl View for ElemDropCombinator {
    type V = SpecElemDropCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemDropCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ElemDropCombinator {
    type Type = ElemDrop;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ElemDropCombinatorAlias = ElemidxCombinator;


pub closed spec fn spec_elem_drop() -> SpecElemDropCombinator {
    SpecElemDropCombinator(spec_elemidx())
}

                
pub fn elem_drop() -> (o: ElemDropCombinator)
    ensures o@ == spec_elem_drop(),
{
    ElemDropCombinator(elemidx())
}

                

pub struct SpecTableCopy {
    pub x: SpecTableidx,
    pub y: SpecTableidx,
}

pub type SpecTableCopyInner = (SpecTableidx, SpecTableidx);
impl SpecFrom<SpecTableCopy> for SpecTableCopyInner {
    open spec fn spec_from(m: SpecTableCopy) -> SpecTableCopyInner {
        (m.x, m.y)
    }
}
impl SpecFrom<SpecTableCopyInner> for SpecTableCopy {
    open spec fn spec_from(m: SpecTableCopyInner) -> SpecTableCopy {
        let (x, y) = m;
        SpecTableCopy { x, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TableCopy {
    pub x: Tableidx,
    pub y: Tableidx,
}

impl View for TableCopy {
    type V = SpecTableCopy;

    open spec fn view(&self) -> Self::V {
        SpecTableCopy {
            x: self.x@,
            y: self.y@,
        }
    }
}
pub type TableCopyInner = (Tableidx, Tableidx);
impl From<TableCopy> for TableCopyInner {
    fn ex_from(m: TableCopy) -> TableCopyInner {
        (m.x, m.y)
    }
}
impl From<TableCopyInner> for TableCopy {
    fn ex_from(m: TableCopyInner) -> TableCopy {
        let (x, y) = m;
        TableCopy { x, y }
    }
}

pub struct TableCopyMapper;
impl TableCopyMapper {
    pub closed spec fn spec_new() -> Self {
        TableCopyMapper
    }
    pub fn new() -> Self {
        TableCopyMapper
    }
}
impl View for TableCopyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TableCopyMapper {
    type Src = SpecTableCopyInner;
    type Dst = SpecTableCopy;
}
impl SpecIsoProof for TableCopyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for TableCopyMapper {
    type Src = TableCopyInner;
    type Dst = TableCopy;
}

pub struct SpecTableCopyCombinator(SpecTableCopyCombinatorAlias);

impl SpecCombinator for SpecTableCopyCombinator {
    type Type = SpecTableCopy;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableCopyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableCopyCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTableCopyCombinatorAlias = Mapped<(SpecTableidxCombinator, SpecTableidxCombinator), TableCopyMapper>;

pub struct TableCopyCombinator(TableCopyCombinatorAlias);

impl View for TableCopyCombinator {
    type V = SpecTableCopyCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableCopyCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TableCopyCombinator {
    type Type = TableCopy;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TableCopyCombinatorAlias = Mapped<(TableidxCombinator, TableidxCombinator), TableCopyMapper>;


pub closed spec fn spec_table_copy() -> SpecTableCopyCombinator {
    SpecTableCopyCombinator(
    Mapped {
        inner: (spec_tableidx(), spec_tableidx()),
        mapper: TableCopyMapper::spec_new(),
    })
}

                
pub fn table_copy() -> (o: TableCopyCombinator)
    ensures o@ == spec_table_copy(),
{
    TableCopyCombinator(
    Mapped {
        inner: (tableidx(), tableidx()),
        mapper: TableCopyMapper::new(),
    })
}

                
pub type SpecTableGrow = SpecTableidx;
pub type TableGrow = Tableidx;


pub struct SpecTableGrowCombinator(SpecTableGrowCombinatorAlias);

impl SpecCombinator for SpecTableGrowCombinator {
    type Type = SpecTableGrow;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableGrowCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableGrowCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTableGrowCombinatorAlias = SpecTableidxCombinator;

pub struct TableGrowCombinator(TableGrowCombinatorAlias);

impl View for TableGrowCombinator {
    type V = SpecTableGrowCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableGrowCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TableGrowCombinator {
    type Type = TableGrow;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TableGrowCombinatorAlias = TableidxCombinator;


pub closed spec fn spec_table_grow() -> SpecTableGrowCombinator {
    SpecTableGrowCombinator(spec_tableidx())
}

                
pub fn table_grow() -> (o: TableGrowCombinator)
    ensures o@ == spec_table_grow(),
{
    TableGrowCombinator(tableidx())
}

                
pub type SpecTableSize = SpecTableidx;
pub type TableSize = Tableidx;


pub struct SpecTableSizeCombinator(SpecTableSizeCombinatorAlias);

impl SpecCombinator for SpecTableSizeCombinator {
    type Type = SpecTableSize;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableSizeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableSizeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTableSizeCombinatorAlias = SpecTableidxCombinator;

pub struct TableSizeCombinator(TableSizeCombinatorAlias);

impl View for TableSizeCombinator {
    type V = SpecTableSizeCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableSizeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TableSizeCombinator {
    type Type = TableSize;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TableSizeCombinatorAlias = TableidxCombinator;


pub closed spec fn spec_table_size() -> SpecTableSizeCombinator {
    SpecTableSizeCombinator(spec_tableidx())
}

                
pub fn table_size() -> (o: TableSizeCombinator)
    ensures o@ == spec_table_size(),
{
    TableSizeCombinator(tableidx())
}

                
pub type SpecTableFill = SpecTableidx;
pub type TableFill = Tableidx;


pub struct SpecTableFillCombinator(SpecTableFillCombinatorAlias);

impl SpecCombinator for SpecTableFillCombinator {
    type Type = SpecTableFill;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableFillCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableFillCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTableFillCombinatorAlias = SpecTableidxCombinator;

pub struct TableFillCombinator(TableFillCombinatorAlias);

impl View for TableFillCombinator {
    type V = SpecTableFillCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableFillCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TableFillCombinator {
    type Type = TableFill;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TableFillCombinatorAlias = TableidxCombinator;


pub closed spec fn spec_table_fill() -> SpecTableFillCombinator {
    SpecTableFillCombinator(spec_tableidx())
}

                
pub fn table_fill() -> (o: TableFillCombinator)
    ensures o@ == spec_table_fill(),
{
    TableFillCombinator(tableidx())
}

                
pub type SpecDataidx = u64;
pub type Dataidx = u64;


pub struct SpecDataidxCombinator(SpecDataidxCombinatorAlias);

impl SpecCombinator for SpecDataidxCombinator {
    type Type = SpecDataidx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDataidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDataidxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecDataidxCombinatorAlias = UnsignedLEB128;

pub struct DataidxCombinator(DataidxCombinatorAlias);

impl View for DataidxCombinator {
    type V = SpecDataidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecDataidxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for DataidxCombinator {
    type Type = Dataidx;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type DataidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_dataidx() -> SpecDataidxCombinator {
    SpecDataidxCombinator(UnsignedLEB128)
}

                
pub fn dataidx() -> (o: DataidxCombinator)
    ensures o@ == spec_dataidx(),
{
    DataidxCombinator(UnsignedLEB128)
}

                
pub type SpecMemoryInit = SpecDataidx;
pub type MemoryInit = Dataidx;


pub const MemoryInit_0_BACK_CONST: u8 = 0;

pub struct SpecMemoryInitCombinator(SpecMemoryInitCombinatorAlias);

impl SpecCombinator for SpecMemoryInitCombinator {
    type Type = SpecMemoryInit;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemoryInitCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemoryInitCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMemoryInitCombinatorAlias = Terminated<SpecDataidxCombinator, Tag<U8, u8>>;


pub struct MemoryInitCombinator(MemoryInitCombinatorAlias);

impl View for MemoryInitCombinator {
    type V = SpecMemoryInitCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemoryInitCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MemoryInitCombinator {
    type Type = MemoryInit;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MemoryInitCombinatorAlias = Terminated<DataidxCombinator, Tag<U8, u8>>;


pub closed spec fn spec_memory_init() -> SpecMemoryInitCombinator {
    SpecMemoryInitCombinator(Terminated(spec_dataidx(), Tag::spec_new(U8, MemoryInit_0_BACK_CONST)))
}

                
pub fn memory_init() -> (o: MemoryInitCombinator)
    ensures o@ == spec_memory_init(),
{
    MemoryInitCombinator(Terminated(dataidx(), Tag::new(U8, MemoryInit_0_BACK_CONST)))
}

                
pub type SpecDataDrop = SpecDataidx;
pub type DataDrop = Dataidx;


pub struct SpecDataDropCombinator(SpecDataDropCombinatorAlias);

impl SpecCombinator for SpecDataDropCombinator {
    type Type = SpecDataDrop;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDataDropCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDataDropCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecDataDropCombinatorAlias = SpecDataidxCombinator;

pub struct DataDropCombinator(DataDropCombinatorAlias);

impl View for DataDropCombinator {
    type V = SpecDataDropCombinator;
    closed spec fn view(&self) -> Self::V { SpecDataDropCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for DataDropCombinator {
    type Type = DataDrop;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type DataDropCombinatorAlias = DataidxCombinator;


pub closed spec fn spec_data_drop() -> SpecDataDropCombinator {
    SpecDataDropCombinator(spec_dataidx())
}

                
pub fn data_drop() -> (o: DataDropCombinator)
    ensures o@ == spec_data_drop(),
{
    DataDropCombinator(dataidx())
}

                

pub struct SpecMemoryCopy {
    pub reserved: Seq<u8>,
}

pub type SpecMemoryCopyInner = Seq<u8>;
impl SpecFrom<SpecMemoryCopy> for SpecMemoryCopyInner {
    open spec fn spec_from(m: SpecMemoryCopy) -> SpecMemoryCopyInner {
        m.reserved
    }
}
impl SpecFrom<SpecMemoryCopyInner> for SpecMemoryCopy {
    open spec fn spec_from(m: SpecMemoryCopyInner) -> SpecMemoryCopy {
        let reserved = m;
        SpecMemoryCopy { reserved }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MemoryCopy<'a> {
    pub reserved: &'a [u8],
}

impl View for MemoryCopy<'_> {
    type V = SpecMemoryCopy;

    open spec fn view(&self) -> Self::V {
        SpecMemoryCopy {
            reserved: self.reserved@,
        }
    }
}
pub type MemoryCopyInner<'a> = &'a [u8];
impl<'a> From<MemoryCopy<'a>> for MemoryCopyInner<'a> {
    fn ex_from(m: MemoryCopy) -> MemoryCopyInner {
        m.reserved
    }
}
impl<'a> From<MemoryCopyInner<'a>> for MemoryCopy<'a> {
    fn ex_from(m: MemoryCopyInner) -> MemoryCopy {
        let reserved = m;
        MemoryCopy { reserved }
    }
}

pub struct MemoryCopyMapper<'a>(PhantomData<&'a ()>);
impl<'a> MemoryCopyMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MemoryCopyMapper(PhantomData)
    }
    pub fn new() -> Self {
        MemoryCopyMapper(PhantomData)
    }
}
impl View for MemoryCopyMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemoryCopyMapper<'_> {
    type Src = SpecMemoryCopyInner;
    type Dst = SpecMemoryCopy;
}
impl SpecIsoProof for MemoryCopyMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for MemoryCopyMapper<'a> {
    type Src = MemoryCopyInner<'a>;
    type Dst = MemoryCopy<'a>;
}
pub spec const SPEC_MEMORYCOPYRESERVED_CONST: Seq<u8> = seq![0, 0];
pub struct SpecMemoryCopyCombinator(SpecMemoryCopyCombinatorAlias);

impl SpecCombinator for SpecMemoryCopyCombinator {
    type Type = SpecMemoryCopy;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemoryCopyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemoryCopyCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMemoryCopyCombinatorAlias = Mapped<Refined<bytes::Fixed<2>, TagPred<Seq<u8>>>, MemoryCopyMapper<'static>>;
pub exec static MEMORYCOPYRESERVED_CONST: [u8; 2]
    ensures MEMORYCOPYRESERVED_CONST@ == SPEC_MEMORYCOPYRESERVED_CONST,
{
    let arr: [u8; 2] = [0, 0];
    assert(arr@ == SPEC_MEMORYCOPYRESERVED_CONST);
    arr
}

pub struct MemoryCopyCombinator<'a>(MemoryCopyCombinatorAlias<'a>);

impl<'a> View for MemoryCopyCombinator<'a> {
    type V = SpecMemoryCopyCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemoryCopyCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MemoryCopyCombinator<'a> {
    type Type = MemoryCopy<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MemoryCopyCombinatorAlias<'a> = Mapped<Refined<bytes::Fixed<2>, TagPred<&'a [u8]>>, MemoryCopyMapper<'a>>;


pub closed spec fn spec_memory_copy() -> SpecMemoryCopyCombinator {
    SpecMemoryCopyCombinator(
    Mapped {
        inner: Refined { inner: bytes::Fixed::<2>, predicate: TagPred(SPEC_MEMORYCOPYRESERVED_CONST) },
        mapper: MemoryCopyMapper::spec_new(),
    })
}

                
pub fn memory_copy<'a>() -> (o: MemoryCopyCombinator<'a>)
    ensures o@ == spec_memory_copy(),
{
    MemoryCopyCombinator(
    Mapped {
        inner: Refined { inner: bytes::Fixed::<2>, predicate: TagPred(MEMORYCOPYRESERVED_CONST.as_slice()) },
        mapper: MemoryCopyMapper::new(),
    })
}

                

pub struct SpecMemoryFill {
    pub reserved: u8,
}

pub type SpecMemoryFillInner = u8;
impl SpecFrom<SpecMemoryFill> for SpecMemoryFillInner {
    open spec fn spec_from(m: SpecMemoryFill) -> SpecMemoryFillInner {
        m.reserved
    }
}
impl SpecFrom<SpecMemoryFillInner> for SpecMemoryFill {
    open spec fn spec_from(m: SpecMemoryFillInner) -> SpecMemoryFill {
        let reserved = m;
        SpecMemoryFill { reserved }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MemoryFill {
    pub reserved: u8,
}

impl View for MemoryFill {
    type V = SpecMemoryFill;

    open spec fn view(&self) -> Self::V {
        SpecMemoryFill {
            reserved: self.reserved@,
        }
    }
}
pub type MemoryFillInner = u8;
impl From<MemoryFill> for MemoryFillInner {
    fn ex_from(m: MemoryFill) -> MemoryFillInner {
        m.reserved
    }
}
impl From<MemoryFillInner> for MemoryFill {
    fn ex_from(m: MemoryFillInner) -> MemoryFill {
        let reserved = m;
        MemoryFill { reserved }
    }
}

pub struct MemoryFillMapper;
impl MemoryFillMapper {
    pub closed spec fn spec_new() -> Self {
        MemoryFillMapper
    }
    pub fn new() -> Self {
        MemoryFillMapper
    }
}
impl View for MemoryFillMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemoryFillMapper {
    type Src = SpecMemoryFillInner;
    type Dst = SpecMemoryFill;
}
impl SpecIsoProof for MemoryFillMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for MemoryFillMapper {
    type Src = MemoryFillInner;
    type Dst = MemoryFill;
}
pub const MEMORYFILLRESERVED_CONST: u8 = 0;

pub struct SpecMemoryFillCombinator(SpecMemoryFillCombinatorAlias);

impl SpecCombinator for SpecMemoryFillCombinator {
    type Type = SpecMemoryFill;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemoryFillCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemoryFillCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMemoryFillCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, MemoryFillMapper>;

pub struct MemoryFillCombinator(MemoryFillCombinatorAlias);

impl View for MemoryFillCombinator {
    type V = SpecMemoryFillCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemoryFillCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MemoryFillCombinator {
    type Type = MemoryFill;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MemoryFillCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, MemoryFillMapper>;


pub closed spec fn spec_memory_fill() -> SpecMemoryFillCombinator {
    SpecMemoryFillCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(MEMORYFILLRESERVED_CONST) },
        mapper: MemoryFillMapper::spec_new(),
    })
}

                
pub fn memory_fill() -> (o: MemoryFillCombinator)
    ensures o@ == spec_memory_fill(),
{
    MemoryFillCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(MEMORYFILLRESERVED_CONST) },
        mapper: MemoryFillMapper::new(),
    })
}

                
pub type SpecEmpty = Seq<u8>;
pub type Empty<'a> = &'a [u8];


pub struct SpecEmptyCombinator(SpecEmptyCombinatorAlias);

impl SpecCombinator for SpecEmptyCombinator {
    type Type = SpecEmpty;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEmptyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEmptyCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecEmptyCombinatorAlias = bytes::Fixed<0>;

pub struct EmptyCombinator(EmptyCombinatorAlias);

impl View for EmptyCombinator {
    type V = SpecEmptyCombinator;
    closed spec fn view(&self) -> Self::V { SpecEmptyCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EmptyCombinator {
    type Type = Empty<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EmptyCombinatorAlias = bytes::Fixed<0>;


pub closed spec fn spec_empty() -> SpecEmptyCombinator {
    SpecEmptyCombinator(bytes::Fixed::<0>)
}

                
pub fn empty() -> (o: EmptyCombinator)
    ensures o@ == spec_empty(),
{
    EmptyCombinator(bytes::Fixed::<0>)
}

                

pub enum SpecInstrWithFcRest {
    Variant0(SpecTableInit),
    Variant1(SpecElemDrop),
    Variant2(SpecTableCopy),
    Variant3(SpecTableGrow),
    Variant4(SpecTableSize),
    Variant5(SpecTableFill),
    Variant6(SpecMemoryInit),
    Variant7(SpecDataDrop),
    Variant8(SpecMemoryCopy),
    Variant9(SpecMemoryFill),
    Variant10(SpecEmpty),
}

pub type SpecInstrWithFcRestInner = Either<SpecTableInit, Either<SpecElemDrop, Either<SpecTableCopy, Either<SpecTableGrow, Either<SpecTableSize, Either<SpecTableFill, Either<SpecMemoryInit, Either<SpecDataDrop, Either<SpecMemoryCopy, Either<SpecMemoryFill, SpecEmpty>>>>>>>>>>;



impl SpecFrom<SpecInstrWithFcRest> for SpecInstrWithFcRestInner {
    open spec fn spec_from(m: SpecInstrWithFcRest) -> SpecInstrWithFcRestInner {
        match m {
            SpecInstrWithFcRest::Variant0(m) => Either::Left(m),
            SpecInstrWithFcRest::Variant1(m) => Either::Right(Either::Left(m)),
            SpecInstrWithFcRest::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrWithFcRest::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrWithFcRest::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecInstrWithFcRest::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecInstrWithFcRest::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecInstrWithFcRest::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecInstrWithFcRest::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecInstrWithFcRest::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecInstrWithFcRest::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }

}

impl SpecFrom<SpecInstrWithFcRestInner> for SpecInstrWithFcRest {
    open spec fn spec_from(m: SpecInstrWithFcRestInner) -> SpecInstrWithFcRest {
        match m {
            Either::Left(m) => SpecInstrWithFcRest::Variant0(m),
            Either::Right(Either::Left(m)) => SpecInstrWithFcRest::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrWithFcRest::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrWithFcRest::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecInstrWithFcRest::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecInstrWithFcRest::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecInstrWithFcRest::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecInstrWithFcRest::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecInstrWithFcRest::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecInstrWithFcRest::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => SpecInstrWithFcRest::Variant10(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrWithFcRest<'a> {
    Variant0(TableInit),
    Variant1(ElemDrop),
    Variant2(TableCopy),
    Variant3(TableGrow),
    Variant4(TableSize),
    Variant5(TableFill),
    Variant6(MemoryInit),
    Variant7(DataDrop),
    Variant8(MemoryCopy<'a>),
    Variant9(MemoryFill),
    Variant10(Empty<'a>),
}

pub type InstrWithFcRestInner<'a> = Either<TableInit, Either<ElemDrop, Either<TableCopy, Either<TableGrow, Either<TableSize, Either<TableFill, Either<MemoryInit, Either<DataDrop, Either<MemoryCopy<'a>, Either<MemoryFill, Empty<'a>>>>>>>>>>>;


impl<'a> View for InstrWithFcRest<'a> {
    type V = SpecInstrWithFcRest;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrWithFcRest::Variant0(m) => SpecInstrWithFcRest::Variant0(m@),
            InstrWithFcRest::Variant1(m) => SpecInstrWithFcRest::Variant1(m@),
            InstrWithFcRest::Variant2(m) => SpecInstrWithFcRest::Variant2(m@),
            InstrWithFcRest::Variant3(m) => SpecInstrWithFcRest::Variant3(m@),
            InstrWithFcRest::Variant4(m) => SpecInstrWithFcRest::Variant4(m@),
            InstrWithFcRest::Variant5(m) => SpecInstrWithFcRest::Variant5(m@),
            InstrWithFcRest::Variant6(m) => SpecInstrWithFcRest::Variant6(m@),
            InstrWithFcRest::Variant7(m) => SpecInstrWithFcRest::Variant7(m@),
            InstrWithFcRest::Variant8(m) => SpecInstrWithFcRest::Variant8(m@),
            InstrWithFcRest::Variant9(m) => SpecInstrWithFcRest::Variant9(m@),
            InstrWithFcRest::Variant10(m) => SpecInstrWithFcRest::Variant10(m@),
        }
    }
}


impl<'a> From<InstrWithFcRest<'a>> for InstrWithFcRestInner<'a> {
    fn ex_from(m: InstrWithFcRest<'a>) -> InstrWithFcRestInner<'a> {
        match m {
            InstrWithFcRest::Variant0(m) => Either::Left(m),
            InstrWithFcRest::Variant1(m) => Either::Right(Either::Left(m)),
            InstrWithFcRest::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrWithFcRest::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrWithFcRest::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            InstrWithFcRest::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            InstrWithFcRest::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            InstrWithFcRest::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            InstrWithFcRest::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            InstrWithFcRest::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            InstrWithFcRest::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }

}

impl<'a> From<InstrWithFcRestInner<'a>> for InstrWithFcRest<'a> {
    fn ex_from(m: InstrWithFcRestInner<'a>) -> InstrWithFcRest<'a> {
        match m {
            Either::Left(m) => InstrWithFcRest::Variant0(m),
            Either::Right(Either::Left(m)) => InstrWithFcRest::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrWithFcRest::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrWithFcRest::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => InstrWithFcRest::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => InstrWithFcRest::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => InstrWithFcRest::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => InstrWithFcRest::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => InstrWithFcRest::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => InstrWithFcRest::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => InstrWithFcRest::Variant10(m),
        }
    }
    
}


pub struct InstrWithFcRestMapper<'a>(PhantomData<&'a ()>);
impl<'a> InstrWithFcRestMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        InstrWithFcRestMapper(PhantomData)
    }
    pub fn new() -> Self {
        InstrWithFcRestMapper(PhantomData)
    }
}
impl View for InstrWithFcRestMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrWithFcRestMapper<'_> {
    type Src = SpecInstrWithFcRestInner;
    type Dst = SpecInstrWithFcRest;
}
impl SpecIsoProof for InstrWithFcRestMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for InstrWithFcRestMapper<'a> {
    type Src = InstrWithFcRestInner<'a>;
    type Dst = InstrWithFcRest<'a>;
}


pub struct SpecInstrWithFcRestCombinator(SpecInstrWithFcRestCombinatorAlias);

impl SpecCombinator for SpecInstrWithFcRestCombinator {
    type Type = SpecInstrWithFcRest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrWithFcRestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrWithFcRestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecInstrWithFcRestCombinatorAlias = Mapped<Choice<Cond<SpecTableInitCombinator>, Choice<Cond<SpecElemDropCombinator>, Choice<Cond<SpecTableCopyCombinator>, Choice<Cond<SpecTableGrowCombinator>, Choice<Cond<SpecTableSizeCombinator>, Choice<Cond<SpecTableFillCombinator>, Choice<Cond<SpecMemoryInitCombinator>, Choice<Cond<SpecDataDropCombinator>, Choice<Cond<SpecMemoryCopyCombinator>, Choice<Cond<SpecMemoryFillCombinator>, Cond<SpecEmptyCombinator>>>>>>>>>>>, InstrWithFcRestMapper<'static>>;

pub struct InstrWithFcRestCombinator<'a>(InstrWithFcRestCombinatorAlias<'a>);

impl<'a> View for InstrWithFcRestCombinator<'a> {
    type V = SpecInstrWithFcRestCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrWithFcRestCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for InstrWithFcRestCombinator<'a> {
    type Type = InstrWithFcRest<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type InstrWithFcRestCombinatorAlias<'a> = Mapped<Choice<Cond<TableInitCombinator>, Choice<Cond<ElemDropCombinator>, Choice<Cond<TableCopyCombinator>, Choice<Cond<TableGrowCombinator>, Choice<Cond<TableSizeCombinator>, Choice<Cond<TableFillCombinator>, Choice<Cond<MemoryInitCombinator>, Choice<Cond<DataDropCombinator>, Choice<Cond<MemoryCopyCombinator<'a>>, Choice<Cond<MemoryFillCombinator>, Cond<EmptyCombinator>>>>>>>>>>>, InstrWithFcRestMapper<'a>>;


pub closed spec fn spec_instr_with_fc_rest(tag: u64) -> SpecInstrWithFcRestCombinator {
    SpecInstrWithFcRestCombinator(Mapped { inner: Choice(Cond { cond: tag == 12, inner: spec_table_init() }, Choice(Cond { cond: tag == 13, inner: spec_elem_drop() }, Choice(Cond { cond: tag == 14, inner: spec_table_copy() }, Choice(Cond { cond: tag == 15, inner: spec_table_grow() }, Choice(Cond { cond: tag == 16, inner: spec_table_size() }, Choice(Cond { cond: tag == 17, inner: spec_table_fill() }, Choice(Cond { cond: tag == 8, inner: spec_memory_init() }, Choice(Cond { cond: tag == 9, inner: spec_data_drop() }, Choice(Cond { cond: tag == 10, inner: spec_memory_copy() }, Choice(Cond { cond: tag == 11, inner: spec_memory_fill() }, Cond { cond: !(tag == 12 || tag == 13 || tag == 14 || tag == 15 || tag == 16 || tag == 17 || tag == 8 || tag == 9 || tag == 10 || tag == 11), inner: spec_empty() })))))))))), mapper: InstrWithFcRestMapper::spec_new() })
}

pub fn instr_with_fc_rest<'a>(tag: u64) -> (o: InstrWithFcRestCombinator<'a>)
    ensures o@ == spec_instr_with_fc_rest(tag@),
{
    InstrWithFcRestCombinator(Mapped { inner: Choice::new(Cond { cond: tag == 12, inner: table_init() }, Choice::new(Cond { cond: tag == 13, inner: elem_drop() }, Choice::new(Cond { cond: tag == 14, inner: table_copy() }, Choice::new(Cond { cond: tag == 15, inner: table_grow() }, Choice::new(Cond { cond: tag == 16, inner: table_size() }, Choice::new(Cond { cond: tag == 17, inner: table_fill() }, Choice::new(Cond { cond: tag == 8, inner: memory_init() }, Choice::new(Cond { cond: tag == 9, inner: data_drop() }, Choice::new(Cond { cond: tag == 10, inner: memory_copy() }, Choice::new(Cond { cond: tag == 11, inner: memory_fill() }, Cond { cond: !(tag == 12 || tag == 13 || tag == 14 || tag == 15 || tag == 16 || tag == 17 || tag == 8 || tag == 9 || tag == 10 || tag == 11), inner: empty() })))))))))), mapper: InstrWithFcRestMapper::new() })
}

pub type SpecInstrBytecode = u8;
pub type InstrBytecode = u8;


pub struct SpecInstrBytecodeCombinator(SpecInstrBytecodeCombinatorAlias);

impl SpecCombinator for SpecInstrBytecodeCombinator {
    type Type = SpecInstrBytecode;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrBytecodeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrBytecodeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecInstrBytecodeCombinatorAlias = U8;

pub struct InstrBytecodeCombinator(InstrBytecodeCombinatorAlias);

impl View for InstrBytecodeCombinator {
    type V = SpecInstrBytecodeCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrBytecodeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for InstrBytecodeCombinator {
    type Type = InstrBytecode;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type InstrBytecodeCombinatorAlias = U8;


pub closed spec fn spec_instr_bytecode() -> SpecInstrBytecodeCombinator {
    SpecInstrBytecodeCombinator(U8)
}

                
pub fn instr_bytecode() -> (o: InstrBytecodeCombinator)
    ensures o@ == spec_instr_bytecode(),
{
    InstrBytecodeCombinator(U8)
}

                
pub type SpecLocalidx = u64;
pub type Localidx = u64;


pub struct SpecLocalidxCombinator(SpecLocalidxCombinatorAlias);

impl SpecCombinator for SpecLocalidxCombinator {
    type Type = SpecLocalidx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLocalidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLocalidxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecLocalidxCombinatorAlias = UnsignedLEB128;

pub struct LocalidxCombinator(LocalidxCombinatorAlias);

impl View for LocalidxCombinator {
    type V = SpecLocalidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecLocalidxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for LocalidxCombinator {
    type Type = Localidx;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type LocalidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_localidx() -> SpecLocalidxCombinator {
    SpecLocalidxCombinator(UnsignedLEB128)
}

                
pub fn localidx() -> (o: LocalidxCombinator)
    ensures o@ == spec_localidx(),
{
    LocalidxCombinator(UnsignedLEB128)
}

                

pub struct SpecMemarg {
    pub align: u64,
    pub offset: u64,
}

pub type SpecMemargInner = (u64, u64);
impl SpecFrom<SpecMemarg> for SpecMemargInner {
    open spec fn spec_from(m: SpecMemarg) -> SpecMemargInner {
        (m.align, m.offset)
    }
}
impl SpecFrom<SpecMemargInner> for SpecMemarg {
    open spec fn spec_from(m: SpecMemargInner) -> SpecMemarg {
        let (align, offset) = m;
        SpecMemarg { align, offset }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Memarg {
    pub align: u64,
    pub offset: u64,
}

impl View for Memarg {
    type V = SpecMemarg;

    open spec fn view(&self) -> Self::V {
        SpecMemarg {
            align: self.align@,
            offset: self.offset@,
        }
    }
}
pub type MemargInner = (u64, u64);
impl From<Memarg> for MemargInner {
    fn ex_from(m: Memarg) -> MemargInner {
        (m.align, m.offset)
    }
}
impl From<MemargInner> for Memarg {
    fn ex_from(m: MemargInner) -> Memarg {
        let (align, offset) = m;
        Memarg { align, offset }
    }
}

pub struct MemargMapper;
impl MemargMapper {
    pub closed spec fn spec_new() -> Self {
        MemargMapper
    }
    pub fn new() -> Self {
        MemargMapper
    }
}
impl View for MemargMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemargMapper {
    type Src = SpecMemargInner;
    type Dst = SpecMemarg;
}
impl SpecIsoProof for MemargMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for MemargMapper {
    type Src = MemargInner;
    type Dst = Memarg;
}

pub struct SpecMemargCombinator(SpecMemargCombinatorAlias);

impl SpecCombinator for SpecMemargCombinator {
    type Type = SpecMemarg;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemargCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemargCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMemargCombinatorAlias = Mapped<(UnsignedLEB128, UnsignedLEB128), MemargMapper>;

pub struct MemargCombinator(MemargCombinatorAlias);

impl View for MemargCombinator {
    type V = SpecMemargCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemargCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MemargCombinator {
    type Type = Memarg;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MemargCombinatorAlias = Mapped<(UnsignedLEB128, UnsignedLEB128), MemargMapper>;


pub closed spec fn spec_memarg() -> SpecMemargCombinator {
    SpecMemargCombinator(
    Mapped {
        inner: (UnsignedLEB128, UnsignedLEB128),
        mapper: MemargMapper::spec_new(),
    })
}

                
pub fn memarg() -> (o: MemargCombinator)
    ensures o@ == spec_memarg(),
{
    MemargCombinator(
    Mapped {
        inner: (UnsignedLEB128, UnsignedLEB128),
        mapper: MemargMapper::new(),
    })
}

                
pub type SpecLabelidx = u64;
pub type Labelidx = u64;


pub struct SpecLabelidxCombinator(SpecLabelidxCombinatorAlias);

impl SpecCombinator for SpecLabelidxCombinator {
    type Type = SpecLabelidx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLabelidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLabelidxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecLabelidxCombinatorAlias = UnsignedLEB128;

pub struct LabelidxCombinator(LabelidxCombinatorAlias);

impl View for LabelidxCombinator {
    type V = SpecLabelidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecLabelidxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for LabelidxCombinator {
    type Type = Labelidx;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type LabelidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_labelidx() -> SpecLabelidxCombinator {
    SpecLabelidxCombinator(UnsignedLEB128)
}

                
pub fn labelidx() -> (o: LabelidxCombinator)
    ensures o@ == spec_labelidx(),
{
    LabelidxCombinator(UnsignedLEB128)
}

                

pub struct SpecEmptyBlock {
    pub tag: u8,
    pub body: SpecEmpty,
}

pub type SpecEmptyBlockInner = (u8, SpecEmpty);
impl SpecFrom<SpecEmptyBlock> for SpecEmptyBlockInner {
    open spec fn spec_from(m: SpecEmptyBlock) -> SpecEmptyBlockInner {
        (m.tag, m.body)
    }
}
impl SpecFrom<SpecEmptyBlockInner> for SpecEmptyBlock {
    open spec fn spec_from(m: SpecEmptyBlockInner) -> SpecEmptyBlock {
        let (tag, body) = m;
        SpecEmptyBlock { tag, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EmptyBlock<'a> {
    pub tag: u8,
    pub body: Empty<'a>,
}

impl View for EmptyBlock<'_> {
    type V = SpecEmptyBlock;

    open spec fn view(&self) -> Self::V {
        SpecEmptyBlock {
            tag: self.tag@,
            body: self.body@,
        }
    }
}
pub type EmptyBlockInner<'a> = (u8, Empty<'a>);
impl<'a> From<EmptyBlock<'a>> for EmptyBlockInner<'a> {
    fn ex_from(m: EmptyBlock) -> EmptyBlockInner {
        (m.tag, m.body)
    }
}
impl<'a> From<EmptyBlockInner<'a>> for EmptyBlock<'a> {
    fn ex_from(m: EmptyBlockInner) -> EmptyBlock {
        let (tag, body) = m;
        EmptyBlock { tag, body }
    }
}

pub struct EmptyBlockMapper<'a>(PhantomData<&'a ()>);
impl<'a> EmptyBlockMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        EmptyBlockMapper(PhantomData)
    }
    pub fn new() -> Self {
        EmptyBlockMapper(PhantomData)
    }
}
impl View for EmptyBlockMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EmptyBlockMapper<'_> {
    type Src = SpecEmptyBlockInner;
    type Dst = SpecEmptyBlock;
}
impl SpecIsoProof for EmptyBlockMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for EmptyBlockMapper<'a> {
    type Src = EmptyBlockInner<'a>;
    type Dst = EmptyBlock<'a>;
}

pub struct SpecEmptyBlockCombinator(SpecEmptyBlockCombinatorAlias);

impl SpecCombinator for SpecEmptyBlockCombinator {
    type Type = SpecEmptyBlock;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEmptyBlockCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEmptyBlockCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecEmptyBlockCombinatorAlias = Mapped<(Refined<U8, Predicate16713707613369419146>, SpecEmptyCombinator), EmptyBlockMapper<'static>>;
pub struct Predicate16713707613369419146;
impl View for Predicate16713707613369419146 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate16713707613369419146 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i == 64)
    }
}
impl SpecPred for Predicate16713707613369419146 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i == 64)
    }
}

pub struct EmptyBlockCombinator<'a>(EmptyBlockCombinatorAlias<'a>);

impl<'a> View for EmptyBlockCombinator<'a> {
    type V = SpecEmptyBlockCombinator;
    closed spec fn view(&self) -> Self::V { SpecEmptyBlockCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EmptyBlockCombinator<'a> {
    type Type = EmptyBlock<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EmptyBlockCombinatorAlias<'a> = Mapped<(Refined<U8, Predicate16713707613369419146>, EmptyCombinator), EmptyBlockMapper<'a>>;


pub closed spec fn spec_empty_block() -> SpecEmptyBlockCombinator {
    SpecEmptyBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate16713707613369419146 }, spec_empty()),
        mapper: EmptyBlockMapper::spec_new(),
    })
}

                
pub fn empty_block<'a>() -> (o: EmptyBlockCombinator<'a>)
    ensures o@ == spec_empty_block(),
{
    EmptyBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate16713707613369419146 }, empty()),
        mapper: EmptyBlockMapper::new(),
    })
}

                

pub struct SpecValtypeBlock {
    pub tag: u8,
    pub body: SpecEmpty,
}

pub type SpecValtypeBlockInner = (u8, SpecEmpty);
impl SpecFrom<SpecValtypeBlock> for SpecValtypeBlockInner {
    open spec fn spec_from(m: SpecValtypeBlock) -> SpecValtypeBlockInner {
        (m.tag, m.body)
    }
}
impl SpecFrom<SpecValtypeBlockInner> for SpecValtypeBlock {
    open spec fn spec_from(m: SpecValtypeBlockInner) -> SpecValtypeBlock {
        let (tag, body) = m;
        SpecValtypeBlock { tag, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ValtypeBlock<'a> {
    pub tag: u8,
    pub body: Empty<'a>,
}

impl View for ValtypeBlock<'_> {
    type V = SpecValtypeBlock;

    open spec fn view(&self) -> Self::V {
        SpecValtypeBlock {
            tag: self.tag@,
            body: self.body@,
        }
    }
}
pub type ValtypeBlockInner<'a> = (u8, Empty<'a>);
impl<'a> From<ValtypeBlock<'a>> for ValtypeBlockInner<'a> {
    fn ex_from(m: ValtypeBlock) -> ValtypeBlockInner {
        (m.tag, m.body)
    }
}
impl<'a> From<ValtypeBlockInner<'a>> for ValtypeBlock<'a> {
    fn ex_from(m: ValtypeBlockInner) -> ValtypeBlock {
        let (tag, body) = m;
        ValtypeBlock { tag, body }
    }
}

pub struct ValtypeBlockMapper<'a>(PhantomData<&'a ()>);
impl<'a> ValtypeBlockMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ValtypeBlockMapper(PhantomData)
    }
    pub fn new() -> Self {
        ValtypeBlockMapper(PhantomData)
    }
}
impl View for ValtypeBlockMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ValtypeBlockMapper<'_> {
    type Src = SpecValtypeBlockInner;
    type Dst = SpecValtypeBlock;
}
impl SpecIsoProof for ValtypeBlockMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ValtypeBlockMapper<'a> {
    type Src = ValtypeBlockInner<'a>;
    type Dst = ValtypeBlock<'a>;
}

pub struct SpecValtypeBlockCombinator(SpecValtypeBlockCombinatorAlias);

impl SpecCombinator for SpecValtypeBlockCombinator {
    type Type = SpecValtypeBlock;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecValtypeBlockCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecValtypeBlockCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecValtypeBlockCombinatorAlias = Mapped<(Refined<U8, Predicate17051755724411564727>, SpecEmptyCombinator), ValtypeBlockMapper<'static>>;
pub struct Predicate17051755724411564727;
impl View for Predicate17051755724411564727 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate17051755724411564727 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i == 123) || (i == 124) || (i == 125) || (i == 126) || (i == 127) || (i == 111) || (i == 112)
    }
}
impl SpecPred for Predicate17051755724411564727 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i == 123) || (i == 124) || (i == 125) || (i == 126) || (i == 127) || (i == 111) || (i == 112)
    }
}

pub struct ValtypeBlockCombinator<'a>(ValtypeBlockCombinatorAlias<'a>);

impl<'a> View for ValtypeBlockCombinator<'a> {
    type V = SpecValtypeBlockCombinator;
    closed spec fn view(&self) -> Self::V { SpecValtypeBlockCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ValtypeBlockCombinator<'a> {
    type Type = ValtypeBlock<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ValtypeBlockCombinatorAlias<'a> = Mapped<(Refined<U8, Predicate17051755724411564727>, EmptyCombinator), ValtypeBlockMapper<'a>>;


pub closed spec fn spec_valtype_block() -> SpecValtypeBlockCombinator {
    SpecValtypeBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate17051755724411564727 }, spec_empty()),
        mapper: ValtypeBlockMapper::spec_new(),
    })
}

                
pub fn valtype_block<'a>() -> (o: ValtypeBlockCombinator<'a>)
    ensures o@ == spec_valtype_block(),
{
    ValtypeBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate17051755724411564727 }, empty()),
        mapper: ValtypeBlockMapper::new(),
    })
}

                

pub struct SpecTypeidxBlock {
    pub tag: u8,
    pub body: u64,
}

pub type SpecTypeidxBlockInner = (u8, u64);
impl SpecFrom<SpecTypeidxBlock> for SpecTypeidxBlockInner {
    open spec fn spec_from(m: SpecTypeidxBlock) -> SpecTypeidxBlockInner {
        (m.tag, m.body)
    }
}
impl SpecFrom<SpecTypeidxBlockInner> for SpecTypeidxBlock {
    open spec fn spec_from(m: SpecTypeidxBlockInner) -> SpecTypeidxBlock {
        let (tag, body) = m;
        SpecTypeidxBlock { tag, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TypeidxBlock {
    pub tag: u8,
    pub body: u64,
}

impl View for TypeidxBlock {
    type V = SpecTypeidxBlock;

    open spec fn view(&self) -> Self::V {
        SpecTypeidxBlock {
            tag: self.tag@,
            body: self.body@,
        }
    }
}
pub type TypeidxBlockInner = (u8, u64);
impl From<TypeidxBlock> for TypeidxBlockInner {
    fn ex_from(m: TypeidxBlock) -> TypeidxBlockInner {
        (m.tag, m.body)
    }
}
impl From<TypeidxBlockInner> for TypeidxBlock {
    fn ex_from(m: TypeidxBlockInner) -> TypeidxBlock {
        let (tag, body) = m;
        TypeidxBlock { tag, body }
    }
}

pub struct TypeidxBlockMapper;
impl TypeidxBlockMapper {
    pub closed spec fn spec_new() -> Self {
        TypeidxBlockMapper
    }
    pub fn new() -> Self {
        TypeidxBlockMapper
    }
}
impl View for TypeidxBlockMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TypeidxBlockMapper {
    type Src = SpecTypeidxBlockInner;
    type Dst = SpecTypeidxBlock;
}
impl SpecIsoProof for TypeidxBlockMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for TypeidxBlockMapper {
    type Src = TypeidxBlockInner;
    type Dst = TypeidxBlock;
}

pub struct SpecTypeidxBlockCombinator(SpecTypeidxBlockCombinatorAlias);

impl SpecCombinator for SpecTypeidxBlockCombinator {
    type Type = SpecTypeidxBlock;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTypeidxBlockCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTypeidxBlockCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTypeidxBlockCombinatorAlias = Mapped<(Refined<U8, Predicate2396169508742552609>, UnsignedLEB128), TypeidxBlockMapper>;
pub struct Predicate2396169508742552609;
impl View for Predicate2396169508742552609 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate2396169508742552609 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        !((i == 64) || (i == 123) || (i == 124) || (i == 125) || (i == 126) || (i == 127) || (i == 111) || (i == 112))
    }
}
impl SpecPred for Predicate2396169508742552609 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        !((i == 64) || (i == 123) || (i == 124) || (i == 125) || (i == 126) || (i == 127) || (i == 111) || (i == 112))
    }
}

pub struct TypeidxBlockCombinator(TypeidxBlockCombinatorAlias);

impl View for TypeidxBlockCombinator {
    type V = SpecTypeidxBlockCombinator;
    closed spec fn view(&self) -> Self::V { SpecTypeidxBlockCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TypeidxBlockCombinator {
    type Type = TypeidxBlock;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TypeidxBlockCombinatorAlias = Mapped<(Refined<U8, Predicate2396169508742552609>, UnsignedLEB128), TypeidxBlockMapper>;


pub closed spec fn spec_typeidx_block() -> SpecTypeidxBlockCombinator {
    SpecTypeidxBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate2396169508742552609 }, UnsignedLEB128),
        mapper: TypeidxBlockMapper::spec_new(),
    })
}

                
pub fn typeidx_block() -> (o: TypeidxBlockCombinator)
    ensures o@ == spec_typeidx_block(),
{
    TypeidxBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate2396169508742552609 }, UnsignedLEB128),
        mapper: TypeidxBlockMapper::new(),
    })
}

                

pub enum SpecBlocktype {
    Empty(SpecEmptyBlock),
    ValType(SpecValtypeBlock),
    TypeIdx(SpecTypeidxBlock),
}

pub type SpecBlocktypeInner = Either<SpecEmptyBlock, Either<SpecValtypeBlock, SpecTypeidxBlock>>;



impl SpecFrom<SpecBlocktype> for SpecBlocktypeInner {
    open spec fn spec_from(m: SpecBlocktype) -> SpecBlocktypeInner {
        match m {
            SpecBlocktype::Empty(m) => Either::Left(m),
            SpecBlocktype::ValType(m) => Either::Right(Either::Left(m)),
            SpecBlocktype::TypeIdx(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl SpecFrom<SpecBlocktypeInner> for SpecBlocktype {
    open spec fn spec_from(m: SpecBlocktypeInner) -> SpecBlocktype {
        match m {
            Either::Left(m) => SpecBlocktype::Empty(m),
            Either::Right(Either::Left(m)) => SpecBlocktype::ValType(m),
            Either::Right(Either::Right(m)) => SpecBlocktype::TypeIdx(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Blocktype<'a> {
    Empty(EmptyBlock<'a>),
    ValType(ValtypeBlock<'a>),
    TypeIdx(TypeidxBlock),
}

pub type BlocktypeInner<'a> = Either<EmptyBlock<'a>, Either<ValtypeBlock<'a>, TypeidxBlock>>;


impl<'a> View for Blocktype<'a> {
    type V = SpecBlocktype;
    open spec fn view(&self) -> Self::V {
        match self {
            Blocktype::Empty(m) => SpecBlocktype::Empty(m@),
            Blocktype::ValType(m) => SpecBlocktype::ValType(m@),
            Blocktype::TypeIdx(m) => SpecBlocktype::TypeIdx(m@),
        }
    }
}


impl<'a> From<Blocktype<'a>> for BlocktypeInner<'a> {
    fn ex_from(m: Blocktype<'a>) -> BlocktypeInner<'a> {
        match m {
            Blocktype::Empty(m) => Either::Left(m),
            Blocktype::ValType(m) => Either::Right(Either::Left(m)),
            Blocktype::TypeIdx(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<BlocktypeInner<'a>> for Blocktype<'a> {
    fn ex_from(m: BlocktypeInner<'a>) -> Blocktype<'a> {
        match m {
            Either::Left(m) => Blocktype::Empty(m),
            Either::Right(Either::Left(m)) => Blocktype::ValType(m),
            Either::Right(Either::Right(m)) => Blocktype::TypeIdx(m),
        }
    }
    
}


pub struct BlocktypeMapper<'a>(PhantomData<&'a ()>);
impl<'a> BlocktypeMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        BlocktypeMapper(PhantomData)
    }
    pub fn new() -> Self {
        BlocktypeMapper(PhantomData)
    }
}
impl View for BlocktypeMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for BlocktypeMapper<'_> {
    type Src = SpecBlocktypeInner;
    type Dst = SpecBlocktype;
}
impl SpecIsoProof for BlocktypeMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for BlocktypeMapper<'a> {
    type Src = BlocktypeInner<'a>;
    type Dst = Blocktype<'a>;
}


impl DisjointFrom<SpecEmptyBlockCombinator> for SpecValtypeBlockCombinator {
    closed spec fn disjoint_from(&self, other: &SpecEmptyBlockCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecEmptyBlockCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}

impl DisjointFrom<SpecEmptyBlockCombinator> for SpecTypeidxBlockCombinator {
    closed spec fn disjoint_from(&self, other: &SpecEmptyBlockCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecEmptyBlockCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}

impl DisjointFrom<SpecValtypeBlockCombinator> for SpecTypeidxBlockCombinator {
    closed spec fn disjoint_from(&self, other: &SpecValtypeBlockCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecValtypeBlockCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}
pub struct SpecBlocktypeCombinator(SpecBlocktypeCombinatorAlias);

impl SpecCombinator for SpecBlocktypeCombinator {
    type Type = SpecBlocktype;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecBlocktypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecBlocktypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecBlocktypeCombinatorAlias = Mapped<Choice<SpecEmptyBlockCombinator, Choice<SpecValtypeBlockCombinator, SpecTypeidxBlockCombinator>>, BlocktypeMapper<'static>>;

pub struct BlocktypeCombinator<'a>(BlocktypeCombinatorAlias<'a>);

impl<'a> View for BlocktypeCombinator<'a> {
    type V = SpecBlocktypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecBlocktypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for BlocktypeCombinator<'a> {
    type Type = Blocktype<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type BlocktypeCombinatorAlias<'a> = Mapped<Choice<EmptyBlockCombinator<'a>, Choice<ValtypeBlockCombinator<'a>, TypeidxBlockCombinator>>, BlocktypeMapper<'a>>;


pub closed spec fn spec_blocktype() -> SpecBlocktypeCombinator {
    SpecBlocktypeCombinator(Mapped { inner: Choice(spec_empty_block(), Choice(spec_valtype_block(), spec_typeidx_block())), mapper: BlocktypeMapper::spec_new() })
}

                
pub fn blocktype<'a>() -> (o: BlocktypeCombinator<'a>)
    ensures o@ == spec_blocktype(),
{
    BlocktypeCombinator(Mapped { inner: Choice::new(empty_block(), Choice::new(valtype_block(), typeidx_block())), mapper: BlocktypeMapper::new() })
}

                
pub type SpecFuncidx = u64;
pub type Funcidx = u64;


pub struct SpecFuncidxCombinator(SpecFuncidxCombinatorAlias);

impl SpecCombinator for SpecFuncidxCombinator {
    type Type = SpecFuncidx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFuncidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFuncidxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecFuncidxCombinatorAlias = UnsignedLEB128;

pub struct FuncidxCombinator(FuncidxCombinatorAlias);

impl View for FuncidxCombinator {
    type V = SpecFuncidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecFuncidxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for FuncidxCombinator {
    type Type = Funcidx;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type FuncidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_funcidx() -> SpecFuncidxCombinator {
    SpecFuncidxCombinator(UnsignedLEB128)
}

                
pub fn funcidx() -> (o: FuncidxCombinator)
    ensures o@ == spec_funcidx(),
{
    FuncidxCombinator(UnsignedLEB128)
}

                

pub struct SpecLabelidxVec {
    pub l: u64,
    pub v: Seq<SpecLabelidx>,
}

pub type SpecLabelidxVecInner = (u64, Seq<SpecLabelidx>);
impl SpecFrom<SpecLabelidxVec> for SpecLabelidxVecInner {
    open spec fn spec_from(m: SpecLabelidxVec) -> SpecLabelidxVecInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecLabelidxVecInner> for SpecLabelidxVec {
    open spec fn spec_from(m: SpecLabelidxVecInner) -> SpecLabelidxVec {
        let (l, v) = m;
        SpecLabelidxVec { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct LabelidxVec {
    pub l: u64,
    pub v: RepeatResult<Labelidx>,
}

impl View for LabelidxVec {
    type V = SpecLabelidxVec;

    open spec fn view(&self) -> Self::V {
        SpecLabelidxVec {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type LabelidxVecInner = (u64, RepeatResult<Labelidx>);
impl From<LabelidxVec> for LabelidxVecInner {
    fn ex_from(m: LabelidxVec) -> LabelidxVecInner {
        (m.l, m.v)
    }
}
impl From<LabelidxVecInner> for LabelidxVec {
    fn ex_from(m: LabelidxVecInner) -> LabelidxVec {
        let (l, v) = m;
        LabelidxVec { l, v }
    }
}

pub struct LabelidxVecMapper;
impl LabelidxVecMapper {
    pub closed spec fn spec_new() -> Self {
        LabelidxVecMapper
    }
    pub fn new() -> Self {
        LabelidxVecMapper
    }
}
impl View for LabelidxVecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LabelidxVecMapper {
    type Src = SpecLabelidxVecInner;
    type Dst = SpecLabelidxVec;
}
impl SpecIsoProof for LabelidxVecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for LabelidxVecMapper {
    type Src = LabelidxVecInner;
    type Dst = LabelidxVec;
}

pub struct SpecLabelidxVecCombinator(SpecLabelidxVecCombinatorAlias);

impl SpecCombinator for SpecLabelidxVecCombinator {
    type Type = SpecLabelidxVec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLabelidxVecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLabelidxVecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecLabelidxVecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecLabelidxCombinator>>, LabelidxVecMapper>;

pub struct LabelidxVecCombinator<'a>(LabelidxVecCombinatorAlias<'a>);

impl<'a> View for LabelidxVecCombinator<'a> {
    type V = SpecLabelidxVecCombinator;
    closed spec fn view(&self) -> Self::V { SpecLabelidxVecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for LabelidxVecCombinator<'a> {
    type Type = LabelidxVec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type LabelidxVecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<LabelidxCombinator>, LabelidxVecCont0<'a>>, LabelidxVecMapper>;


pub closed spec fn spec_labelidx_vec() -> SpecLabelidxVecCombinator {
    SpecLabelidxVecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_labelidx_vec_cont0(deps) },
        mapper: LabelidxVecMapper::spec_new(),
    })
}

pub open spec fn spec_labelidx_vec_cont0(deps: u64) -> RepeatN<SpecLabelidxCombinator> {
    let l = deps;
    RepeatN(spec_labelidx(), l.spec_into())
}
                
pub fn labelidx_vec<'a>() -> (o: LabelidxVecCombinator<'a>)
    ensures o@ == spec_labelidx_vec(),
{
    LabelidxVecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: LabelidxVecCont0::new(), spec_snd: Ghost(|deps| spec_labelidx_vec_cont0(deps)) },
        mapper: LabelidxVecMapper::new(),
    })
}

pub struct LabelidxVecCont0<'a>(PhantomData<&'a ()>);
impl<'a> LabelidxVecCont0<'a> {
    pub fn new() -> Self {
        LabelidxVecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for LabelidxVecCont0<'a> {
    type Output = RepeatN<LabelidxCombinator>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_labelidx_vec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(labelidx(), l.ex_into())
    }
}
                

pub struct SpecBrTable {
    pub l: SpecLabelidxVec,
    pub l_n: SpecLabelidx,
}

pub type SpecBrTableInner = (SpecLabelidxVec, SpecLabelidx);
impl SpecFrom<SpecBrTable> for SpecBrTableInner {
    open spec fn spec_from(m: SpecBrTable) -> SpecBrTableInner {
        (m.l, m.l_n)
    }
}
impl SpecFrom<SpecBrTableInner> for SpecBrTable {
    open spec fn spec_from(m: SpecBrTableInner) -> SpecBrTable {
        let (l, l_n) = m;
        SpecBrTable { l, l_n }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct BrTable {
    pub l: LabelidxVec,
    pub l_n: Labelidx,
}

impl View for BrTable {
    type V = SpecBrTable;

    open spec fn view(&self) -> Self::V {
        SpecBrTable {
            l: self.l@,
            l_n: self.l_n@,
        }
    }
}
pub type BrTableInner = (LabelidxVec, Labelidx);
impl From<BrTable> for BrTableInner {
    fn ex_from(m: BrTable) -> BrTableInner {
        (m.l, m.l_n)
    }
}
impl From<BrTableInner> for BrTable {
    fn ex_from(m: BrTableInner) -> BrTable {
        let (l, l_n) = m;
        BrTable { l, l_n }
    }
}

pub struct BrTableMapper;
impl BrTableMapper {
    pub closed spec fn spec_new() -> Self {
        BrTableMapper
    }
    pub fn new() -> Self {
        BrTableMapper
    }
}
impl View for BrTableMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for BrTableMapper {
    type Src = SpecBrTableInner;
    type Dst = SpecBrTable;
}
impl SpecIsoProof for BrTableMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for BrTableMapper {
    type Src = BrTableInner;
    type Dst = BrTable;
}

pub struct SpecBrTableCombinator(SpecBrTableCombinatorAlias);

impl SpecCombinator for SpecBrTableCombinator {
    type Type = SpecBrTable;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecBrTableCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecBrTableCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecBrTableCombinatorAlias = Mapped<(SpecLabelidxVecCombinator, SpecLabelidxCombinator), BrTableMapper>;

pub struct BrTableCombinator<'a>(BrTableCombinatorAlias<'a>);

impl<'a> View for BrTableCombinator<'a> {
    type V = SpecBrTableCombinator;
    closed spec fn view(&self) -> Self::V { SpecBrTableCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for BrTableCombinator<'a> {
    type Type = BrTable;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type BrTableCombinatorAlias<'a> = Mapped<(LabelidxVecCombinator<'a>, LabelidxCombinator), BrTableMapper>;


pub closed spec fn spec_br_table() -> SpecBrTableCombinator {
    SpecBrTableCombinator(
    Mapped {
        inner: (spec_labelidx_vec(), spec_labelidx()),
        mapper: BrTableMapper::spec_new(),
    })
}

                
pub fn br_table<'a>() -> (o: BrTableCombinator<'a>)
    ensures o@ == spec_br_table(),
{
    BrTableCombinator(
    Mapped {
        inner: (labelidx_vec(), labelidx()),
        mapper: BrTableMapper::new(),
    })
}

                
pub type SpecTypeidx = u64;
pub type Typeidx = u64;


pub struct SpecTypeidxCombinator(SpecTypeidxCombinatorAlias);

impl SpecCombinator for SpecTypeidxCombinator {
    type Type = SpecTypeidx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTypeidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTypeidxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTypeidxCombinatorAlias = UnsignedLEB128;

pub struct TypeidxCombinator(TypeidxCombinatorAlias);

impl View for TypeidxCombinator {
    type V = SpecTypeidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecTypeidxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TypeidxCombinator {
    type Type = Typeidx;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TypeidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_typeidx() -> SpecTypeidxCombinator {
    SpecTypeidxCombinator(UnsignedLEB128)
}

                
pub fn typeidx() -> (o: TypeidxCombinator)
    ensures o@ == spec_typeidx(),
{
    TypeidxCombinator(UnsignedLEB128)
}

                

pub struct SpecCallIndirect {
    pub y: SpecTypeidx,
    pub x: SpecTableidx,
}

pub type SpecCallIndirectInner = (SpecTypeidx, SpecTableidx);
impl SpecFrom<SpecCallIndirect> for SpecCallIndirectInner {
    open spec fn spec_from(m: SpecCallIndirect) -> SpecCallIndirectInner {
        (m.y, m.x)
    }
}
impl SpecFrom<SpecCallIndirectInner> for SpecCallIndirect {
    open spec fn spec_from(m: SpecCallIndirectInner) -> SpecCallIndirect {
        let (y, x) = m;
        SpecCallIndirect { y, x }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CallIndirect {
    pub y: Typeidx,
    pub x: Tableidx,
}

impl View for CallIndirect {
    type V = SpecCallIndirect;

    open spec fn view(&self) -> Self::V {
        SpecCallIndirect {
            y: self.y@,
            x: self.x@,
        }
    }
}
pub type CallIndirectInner = (Typeidx, Tableidx);
impl From<CallIndirect> for CallIndirectInner {
    fn ex_from(m: CallIndirect) -> CallIndirectInner {
        (m.y, m.x)
    }
}
impl From<CallIndirectInner> for CallIndirect {
    fn ex_from(m: CallIndirectInner) -> CallIndirect {
        let (y, x) = m;
        CallIndirect { y, x }
    }
}

pub struct CallIndirectMapper;
impl CallIndirectMapper {
    pub closed spec fn spec_new() -> Self {
        CallIndirectMapper
    }
    pub fn new() -> Self {
        CallIndirectMapper
    }
}
impl View for CallIndirectMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CallIndirectMapper {
    type Src = SpecCallIndirectInner;
    type Dst = SpecCallIndirect;
}
impl SpecIsoProof for CallIndirectMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for CallIndirectMapper {
    type Src = CallIndirectInner;
    type Dst = CallIndirect;
}

pub struct SpecCallIndirectCombinator(SpecCallIndirectCombinatorAlias);

impl SpecCombinator for SpecCallIndirectCombinator {
    type Type = SpecCallIndirect;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCallIndirectCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCallIndirectCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecCallIndirectCombinatorAlias = Mapped<(SpecTypeidxCombinator, SpecTableidxCombinator), CallIndirectMapper>;

pub struct CallIndirectCombinator(CallIndirectCombinatorAlias);

impl View for CallIndirectCombinator {
    type V = SpecCallIndirectCombinator;
    closed spec fn view(&self) -> Self::V { SpecCallIndirectCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CallIndirectCombinator {
    type Type = CallIndirect;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CallIndirectCombinatorAlias = Mapped<(TypeidxCombinator, TableidxCombinator), CallIndirectMapper>;


pub closed spec fn spec_call_indirect() -> SpecCallIndirectCombinator {
    SpecCallIndirectCombinator(
    Mapped {
        inner: (spec_typeidx(), spec_tableidx()),
        mapper: CallIndirectMapper::spec_new(),
    })
}

                
pub fn call_indirect() -> (o: CallIndirectCombinator)
    ensures o@ == spec_call_indirect(),
{
    CallIndirectCombinator(
    Mapped {
        inner: (typeidx(), tableidx()),
        mapper: CallIndirectMapper::new(),
    })
}

                

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum Reftype {
    FuncRef = 112,
ExternRef = 111
}
pub type SpecReftype = Reftype;

pub type ReftypeInner = u8;

impl View for Reftype {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<ReftypeInner> for Reftype {
    type Error = ();

    open spec fn spec_try_from(v: ReftypeInner) -> Result<Reftype, ()> {
        match v {
            112u8 => Ok(Reftype::FuncRef),
            111u8 => Ok(Reftype::ExternRef),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<Reftype> for ReftypeInner {
    type Error = ();

    open spec fn spec_try_from(v: Reftype) -> Result<ReftypeInner, ()> {
        match v {
            Reftype::FuncRef => Ok(112u8),
            Reftype::ExternRef => Ok(111u8),
        }
    }
}

impl TryFrom<ReftypeInner> for Reftype {
    type Error = ();

    fn ex_try_from(v: ReftypeInner) -> Result<Reftype, ()> {
        match v {
            112u8 => Ok(Reftype::FuncRef),
            111u8 => Ok(Reftype::ExternRef),
            _ => Err(()),
        }
    }
}

impl TryFrom<Reftype> for ReftypeInner {
    type Error = ();

    fn ex_try_from(v: Reftype) -> Result<ReftypeInner, ()> {
        match v {
            Reftype::FuncRef => Ok(112u8),
            Reftype::ExternRef => Ok(111u8),
        }
    }
}

pub struct ReftypeMapper;

impl View for ReftypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for ReftypeMapper {
    type Src = ReftypeInner;
    type Dst = Reftype;
}

impl SpecPartialIsoProof for ReftypeMapper {
    proof fn spec_iso(s: Self::Src) { 
        assert(
            Self::spec_apply(s) matches Ok(v) ==> {
            &&& Self::spec_rev_apply(v) is Ok
            &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
        });
    }

    proof fn spec_iso_rev(s: Self::Dst) { 
        assert(
            Self::spec_rev_apply(s) matches Ok(v) ==> {
            &&& Self::spec_apply(v) is Ok
            &&& Self::spec_apply(v) matches Ok(s_) && s == s_
        });
    }
}

impl PartialIso for ReftypeMapper {
    type Src = ReftypeInner;
    type Dst = Reftype;
}


pub struct SpecReftypeCombinator(SpecReftypeCombinatorAlias);

impl SpecCombinator for SpecReftypeCombinator {
    type Type = SpecReftype;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecReftypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecReftypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecReftypeCombinatorAlias = TryMap<U8, ReftypeMapper>;

pub struct ReftypeCombinator(ReftypeCombinatorAlias);

impl View for ReftypeCombinator {
    type V = SpecReftypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecReftypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ReftypeCombinator {
    type Type = Reftype;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ReftypeCombinatorAlias = TryMap<U8, ReftypeMapper>;


pub closed spec fn spec_reftype() -> SpecReftypeCombinator {
    SpecReftypeCombinator(TryMap { inner: U8, mapper: ReftypeMapper })
}

                
pub fn reftype() -> (o: ReftypeCombinator)
    ensures o@ == spec_reftype(),
{
    ReftypeCombinator(TryMap { inner: U8, mapper: ReftypeMapper })
}

                

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum Numtype {
    I32 = 127,
I64 = 126,
F32 = 125,
F64 = 124
}
pub type SpecNumtype = Numtype;

pub type NumtypeInner = u8;

impl View for Numtype {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<NumtypeInner> for Numtype {
    type Error = ();

    open spec fn spec_try_from(v: NumtypeInner) -> Result<Numtype, ()> {
        match v {
            127u8 => Ok(Numtype::I32),
            126u8 => Ok(Numtype::I64),
            125u8 => Ok(Numtype::F32),
            124u8 => Ok(Numtype::F64),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<Numtype> for NumtypeInner {
    type Error = ();

    open spec fn spec_try_from(v: Numtype) -> Result<NumtypeInner, ()> {
        match v {
            Numtype::I32 => Ok(127u8),
            Numtype::I64 => Ok(126u8),
            Numtype::F32 => Ok(125u8),
            Numtype::F64 => Ok(124u8),
        }
    }
}

impl TryFrom<NumtypeInner> for Numtype {
    type Error = ();

    fn ex_try_from(v: NumtypeInner) -> Result<Numtype, ()> {
        match v {
            127u8 => Ok(Numtype::I32),
            126u8 => Ok(Numtype::I64),
            125u8 => Ok(Numtype::F32),
            124u8 => Ok(Numtype::F64),
            _ => Err(()),
        }
    }
}

impl TryFrom<Numtype> for NumtypeInner {
    type Error = ();

    fn ex_try_from(v: Numtype) -> Result<NumtypeInner, ()> {
        match v {
            Numtype::I32 => Ok(127u8),
            Numtype::I64 => Ok(126u8),
            Numtype::F32 => Ok(125u8),
            Numtype::F64 => Ok(124u8),
        }
    }
}

pub struct NumtypeMapper;

impl View for NumtypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for NumtypeMapper {
    type Src = NumtypeInner;
    type Dst = Numtype;
}

impl SpecPartialIsoProof for NumtypeMapper {
    proof fn spec_iso(s: Self::Src) { 
        assert(
            Self::spec_apply(s) matches Ok(v) ==> {
            &&& Self::spec_rev_apply(v) is Ok
            &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
        });
    }

    proof fn spec_iso_rev(s: Self::Dst) { 
        assert(
            Self::spec_rev_apply(s) matches Ok(v) ==> {
            &&& Self::spec_apply(v) is Ok
            &&& Self::spec_apply(v) matches Ok(s_) && s == s_
        });
    }
}

impl PartialIso for NumtypeMapper {
    type Src = NumtypeInner;
    type Dst = Numtype;
}


pub struct SpecNumtypeCombinator(SpecNumtypeCombinatorAlias);

impl SpecCombinator for SpecNumtypeCombinator {
    type Type = SpecNumtype;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNumtypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNumtypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecNumtypeCombinatorAlias = TryMap<U8, NumtypeMapper>;

pub struct NumtypeCombinator(NumtypeCombinatorAlias);

impl View for NumtypeCombinator {
    type V = SpecNumtypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecNumtypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NumtypeCombinator {
    type Type = Numtype;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NumtypeCombinatorAlias = TryMap<U8, NumtypeMapper>;


pub closed spec fn spec_numtype() -> SpecNumtypeCombinator {
    SpecNumtypeCombinator(TryMap { inner: U8, mapper: NumtypeMapper })
}

                
pub fn numtype() -> (o: NumtypeCombinator)
    ensures o@ == spec_numtype(),
{
    NumtypeCombinator(TryMap { inner: U8, mapper: NumtypeMapper })
}

                

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum Vectype {
    V128 = 123
}
pub type SpecVectype = Vectype;

pub type VectypeInner = u8;

impl View for Vectype {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<VectypeInner> for Vectype {
    type Error = ();

    open spec fn spec_try_from(v: VectypeInner) -> Result<Vectype, ()> {
        match v {
            123u8 => Ok(Vectype::V128),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<Vectype> for VectypeInner {
    type Error = ();

    open spec fn spec_try_from(v: Vectype) -> Result<VectypeInner, ()> {
        match v {
            Vectype::V128 => Ok(123u8),
        }
    }
}

impl TryFrom<VectypeInner> for Vectype {
    type Error = ();

    fn ex_try_from(v: VectypeInner) -> Result<Vectype, ()> {
        match v {
            123u8 => Ok(Vectype::V128),
            _ => Err(()),
        }
    }
}

impl TryFrom<Vectype> for VectypeInner {
    type Error = ();

    fn ex_try_from(v: Vectype) -> Result<VectypeInner, ()> {
        match v {
            Vectype::V128 => Ok(123u8),
        }
    }
}

pub struct VectypeMapper;

impl View for VectypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for VectypeMapper {
    type Src = VectypeInner;
    type Dst = Vectype;
}

impl SpecPartialIsoProof for VectypeMapper {
    proof fn spec_iso(s: Self::Src) { 
        assert(
            Self::spec_apply(s) matches Ok(v) ==> {
            &&& Self::spec_rev_apply(v) is Ok
            &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
        });
    }

    proof fn spec_iso_rev(s: Self::Dst) { 
        assert(
            Self::spec_rev_apply(s) matches Ok(v) ==> {
            &&& Self::spec_apply(v) is Ok
            &&& Self::spec_apply(v) matches Ok(s_) && s == s_
        });
    }
}

impl PartialIso for VectypeMapper {
    type Src = VectypeInner;
    type Dst = Vectype;
}


pub struct SpecVectypeCombinator(SpecVectypeCombinatorAlias);

impl SpecCombinator for SpecVectypeCombinator {
    type Type = SpecVectype;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecVectypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecVectypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecVectypeCombinatorAlias = TryMap<U8, VectypeMapper>;

pub struct VectypeCombinator(VectypeCombinatorAlias);

impl View for VectypeCombinator {
    type V = SpecVectypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecVectypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for VectypeCombinator {
    type Type = Vectype;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type VectypeCombinatorAlias = TryMap<U8, VectypeMapper>;


pub closed spec fn spec_vectype() -> SpecVectypeCombinator {
    SpecVectypeCombinator(TryMap { inner: U8, mapper: VectypeMapper })
}

                
pub fn vectype() -> (o: VectypeCombinator)
    ensures o@ == spec_vectype(),
{
    VectypeCombinator(TryMap { inner: U8, mapper: VectypeMapper })
}

                

pub enum SpecValtype {
    NumTy(SpecNumtype),
    VecTy(SpecVectype),
    RefTy(SpecReftype),
}

pub type SpecValtypeInner = Either<SpecNumtype, Either<SpecVectype, SpecReftype>>;



impl SpecFrom<SpecValtype> for SpecValtypeInner {
    open spec fn spec_from(m: SpecValtype) -> SpecValtypeInner {
        match m {
            SpecValtype::NumTy(m) => Either::Left(m),
            SpecValtype::VecTy(m) => Either::Right(Either::Left(m)),
            SpecValtype::RefTy(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl SpecFrom<SpecValtypeInner> for SpecValtype {
    open spec fn spec_from(m: SpecValtypeInner) -> SpecValtype {
        match m {
            Either::Left(m) => SpecValtype::NumTy(m),
            Either::Right(Either::Left(m)) => SpecValtype::VecTy(m),
            Either::Right(Either::Right(m)) => SpecValtype::RefTy(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Valtype {
    NumTy(Numtype),
    VecTy(Vectype),
    RefTy(Reftype),
}

pub type ValtypeInner = Either<Numtype, Either<Vectype, Reftype>>;


impl View for Valtype {
    type V = SpecValtype;
    open spec fn view(&self) -> Self::V {
        match self {
            Valtype::NumTy(m) => SpecValtype::NumTy(m@),
            Valtype::VecTy(m) => SpecValtype::VecTy(m@),
            Valtype::RefTy(m) => SpecValtype::RefTy(m@),
        }
    }
}


impl From<Valtype> for ValtypeInner {
    fn ex_from(m: Valtype) -> ValtypeInner {
        match m {
            Valtype::NumTy(m) => Either::Left(m),
            Valtype::VecTy(m) => Either::Right(Either::Left(m)),
            Valtype::RefTy(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl From<ValtypeInner> for Valtype {
    fn ex_from(m: ValtypeInner) -> Valtype {
        match m {
            Either::Left(m) => Valtype::NumTy(m),
            Either::Right(Either::Left(m)) => Valtype::VecTy(m),
            Either::Right(Either::Right(m)) => Valtype::RefTy(m),
        }
    }
    
}


pub struct ValtypeMapper;
impl ValtypeMapper {
    pub closed spec fn spec_new() -> Self {
        ValtypeMapper
    }
    pub fn new() -> Self {
        ValtypeMapper
    }
}
impl View for ValtypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ValtypeMapper {
    type Src = SpecValtypeInner;
    type Dst = SpecValtype;
}
impl SpecIsoProof for ValtypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ValtypeMapper {
    type Src = ValtypeInner;
    type Dst = Valtype;
}


impl DisjointFrom<SpecNumtypeCombinator> for SpecVectypeCombinator {
    closed spec fn disjoint_from(&self, other: &SpecNumtypeCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecNumtypeCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}

impl DisjointFrom<SpecNumtypeCombinator> for SpecReftypeCombinator {
    closed spec fn disjoint_from(&self, other: &SpecNumtypeCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecNumtypeCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}

impl DisjointFrom<SpecVectypeCombinator> for SpecReftypeCombinator {
    closed spec fn disjoint_from(&self, other: &SpecVectypeCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecVectypeCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}
pub struct SpecValtypeCombinator(SpecValtypeCombinatorAlias);

impl SpecCombinator for SpecValtypeCombinator {
    type Type = SpecValtype;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecValtypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecValtypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecValtypeCombinatorAlias = Mapped<Choice<SpecNumtypeCombinator, Choice<SpecVectypeCombinator, SpecReftypeCombinator>>, ValtypeMapper>;

pub struct ValtypeCombinator(ValtypeCombinatorAlias);

impl View for ValtypeCombinator {
    type V = SpecValtypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecValtypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ValtypeCombinator {
    type Type = Valtype;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ValtypeCombinatorAlias = Mapped<Choice<NumtypeCombinator, Choice<VectypeCombinator, ReftypeCombinator>>, ValtypeMapper>;


pub closed spec fn spec_valtype() -> SpecValtypeCombinator {
    SpecValtypeCombinator(Mapped { inner: Choice(spec_numtype(), Choice(spec_vectype(), spec_reftype())), mapper: ValtypeMapper::spec_new() })
}

                
pub fn valtype() -> (o: ValtypeCombinator)
    ensures o@ == spec_valtype(),
{
    ValtypeCombinator(Mapped { inner: Choice::new(numtype(), Choice::new(vectype(), reftype())), mapper: ValtypeMapper::new() })
}

                

pub struct SpecSelectT {
    pub l: u64,
    pub v: Seq<SpecValtype>,
}

pub type SpecSelectTInner = (u64, Seq<SpecValtype>);
impl SpecFrom<SpecSelectT> for SpecSelectTInner {
    open spec fn spec_from(m: SpecSelectT) -> SpecSelectTInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecSelectTInner> for SpecSelectT {
    open spec fn spec_from(m: SpecSelectTInner) -> SpecSelectT {
        let (l, v) = m;
        SpecSelectT { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SelectT {
    pub l: u64,
    pub v: RepeatResult<Valtype>,
}

impl View for SelectT {
    type V = SpecSelectT;

    open spec fn view(&self) -> Self::V {
        SpecSelectT {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type SelectTInner = (u64, RepeatResult<Valtype>);
impl From<SelectT> for SelectTInner {
    fn ex_from(m: SelectT) -> SelectTInner {
        (m.l, m.v)
    }
}
impl From<SelectTInner> for SelectT {
    fn ex_from(m: SelectTInner) -> SelectT {
        let (l, v) = m;
        SelectT { l, v }
    }
}

pub struct SelectTMapper;
impl SelectTMapper {
    pub closed spec fn spec_new() -> Self {
        SelectTMapper
    }
    pub fn new() -> Self {
        SelectTMapper
    }
}
impl View for SelectTMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SelectTMapper {
    type Src = SpecSelectTInner;
    type Dst = SpecSelectT;
}
impl SpecIsoProof for SelectTMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for SelectTMapper {
    type Src = SelectTInner;
    type Dst = SelectT;
}

pub struct SpecSelectTCombinator(SpecSelectTCombinatorAlias);

impl SpecCombinator for SpecSelectTCombinator {
    type Type = SpecSelectT;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSelectTCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSelectTCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecSelectTCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecValtypeCombinator>>, SelectTMapper>;

pub struct SelectTCombinator<'a>(SelectTCombinatorAlias<'a>);

impl<'a> View for SelectTCombinator<'a> {
    type V = SpecSelectTCombinator;
    closed spec fn view(&self) -> Self::V { SpecSelectTCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SelectTCombinator<'a> {
    type Type = SelectT;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SelectTCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<ValtypeCombinator>, SelectTCont0<'a>>, SelectTMapper>;


pub closed spec fn spec_select_t() -> SpecSelectTCombinator {
    SpecSelectTCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_select_t_cont0(deps) },
        mapper: SelectTMapper::spec_new(),
    })
}

pub open spec fn spec_select_t_cont0(deps: u64) -> RepeatN<SpecValtypeCombinator> {
    let l = deps;
    RepeatN(spec_valtype(), l.spec_into())
}
                
pub fn select_t<'a>() -> (o: SelectTCombinator<'a>)
    ensures o@ == spec_select_t(),
{
    SelectTCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: SelectTCont0::new(), spec_snd: Ghost(|deps| spec_select_t_cont0(deps)) },
        mapper: SelectTMapper::new(),
    })
}

pub struct SelectTCont0<'a>(PhantomData<&'a ()>);
impl<'a> SelectTCont0<'a> {
    pub fn new() -> Self {
        SelectTCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for SelectTCont0<'a> {
    type Output = RepeatN<ValtypeCombinator>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_select_t_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(valtype(), l.ex_into())
    }
}
                
pub type SpecGlobalidx = u64;
pub type Globalidx = u64;


pub struct SpecGlobalidxCombinator(SpecGlobalidxCombinatorAlias);

impl SpecCombinator for SpecGlobalidxCombinator {
    type Type = SpecGlobalidx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGlobalidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecGlobalidxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecGlobalidxCombinatorAlias = UnsignedLEB128;

pub struct GlobalidxCombinator(GlobalidxCombinatorAlias);

impl View for GlobalidxCombinator {
    type V = SpecGlobalidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecGlobalidxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for GlobalidxCombinator {
    type Type = Globalidx;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type GlobalidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_globalidx() -> SpecGlobalidxCombinator {
    SpecGlobalidxCombinator(UnsignedLEB128)
}

                
pub fn globalidx() -> (o: GlobalidxCombinator)
    ensures o@ == spec_globalidx(),
{
    GlobalidxCombinator(UnsignedLEB128)
}

                

pub struct SpecByteZero {
    pub zero: u8,
}

pub type SpecByteZeroInner = u8;
impl SpecFrom<SpecByteZero> for SpecByteZeroInner {
    open spec fn spec_from(m: SpecByteZero) -> SpecByteZeroInner {
        m.zero
    }
}
impl SpecFrom<SpecByteZeroInner> for SpecByteZero {
    open spec fn spec_from(m: SpecByteZeroInner) -> SpecByteZero {
        let zero = m;
        SpecByteZero { zero }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ByteZero {
    pub zero: u8,
}

impl View for ByteZero {
    type V = SpecByteZero;

    open spec fn view(&self) -> Self::V {
        SpecByteZero {
            zero: self.zero@,
        }
    }
}
pub type ByteZeroInner = u8;
impl From<ByteZero> for ByteZeroInner {
    fn ex_from(m: ByteZero) -> ByteZeroInner {
        m.zero
    }
}
impl From<ByteZeroInner> for ByteZero {
    fn ex_from(m: ByteZeroInner) -> ByteZero {
        let zero = m;
        ByteZero { zero }
    }
}

pub struct ByteZeroMapper;
impl ByteZeroMapper {
    pub closed spec fn spec_new() -> Self {
        ByteZeroMapper
    }
    pub fn new() -> Self {
        ByteZeroMapper
    }
}
impl View for ByteZeroMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ByteZeroMapper {
    type Src = SpecByteZeroInner;
    type Dst = SpecByteZero;
}
impl SpecIsoProof for ByteZeroMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ByteZeroMapper {
    type Src = ByteZeroInner;
    type Dst = ByteZero;
}
pub const BYTEZEROZERO_CONST: u8 = 0;

pub struct SpecByteZeroCombinator(SpecByteZeroCombinatorAlias);

impl SpecCombinator for SpecByteZeroCombinator {
    type Type = SpecByteZero;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecByteZeroCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecByteZeroCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecByteZeroCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, ByteZeroMapper>;

pub struct ByteZeroCombinator(ByteZeroCombinatorAlias);

impl View for ByteZeroCombinator {
    type V = SpecByteZeroCombinator;
    closed spec fn view(&self) -> Self::V { SpecByteZeroCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ByteZeroCombinator {
    type Type = ByteZero;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ByteZeroCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, ByteZeroMapper>;


pub closed spec fn spec_byte_zero() -> SpecByteZeroCombinator {
    SpecByteZeroCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(BYTEZEROZERO_CONST) },
        mapper: ByteZeroMapper::spec_new(),
    })
}

                
pub fn byte_zero() -> (o: ByteZeroCombinator)
    ensures o@ == spec_byte_zero(),
{
    ByteZeroCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(BYTEZEROZERO_CONST) },
        mapper: ByteZeroMapper::new(),
    })
}

                
pub type SpecF32 = Seq<u8>;
pub type F32<'a> = &'a [u8];


pub struct SpecF32Combinator(SpecF32CombinatorAlias);

impl SpecCombinator for SpecF32Combinator {
    type Type = SpecF32;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecF32Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecF32CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecF32CombinatorAlias = bytes::Fixed<4>;

pub struct F32Combinator(F32CombinatorAlias);

impl View for F32Combinator {
    type V = SpecF32Combinator;
    closed spec fn view(&self) -> Self::V { SpecF32Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for F32Combinator {
    type Type = F32<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type F32CombinatorAlias = bytes::Fixed<4>;


pub closed spec fn spec_f32() -> SpecF32Combinator {
    SpecF32Combinator(bytes::Fixed::<4>)
}

                
pub fn f32() -> (o: F32Combinator)
    ensures o@ == spec_f32(),
{
    F32Combinator(bytes::Fixed::<4>)
}

                
pub type SpecF64 = Seq<u8>;
pub type F64<'a> = &'a [u8];


pub struct SpecF64Combinator(SpecF64CombinatorAlias);

impl SpecCombinator for SpecF64Combinator {
    type Type = SpecF64;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecF64Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecF64CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecF64CombinatorAlias = bytes::Fixed<8>;

pub struct F64Combinator(F64CombinatorAlias);

impl View for F64Combinator {
    type V = SpecF64Combinator;
    closed spec fn view(&self) -> Self::V { SpecF64Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for F64Combinator {
    type Type = F64<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type F64CombinatorAlias = bytes::Fixed<8>;


pub closed spec fn spec_f64() -> SpecF64Combinator {
    SpecF64Combinator(bytes::Fixed::<8>)
}

                
pub fn f64() -> (o: F64Combinator)
    ensures o@ == spec_f64(),
{
    F64Combinator(bytes::Fixed::<8>)
}

                

pub struct SpecInstrWithFc {
    pub tag: u64,
    pub rest: SpecInstrWithFcRest,
}

pub type SpecInstrWithFcInner = (u64, SpecInstrWithFcRest);
impl SpecFrom<SpecInstrWithFc> for SpecInstrWithFcInner {
    open spec fn spec_from(m: SpecInstrWithFc) -> SpecInstrWithFcInner {
        (m.tag, m.rest)
    }
}
impl SpecFrom<SpecInstrWithFcInner> for SpecInstrWithFc {
    open spec fn spec_from(m: SpecInstrWithFcInner) -> SpecInstrWithFc {
        let (tag, rest) = m;
        SpecInstrWithFc { tag, rest }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct InstrWithFc<'a> {
    pub tag: u64,
    pub rest: InstrWithFcRest<'a>,
}

impl View for InstrWithFc<'_> {
    type V = SpecInstrWithFc;

    open spec fn view(&self) -> Self::V {
        SpecInstrWithFc {
            tag: self.tag@,
            rest: self.rest@,
        }
    }
}
pub type InstrWithFcInner<'a> = (u64, InstrWithFcRest<'a>);
impl<'a> From<InstrWithFc<'a>> for InstrWithFcInner<'a> {
    fn ex_from(m: InstrWithFc) -> InstrWithFcInner {
        (m.tag, m.rest)
    }
}
impl<'a> From<InstrWithFcInner<'a>> for InstrWithFc<'a> {
    fn ex_from(m: InstrWithFcInner) -> InstrWithFc {
        let (tag, rest) = m;
        InstrWithFc { tag, rest }
    }
}

pub struct InstrWithFcMapper<'a>(PhantomData<&'a ()>);
impl<'a> InstrWithFcMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        InstrWithFcMapper(PhantomData)
    }
    pub fn new() -> Self {
        InstrWithFcMapper(PhantomData)
    }
}
impl View for InstrWithFcMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrWithFcMapper<'_> {
    type Src = SpecInstrWithFcInner;
    type Dst = SpecInstrWithFc;
}
impl SpecIsoProof for InstrWithFcMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for InstrWithFcMapper<'a> {
    type Src = InstrWithFcInner<'a>;
    type Dst = InstrWithFc<'a>;
}

pub struct SpecInstrWithFcCombinator(SpecInstrWithFcCombinatorAlias);

impl SpecCombinator for SpecInstrWithFcCombinator {
    type Type = SpecInstrWithFc;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrWithFcCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrWithFcCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecInstrWithFcCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, SpecInstrWithFcRestCombinator>, InstrWithFcMapper<'static>>;

pub struct InstrWithFcCombinator<'a>(InstrWithFcCombinatorAlias<'a>);

impl<'a> View for InstrWithFcCombinator<'a> {
    type V = SpecInstrWithFcCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrWithFcCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for InstrWithFcCombinator<'a> {
    type Type = InstrWithFc<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type InstrWithFcCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, InstrWithFcRestCombinator<'a>, InstrWithFcCont0<'a>>, InstrWithFcMapper<'a>>;


pub closed spec fn spec_instr_with_fc() -> SpecInstrWithFcCombinator {
    SpecInstrWithFcCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_instr_with_fc_cont0(deps) },
        mapper: InstrWithFcMapper::spec_new(),
    })
}

pub open spec fn spec_instr_with_fc_cont0(deps: u64) -> SpecInstrWithFcRestCombinator {
    let tag = deps;
    spec_instr_with_fc_rest(tag)
}
                
pub fn instr_with_fc<'a>() -> (o: InstrWithFcCombinator<'a>)
    ensures o@ == spec_instr_with_fc(),
{
    InstrWithFcCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: InstrWithFcCont0::new(), spec_snd: Ghost(|deps| spec_instr_with_fc_cont0(deps)) },
        mapper: InstrWithFcMapper::new(),
    })
}

pub struct InstrWithFcCont0<'a>(PhantomData<&'a ()>);
impl<'a> InstrWithFcCont0<'a> {
    pub fn new() -> Self {
        InstrWithFcCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for InstrWithFcCont0<'a> {
    type Output = InstrWithFcRestCombinator<'a>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_instr_with_fc_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let tag = *deps;
        instr_with_fc_rest(tag)
    }
}
                
pub type SpecLaneidx = u8;
pub type Laneidx = u8;


pub struct SpecLaneidxCombinator(SpecLaneidxCombinatorAlias);

impl SpecCombinator for SpecLaneidxCombinator {
    type Type = SpecLaneidx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLaneidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLaneidxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecLaneidxCombinatorAlias = U8;

pub struct LaneidxCombinator(LaneidxCombinatorAlias);

impl View for LaneidxCombinator {
    type V = SpecLaneidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecLaneidxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for LaneidxCombinator {
    type Type = Laneidx;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type LaneidxCombinatorAlias = U8;


pub closed spec fn spec_laneidx() -> SpecLaneidxCombinator {
    SpecLaneidxCombinator(U8)
}

                
pub fn laneidx() -> (o: LaneidxCombinator)
    ensures o@ == spec_laneidx(),
{
    LaneidxCombinator(U8)
}

                

pub struct SpecV128Lane {
    pub m: SpecMemarg,
    pub l: SpecLaneidx,
}

pub type SpecV128LaneInner = (SpecMemarg, SpecLaneidx);
impl SpecFrom<SpecV128Lane> for SpecV128LaneInner {
    open spec fn spec_from(m: SpecV128Lane) -> SpecV128LaneInner {
        (m.m, m.l)
    }
}
impl SpecFrom<SpecV128LaneInner> for SpecV128Lane {
    open spec fn spec_from(m: SpecV128LaneInner) -> SpecV128Lane {
        let (m, l) = m;
        SpecV128Lane { m, l }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct V128Lane {
    pub m: Memarg,
    pub l: Laneidx,
}

impl View for V128Lane {
    type V = SpecV128Lane;

    open spec fn view(&self) -> Self::V {
        SpecV128Lane {
            m: self.m@,
            l: self.l@,
        }
    }
}
pub type V128LaneInner = (Memarg, Laneidx);
impl From<V128Lane> for V128LaneInner {
    fn ex_from(m: V128Lane) -> V128LaneInner {
        (m.m, m.l)
    }
}
impl From<V128LaneInner> for V128Lane {
    fn ex_from(m: V128LaneInner) -> V128Lane {
        let (m, l) = m;
        V128Lane { m, l }
    }
}

pub struct V128LaneMapper;
impl V128LaneMapper {
    pub closed spec fn spec_new() -> Self {
        V128LaneMapper
    }
    pub fn new() -> Self {
        V128LaneMapper
    }
}
impl View for V128LaneMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for V128LaneMapper {
    type Src = SpecV128LaneInner;
    type Dst = SpecV128Lane;
}
impl SpecIsoProof for V128LaneMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for V128LaneMapper {
    type Src = V128LaneInner;
    type Dst = V128Lane;
}

pub struct SpecV128LaneCombinator(SpecV128LaneCombinatorAlias);

impl SpecCombinator for SpecV128LaneCombinator {
    type Type = SpecV128Lane;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecV128LaneCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecV128LaneCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecV128LaneCombinatorAlias = Mapped<(SpecMemargCombinator, SpecLaneidxCombinator), V128LaneMapper>;

pub struct V128LaneCombinator(V128LaneCombinatorAlias);

impl View for V128LaneCombinator {
    type V = SpecV128LaneCombinator;
    closed spec fn view(&self) -> Self::V { SpecV128LaneCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for V128LaneCombinator {
    type Type = V128Lane;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type V128LaneCombinatorAlias = Mapped<(MemargCombinator, LaneidxCombinator), V128LaneMapper>;


pub closed spec fn spec_v128_lane() -> SpecV128LaneCombinator {
    SpecV128LaneCombinator(
    Mapped {
        inner: (spec_memarg(), spec_laneidx()),
        mapper: V128LaneMapper::spec_new(),
    })
}

                
pub fn v128_lane() -> (o: V128LaneCombinator)
    ensures o@ == spec_v128_lane(),
{
    V128LaneCombinator(
    Mapped {
        inner: (memarg(), laneidx()),
        mapper: V128LaneMapper::new(),
    })
}

                
pub type SpecV128Const = Seq<u8>;
pub type V128Const<'a> = &'a [u8];


pub struct SpecV128ConstCombinator(SpecV128ConstCombinatorAlias);

impl SpecCombinator for SpecV128ConstCombinator {
    type Type = SpecV128Const;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecV128ConstCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecV128ConstCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecV128ConstCombinatorAlias = bytes::Fixed<16>;

pub struct V128ConstCombinator(V128ConstCombinatorAlias);

impl View for V128ConstCombinator {
    type V = SpecV128ConstCombinator;
    closed spec fn view(&self) -> Self::V { SpecV128ConstCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for V128ConstCombinator {
    type Type = V128Const<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type V128ConstCombinatorAlias = bytes::Fixed<16>;


pub closed spec fn spec_v128_const() -> SpecV128ConstCombinator {
    SpecV128ConstCombinator(bytes::Fixed::<16>)
}

                
pub fn v128_const() -> (o: V128ConstCombinator)
    ensures o@ == spec_v128_const(),
{
    V128ConstCombinator(bytes::Fixed::<16>)
}

                
pub type SpecShuffle = Seq<SpecLaneidx>;
pub type Shuffle = RepeatResult<Laneidx>;


pub struct SpecShuffleCombinator(SpecShuffleCombinatorAlias);

impl SpecCombinator for SpecShuffleCombinator {
    type Type = SpecShuffle;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecShuffleCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecShuffleCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecShuffleCombinatorAlias = RepeatN<SpecLaneidxCombinator>;

pub struct ShuffleCombinator(ShuffleCombinatorAlias);

impl View for ShuffleCombinator {
    type V = SpecShuffleCombinator;
    closed spec fn view(&self) -> Self::V { SpecShuffleCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ShuffleCombinator {
    type Type = Shuffle;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ShuffleCombinatorAlias = RepeatN<LaneidxCombinator>;


pub closed spec fn spec_shuffle() -> SpecShuffleCombinator {
    SpecShuffleCombinator(RepeatN(spec_laneidx(), 16))
}

                
pub fn shuffle() -> (o: ShuffleCombinator)
    ensures o@ == spec_shuffle(),
{
    ShuffleCombinator(RepeatN(laneidx(), 16))
}

                

pub enum SpecInstrWithFdRest {
    Variant0(SpecMemarg),
    Variant1(SpecMemarg),
    Variant2(SpecMemarg),
    Variant3(SpecV128Lane),
    Variant4(SpecV128Const),
    Variant5(SpecShuffle),
    Variant6(SpecLaneidx),
    Variant7(SpecEmpty),
}

pub type SpecInstrWithFdRestInner = Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecV128Lane, Either<SpecV128Const, Either<SpecShuffle, Either<SpecLaneidx, SpecEmpty>>>>>>>;



impl SpecFrom<SpecInstrWithFdRest> for SpecInstrWithFdRestInner {
    open spec fn spec_from(m: SpecInstrWithFdRest) -> SpecInstrWithFdRestInner {
        match m {
            SpecInstrWithFdRest::Variant0(m) => Either::Left(m),
            SpecInstrWithFdRest::Variant1(m) => Either::Right(Either::Left(m)),
            SpecInstrWithFdRest::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrWithFdRest::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrWithFdRest::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecInstrWithFdRest::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecInstrWithFdRest::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecInstrWithFdRest::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))),
        }
    }

}

impl SpecFrom<SpecInstrWithFdRestInner> for SpecInstrWithFdRest {
    open spec fn spec_from(m: SpecInstrWithFdRestInner) -> SpecInstrWithFdRest {
        match m {
            Either::Left(m) => SpecInstrWithFdRest::Variant0(m),
            Either::Right(Either::Left(m)) => SpecInstrWithFdRest::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrWithFdRest::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrWithFdRest::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecInstrWithFdRest::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecInstrWithFdRest::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecInstrWithFdRest::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))) => SpecInstrWithFdRest::Variant7(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrWithFdRest<'a> {
    Variant0(Memarg),
    Variant1(Memarg),
    Variant2(Memarg),
    Variant3(V128Lane),
    Variant4(V128Const<'a>),
    Variant5(Shuffle),
    Variant6(Laneidx),
    Variant7(Empty<'a>),
}

pub type InstrWithFdRestInner<'a> = Either<Memarg, Either<Memarg, Either<Memarg, Either<V128Lane, Either<V128Const<'a>, Either<Shuffle, Either<Laneidx, Empty<'a>>>>>>>>;


impl<'a> View for InstrWithFdRest<'a> {
    type V = SpecInstrWithFdRest;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrWithFdRest::Variant0(m) => SpecInstrWithFdRest::Variant0(m@),
            InstrWithFdRest::Variant1(m) => SpecInstrWithFdRest::Variant1(m@),
            InstrWithFdRest::Variant2(m) => SpecInstrWithFdRest::Variant2(m@),
            InstrWithFdRest::Variant3(m) => SpecInstrWithFdRest::Variant3(m@),
            InstrWithFdRest::Variant4(m) => SpecInstrWithFdRest::Variant4(m@),
            InstrWithFdRest::Variant5(m) => SpecInstrWithFdRest::Variant5(m@),
            InstrWithFdRest::Variant6(m) => SpecInstrWithFdRest::Variant6(m@),
            InstrWithFdRest::Variant7(m) => SpecInstrWithFdRest::Variant7(m@),
        }
    }
}


impl<'a> From<InstrWithFdRest<'a>> for InstrWithFdRestInner<'a> {
    fn ex_from(m: InstrWithFdRest<'a>) -> InstrWithFdRestInner<'a> {
        match m {
            InstrWithFdRest::Variant0(m) => Either::Left(m),
            InstrWithFdRest::Variant1(m) => Either::Right(Either::Left(m)),
            InstrWithFdRest::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrWithFdRest::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrWithFdRest::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            InstrWithFdRest::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            InstrWithFdRest::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            InstrWithFdRest::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))),
        }
    }

}

impl<'a> From<InstrWithFdRestInner<'a>> for InstrWithFdRest<'a> {
    fn ex_from(m: InstrWithFdRestInner<'a>) -> InstrWithFdRest<'a> {
        match m {
            Either::Left(m) => InstrWithFdRest::Variant0(m),
            Either::Right(Either::Left(m)) => InstrWithFdRest::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrWithFdRest::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrWithFdRest::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => InstrWithFdRest::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => InstrWithFdRest::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => InstrWithFdRest::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))) => InstrWithFdRest::Variant7(m),
        }
    }
    
}


pub struct InstrWithFdRestMapper<'a>(PhantomData<&'a ()>);
impl<'a> InstrWithFdRestMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        InstrWithFdRestMapper(PhantomData)
    }
    pub fn new() -> Self {
        InstrWithFdRestMapper(PhantomData)
    }
}
impl View for InstrWithFdRestMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrWithFdRestMapper<'_> {
    type Src = SpecInstrWithFdRestInner;
    type Dst = SpecInstrWithFdRest;
}
impl SpecIsoProof for InstrWithFdRestMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for InstrWithFdRestMapper<'a> {
    type Src = InstrWithFdRestInner<'a>;
    type Dst = InstrWithFdRest<'a>;
}


pub struct SpecInstrWithFdRestCombinator(SpecInstrWithFdRestCombinatorAlias);

impl SpecCombinator for SpecInstrWithFdRestCombinator {
    type Type = SpecInstrWithFdRest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrWithFdRestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrWithFdRestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecInstrWithFdRestCombinatorAlias = Mapped<Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecV128LaneCombinator>, Choice<Cond<SpecV128ConstCombinator>, Choice<Cond<SpecShuffleCombinator>, Choice<Cond<SpecLaneidxCombinator>, Cond<SpecEmptyCombinator>>>>>>>>, InstrWithFdRestMapper<'static>>;

pub struct InstrWithFdRestCombinator<'a>(InstrWithFdRestCombinatorAlias<'a>);

impl<'a> View for InstrWithFdRestCombinator<'a> {
    type V = SpecInstrWithFdRestCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrWithFdRestCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for InstrWithFdRestCombinator<'a> {
    type Type = InstrWithFdRest<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type InstrWithFdRestCombinatorAlias<'a> = Mapped<Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<V128LaneCombinator>, Choice<Cond<V128ConstCombinator>, Choice<Cond<ShuffleCombinator>, Choice<Cond<LaneidxCombinator>, Cond<EmptyCombinator>>>>>>>>, InstrWithFdRestMapper<'a>>;


pub closed spec fn spec_instr_with_fd_rest(tag: u64) -> SpecInstrWithFdRestCombinator {
    SpecInstrWithFdRestCombinator(Mapped { inner: Choice(Cond { cond: tag >= 0 && tag <= 11, inner: spec_memarg() }, Choice(Cond { cond: tag == 92, inner: spec_memarg() }, Choice(Cond { cond: tag == 93, inner: spec_memarg() }, Choice(Cond { cond: tag >= 84 && tag <= 91, inner: spec_v128_lane() }, Choice(Cond { cond: tag == 12, inner: spec_v128_const() }, Choice(Cond { cond: tag == 13, inner: spec_shuffle() }, Choice(Cond { cond: tag >= 21 && tag <= 34, inner: spec_laneidx() }, Cond { cond: !(tag >= 0 && tag <= 11 || tag == 92 || tag == 93 || tag >= 84 && tag <= 91 || tag == 12 || tag == 13 || tag >= 21 && tag <= 34), inner: spec_empty() }))))))), mapper: InstrWithFdRestMapper::spec_new() })
}

pub fn instr_with_fd_rest<'a>(tag: u64) -> (o: InstrWithFdRestCombinator<'a>)
    ensures o@ == spec_instr_with_fd_rest(tag@),
{
    InstrWithFdRestCombinator(Mapped { inner: Choice::new(Cond { cond: tag >= 0 && tag <= 11, inner: memarg() }, Choice::new(Cond { cond: tag == 92, inner: memarg() }, Choice::new(Cond { cond: tag == 93, inner: memarg() }, Choice::new(Cond { cond: tag >= 84 && tag <= 91, inner: v128_lane() }, Choice::new(Cond { cond: tag == 12, inner: v128_const() }, Choice::new(Cond { cond: tag == 13, inner: shuffle() }, Choice::new(Cond { cond: tag >= 21 && tag <= 34, inner: laneidx() }, Cond { cond: !(tag >= 0 && tag <= 11 || tag == 92 || tag == 93 || tag >= 84 && tag <= 91 || tag == 12 || tag == 13 || tag >= 21 && tag <= 34), inner: empty() }))))))), mapper: InstrWithFdRestMapper::new() })
}


pub struct SpecInstrWithFd {
    pub tag: u64,
    pub rest: SpecInstrWithFdRest,
}

pub type SpecInstrWithFdInner = (u64, SpecInstrWithFdRest);
impl SpecFrom<SpecInstrWithFd> for SpecInstrWithFdInner {
    open spec fn spec_from(m: SpecInstrWithFd) -> SpecInstrWithFdInner {
        (m.tag, m.rest)
    }
}
impl SpecFrom<SpecInstrWithFdInner> for SpecInstrWithFd {
    open spec fn spec_from(m: SpecInstrWithFdInner) -> SpecInstrWithFd {
        let (tag, rest) = m;
        SpecInstrWithFd { tag, rest }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct InstrWithFd<'a> {
    pub tag: u64,
    pub rest: InstrWithFdRest<'a>,
}

impl View for InstrWithFd<'_> {
    type V = SpecInstrWithFd;

    open spec fn view(&self) -> Self::V {
        SpecInstrWithFd {
            tag: self.tag@,
            rest: self.rest@,
        }
    }
}
pub type InstrWithFdInner<'a> = (u64, InstrWithFdRest<'a>);
impl<'a> From<InstrWithFd<'a>> for InstrWithFdInner<'a> {
    fn ex_from(m: InstrWithFd) -> InstrWithFdInner {
        (m.tag, m.rest)
    }
}
impl<'a> From<InstrWithFdInner<'a>> for InstrWithFd<'a> {
    fn ex_from(m: InstrWithFdInner) -> InstrWithFd {
        let (tag, rest) = m;
        InstrWithFd { tag, rest }
    }
}

pub struct InstrWithFdMapper<'a>(PhantomData<&'a ()>);
impl<'a> InstrWithFdMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        InstrWithFdMapper(PhantomData)
    }
    pub fn new() -> Self {
        InstrWithFdMapper(PhantomData)
    }
}
impl View for InstrWithFdMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrWithFdMapper<'_> {
    type Src = SpecInstrWithFdInner;
    type Dst = SpecInstrWithFd;
}
impl SpecIsoProof for InstrWithFdMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for InstrWithFdMapper<'a> {
    type Src = InstrWithFdInner<'a>;
    type Dst = InstrWithFd<'a>;
}

pub struct SpecInstrWithFdCombinator(SpecInstrWithFdCombinatorAlias);

impl SpecCombinator for SpecInstrWithFdCombinator {
    type Type = SpecInstrWithFd;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrWithFdCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrWithFdCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecInstrWithFdCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, SpecInstrWithFdRestCombinator>, InstrWithFdMapper<'static>>;

pub struct InstrWithFdCombinator<'a>(InstrWithFdCombinatorAlias<'a>);

impl<'a> View for InstrWithFdCombinator<'a> {
    type V = SpecInstrWithFdCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrWithFdCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for InstrWithFdCombinator<'a> {
    type Type = InstrWithFd<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type InstrWithFdCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, InstrWithFdRestCombinator<'a>, InstrWithFdCont0<'a>>, InstrWithFdMapper<'a>>;


pub closed spec fn spec_instr_with_fd() -> SpecInstrWithFdCombinator {
    SpecInstrWithFdCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_instr_with_fd_cont0(deps) },
        mapper: InstrWithFdMapper::spec_new(),
    })
}

pub open spec fn spec_instr_with_fd_cont0(deps: u64) -> SpecInstrWithFdRestCombinator {
    let tag = deps;
    spec_instr_with_fd_rest(tag)
}
                
pub fn instr_with_fd<'a>() -> (o: InstrWithFdCombinator<'a>)
    ensures o@ == spec_instr_with_fd(),
{
    InstrWithFdCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: InstrWithFdCont0::new(), spec_snd: Ghost(|deps| spec_instr_with_fd_cont0(deps)) },
        mapper: InstrWithFdMapper::new(),
    })
}

pub struct InstrWithFdCont0<'a>(PhantomData<&'a ()>);
impl<'a> InstrWithFdCont0<'a> {
    pub fn new() -> Self {
        InstrWithFdCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for InstrWithFdCont0<'a> {
    type Output = InstrWithFdRestCombinator<'a>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_instr_with_fd_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let tag = *deps;
        instr_with_fd_rest(tag)
    }
}
                

pub enum SpecInstrRest {
    LocalGet(SpecLocalidx),
    I32Const(u64),
    LocalTee(SpecLocalidx),
    I32Add(SpecEmpty),
    End(SpecEmpty),
    LocalSet(SpecLocalidx),
    I32Store(SpecMemarg),
    I32Load(SpecMemarg),
    BrIf(SpecLabelidx),
    I32And(SpecEmpty),
    If(SpecBlocktype),
    Block(SpecBlocktype),
    I32Eqz(SpecEmpty),
    I32Sub(SpecEmpty),
    Br(SpecLabelidx),
    Call(SpecFuncidx),
    I32Or(SpecEmpty),
    Select(SpecEmpty),
    I32ShrU(SpecEmpty),
    I32Shl(SpecEmpty),
    Unreachable(SpecEmpty),
    Nop(SpecEmpty),
    Loop(SpecBlocktype),
    BrTable(SpecBrTable),
    Ret(SpecEmpty),
    CallIndirect(SpecCallIndirect),
    RefNull(SpecReftype),
    RefIsNull(SpecEmpty),
    RefFunc(SpecFuncidx),
    Drop(SpecEmpty),
    SelectT(SpecSelectT),
    GlobalGet(SpecGlobalidx),
    GlobalSet(SpecGlobalidx),
    TableGet(SpecTableidx),
    TableSet(SpecTableidx),
    I64Load(SpecMemarg),
    F32Load(SpecMemarg),
    F64Load(SpecMemarg),
    I32Load8S(SpecMemarg),
    I32Load8U(SpecMemarg),
    I32Load16S(SpecMemarg),
    I32Load16U(SpecMemarg),
    I64Load8S(SpecMemarg),
    I64Load8U(SpecMemarg),
    I64Load16S(SpecMemarg),
    I64Load16U(SpecMemarg),
    I64Load32S(SpecMemarg),
    I64Load32U(SpecMemarg),
    I64Store(SpecMemarg),
    F32Store(SpecMemarg),
    F64Store(SpecMemarg),
    I32Store8(SpecMemarg),
    I32Store16(SpecMemarg),
    I64Store8(SpecMemarg),
    I64Store16(SpecMemarg),
    I64Store32(SpecMemarg),
    MemorySize(SpecByteZero),
    MemoryGrow(SpecByteZero),
    I64Const(u64),
    F32Const(SpecF32),
    F64Const(SpecF64),
    OpcodeFC(SpecInstrWithFc),
    OpcodeFD(SpecInstrWithFd),
    Unrecognized(SpecEmpty),
}

pub type SpecInstrRestInner = Either<SpecLocalidx, Either<u64, Either<SpecLocalidx, Either<SpecEmpty, Either<SpecEmpty, Either<SpecLocalidx, Either<SpecMemarg, Either<SpecMemarg, Either<SpecLabelidx, Either<SpecEmpty, Either<SpecBlocktype, Either<SpecBlocktype, Either<SpecEmpty, Either<SpecEmpty, Either<SpecLabelidx, Either<SpecFuncidx, Either<SpecEmpty, Either<SpecEmpty, Either<SpecEmpty, Either<SpecEmpty, Either<SpecEmpty, Either<SpecEmpty, Either<SpecBlocktype, Either<SpecBrTable, Either<SpecEmpty, Either<SpecCallIndirect, Either<SpecReftype, Either<SpecEmpty, Either<SpecFuncidx, Either<SpecEmpty, Either<SpecSelectT, Either<SpecGlobalidx, Either<SpecGlobalidx, Either<SpecTableidx, Either<SpecTableidx, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecByteZero, Either<SpecByteZero, Either<u64, Either<SpecF32, Either<SpecF64, Either<SpecInstrWithFc, Either<SpecInstrWithFd, SpecEmpty>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;



impl SpecFrom<SpecInstrRest> for SpecInstrRestInner {
    open spec fn spec_from(m: SpecInstrRest) -> SpecInstrRestInner {
        match m {
            SpecInstrRest::LocalGet(m) => Either::Left(m),
            SpecInstrRest::I32Const(m) => Either::Right(Either::Left(m)),
            SpecInstrRest::LocalTee(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrRest::I32Add(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrRest::End(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecInstrRest::LocalSet(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecInstrRest::I32Store(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecInstrRest::I32Load(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecInstrRest::BrIf(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecInstrRest::I32And(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecInstrRest::If(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecInstrRest::Block(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecInstrRest::I32Eqz(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecInstrRest::I32Sub(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecInstrRest::Br(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecInstrRest::Call(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecInstrRest::I32Or(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SpecInstrRest::Select(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SpecInstrRest::I32ShrU(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SpecInstrRest::I32Shl(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SpecInstrRest::Unreachable(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SpecInstrRest::Nop(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SpecInstrRest::Loop(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SpecInstrRest::BrTable(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SpecInstrRest::Ret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SpecInstrRest::CallIndirect(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SpecInstrRest::RefNull(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            SpecInstrRest::RefIsNull(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            SpecInstrRest::RefFunc(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            SpecInstrRest::Drop(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            SpecInstrRest::SelectT(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))),
            SpecInstrRest::GlobalGet(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))),
            SpecInstrRest::GlobalSet(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))),
            SpecInstrRest::TableGet(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))),
            SpecInstrRest::TableSet(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Load(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))),
            SpecInstrRest::F32Load(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::F64Load(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I32Load8S(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I32Load8U(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I32Load16S(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I32Load16U(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Load8S(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Load8U(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Load16S(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Load16U(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Load32S(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Load32U(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Store(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::F32Store(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::F64Store(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I32Store8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I32Store16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Store8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Store16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Store32(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::MemorySize(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::MemoryGrow(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::I64Const(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::F32Const(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::F64Const(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::OpcodeFC(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::OpcodeFD(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecInstrRest::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
        }
    }

}

impl SpecFrom<SpecInstrRestInner> for SpecInstrRest {
    open spec fn spec_from(m: SpecInstrRestInner) -> SpecInstrRest {
        match m {
            Either::Left(m) => SpecInstrRest::LocalGet(m),
            Either::Right(Either::Left(m)) => SpecInstrRest::I32Const(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrRest::LocalTee(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrRest::I32Add(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecInstrRest::End(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecInstrRest::LocalSet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecInstrRest::I32Store(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecInstrRest::I32Load(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecInstrRest::BrIf(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecInstrRest::I32And(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecInstrRest::If(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecInstrRest::Block(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecInstrRest::I32Eqz(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecInstrRest::I32Sub(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecInstrRest::Br(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecInstrRest::Call(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SpecInstrRest::I32Or(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SpecInstrRest::Select(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SpecInstrRest::I32ShrU(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SpecInstrRest::I32Shl(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SpecInstrRest::Unreachable(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SpecInstrRest::Nop(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SpecInstrRest::Loop(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SpecInstrRest::BrTable(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SpecInstrRest::Ret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SpecInstrRest::CallIndirect(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => SpecInstrRest::RefNull(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => SpecInstrRest::RefIsNull(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => SpecInstrRest::RefFunc(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => SpecInstrRest::Drop(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))) => SpecInstrRest::SelectT(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))) => SpecInstrRest::GlobalGet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))) => SpecInstrRest::GlobalSet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))) => SpecInstrRest::TableGet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))) => SpecInstrRest::TableSet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Load(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))) => SpecInstrRest::F32Load(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))) => SpecInstrRest::F64Load(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I32Load8S(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I32Load8U(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I32Load16S(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I32Load16U(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Load8S(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Load8U(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Load16S(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Load16U(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Load32S(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Load32U(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Store(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::F32Store(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::F64Store(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I32Store8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I32Store16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Store8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Store16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Store32(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::MemorySize(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::MemoryGrow(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::I64Const(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::F32Const(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::F64Const(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::OpcodeFC(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::OpcodeFD(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecInstrRest::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrRest<'a> {
    LocalGet(Localidx),
    I32Const(u64),
    LocalTee(Localidx),
    I32Add(Empty<'a>),
    End(Empty<'a>),
    LocalSet(Localidx),
    I32Store(Memarg),
    I32Load(Memarg),
    BrIf(Labelidx),
    I32And(Empty<'a>),
    If(Blocktype<'a>),
    Block(Blocktype<'a>),
    I32Eqz(Empty<'a>),
    I32Sub(Empty<'a>),
    Br(Labelidx),
    Call(Funcidx),
    I32Or(Empty<'a>),
    Select(Empty<'a>),
    I32ShrU(Empty<'a>),
    I32Shl(Empty<'a>),
    Unreachable(Empty<'a>),
    Nop(Empty<'a>),
    Loop(Blocktype<'a>),
    BrTable(BrTable),
    Ret(Empty<'a>),
    CallIndirect(CallIndirect),
    RefNull(Reftype),
    RefIsNull(Empty<'a>),
    RefFunc(Funcidx),
    Drop(Empty<'a>),
    SelectT(SelectT),
    GlobalGet(Globalidx),
    GlobalSet(Globalidx),
    TableGet(Tableidx),
    TableSet(Tableidx),
    I64Load(Memarg),
    F32Load(Memarg),
    F64Load(Memarg),
    I32Load8S(Memarg),
    I32Load8U(Memarg),
    I32Load16S(Memarg),
    I32Load16U(Memarg),
    I64Load8S(Memarg),
    I64Load8U(Memarg),
    I64Load16S(Memarg),
    I64Load16U(Memarg),
    I64Load32S(Memarg),
    I64Load32U(Memarg),
    I64Store(Memarg),
    F32Store(Memarg),
    F64Store(Memarg),
    I32Store8(Memarg),
    I32Store16(Memarg),
    I64Store8(Memarg),
    I64Store16(Memarg),
    I64Store32(Memarg),
    MemorySize(ByteZero),
    MemoryGrow(ByteZero),
    I64Const(u64),
    F32Const(F32<'a>),
    F64Const(F64<'a>),
    OpcodeFC(InstrWithFc<'a>),
    OpcodeFD(InstrWithFd<'a>),
    Unrecognized(Empty<'a>),
}

pub type InstrRestInner<'a> = Either<Localidx, Either<u64, Either<Localidx, Either<Empty<'a>, Either<Empty<'a>, Either<Localidx, Either<Memarg, Either<Memarg, Either<Labelidx, Either<Empty<'a>, Either<Blocktype<'a>, Either<Blocktype<'a>, Either<Empty<'a>, Either<Empty<'a>, Either<Labelidx, Either<Funcidx, Either<Empty<'a>, Either<Empty<'a>, Either<Empty<'a>, Either<Empty<'a>, Either<Empty<'a>, Either<Empty<'a>, Either<Blocktype<'a>, Either<BrTable, Either<Empty<'a>, Either<CallIndirect, Either<Reftype, Either<Empty<'a>, Either<Funcidx, Either<Empty<'a>, Either<SelectT, Either<Globalidx, Either<Globalidx, Either<Tableidx, Either<Tableidx, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<ByteZero, Either<ByteZero, Either<u64, Either<F32<'a>, Either<F64<'a>, Either<InstrWithFc<'a>, Either<InstrWithFd<'a>, Empty<'a>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;


impl<'a> View for InstrRest<'a> {
    type V = SpecInstrRest;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrRest::LocalGet(m) => SpecInstrRest::LocalGet(m@),
            InstrRest::I32Const(m) => SpecInstrRest::I32Const(m@),
            InstrRest::LocalTee(m) => SpecInstrRest::LocalTee(m@),
            InstrRest::I32Add(m) => SpecInstrRest::I32Add(m@),
            InstrRest::End(m) => SpecInstrRest::End(m@),
            InstrRest::LocalSet(m) => SpecInstrRest::LocalSet(m@),
            InstrRest::I32Store(m) => SpecInstrRest::I32Store(m@),
            InstrRest::I32Load(m) => SpecInstrRest::I32Load(m@),
            InstrRest::BrIf(m) => SpecInstrRest::BrIf(m@),
            InstrRest::I32And(m) => SpecInstrRest::I32And(m@),
            InstrRest::If(m) => SpecInstrRest::If(m@),
            InstrRest::Block(m) => SpecInstrRest::Block(m@),
            InstrRest::I32Eqz(m) => SpecInstrRest::I32Eqz(m@),
            InstrRest::I32Sub(m) => SpecInstrRest::I32Sub(m@),
            InstrRest::Br(m) => SpecInstrRest::Br(m@),
            InstrRest::Call(m) => SpecInstrRest::Call(m@),
            InstrRest::I32Or(m) => SpecInstrRest::I32Or(m@),
            InstrRest::Select(m) => SpecInstrRest::Select(m@),
            InstrRest::I32ShrU(m) => SpecInstrRest::I32ShrU(m@),
            InstrRest::I32Shl(m) => SpecInstrRest::I32Shl(m@),
            InstrRest::Unreachable(m) => SpecInstrRest::Unreachable(m@),
            InstrRest::Nop(m) => SpecInstrRest::Nop(m@),
            InstrRest::Loop(m) => SpecInstrRest::Loop(m@),
            InstrRest::BrTable(m) => SpecInstrRest::BrTable(m@),
            InstrRest::Ret(m) => SpecInstrRest::Ret(m@),
            InstrRest::CallIndirect(m) => SpecInstrRest::CallIndirect(m@),
            InstrRest::RefNull(m) => SpecInstrRest::RefNull(m@),
            InstrRest::RefIsNull(m) => SpecInstrRest::RefIsNull(m@),
            InstrRest::RefFunc(m) => SpecInstrRest::RefFunc(m@),
            InstrRest::Drop(m) => SpecInstrRest::Drop(m@),
            InstrRest::SelectT(m) => SpecInstrRest::SelectT(m@),
            InstrRest::GlobalGet(m) => SpecInstrRest::GlobalGet(m@),
            InstrRest::GlobalSet(m) => SpecInstrRest::GlobalSet(m@),
            InstrRest::TableGet(m) => SpecInstrRest::TableGet(m@),
            InstrRest::TableSet(m) => SpecInstrRest::TableSet(m@),
            InstrRest::I64Load(m) => SpecInstrRest::I64Load(m@),
            InstrRest::F32Load(m) => SpecInstrRest::F32Load(m@),
            InstrRest::F64Load(m) => SpecInstrRest::F64Load(m@),
            InstrRest::I32Load8S(m) => SpecInstrRest::I32Load8S(m@),
            InstrRest::I32Load8U(m) => SpecInstrRest::I32Load8U(m@),
            InstrRest::I32Load16S(m) => SpecInstrRest::I32Load16S(m@),
            InstrRest::I32Load16U(m) => SpecInstrRest::I32Load16U(m@),
            InstrRest::I64Load8S(m) => SpecInstrRest::I64Load8S(m@),
            InstrRest::I64Load8U(m) => SpecInstrRest::I64Load8U(m@),
            InstrRest::I64Load16S(m) => SpecInstrRest::I64Load16S(m@),
            InstrRest::I64Load16U(m) => SpecInstrRest::I64Load16U(m@),
            InstrRest::I64Load32S(m) => SpecInstrRest::I64Load32S(m@),
            InstrRest::I64Load32U(m) => SpecInstrRest::I64Load32U(m@),
            InstrRest::I64Store(m) => SpecInstrRest::I64Store(m@),
            InstrRest::F32Store(m) => SpecInstrRest::F32Store(m@),
            InstrRest::F64Store(m) => SpecInstrRest::F64Store(m@),
            InstrRest::I32Store8(m) => SpecInstrRest::I32Store8(m@),
            InstrRest::I32Store16(m) => SpecInstrRest::I32Store16(m@),
            InstrRest::I64Store8(m) => SpecInstrRest::I64Store8(m@),
            InstrRest::I64Store16(m) => SpecInstrRest::I64Store16(m@),
            InstrRest::I64Store32(m) => SpecInstrRest::I64Store32(m@),
            InstrRest::MemorySize(m) => SpecInstrRest::MemorySize(m@),
            InstrRest::MemoryGrow(m) => SpecInstrRest::MemoryGrow(m@),
            InstrRest::I64Const(m) => SpecInstrRest::I64Const(m@),
            InstrRest::F32Const(m) => SpecInstrRest::F32Const(m@),
            InstrRest::F64Const(m) => SpecInstrRest::F64Const(m@),
            InstrRest::OpcodeFC(m) => SpecInstrRest::OpcodeFC(m@),
            InstrRest::OpcodeFD(m) => SpecInstrRest::OpcodeFD(m@),
            InstrRest::Unrecognized(m) => SpecInstrRest::Unrecognized(m@),
        }
    }
}


impl<'a> From<InstrRest<'a>> for InstrRestInner<'a> {
    fn ex_from(m: InstrRest<'a>) -> InstrRestInner<'a> {
        match m {
            InstrRest::LocalGet(m) => Either::Left(m),
            InstrRest::I32Const(m) => Either::Right(Either::Left(m)),
            InstrRest::LocalTee(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrRest::I32Add(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrRest::End(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            InstrRest::LocalSet(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            InstrRest::I32Store(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            InstrRest::I32Load(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            InstrRest::BrIf(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            InstrRest::I32And(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            InstrRest::If(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            InstrRest::Block(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            InstrRest::I32Eqz(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            InstrRest::I32Sub(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            InstrRest::Br(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            InstrRest::Call(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            InstrRest::I32Or(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            InstrRest::Select(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            InstrRest::I32ShrU(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            InstrRest::I32Shl(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            InstrRest::Unreachable(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            InstrRest::Nop(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            InstrRest::Loop(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            InstrRest::BrTable(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            InstrRest::Ret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            InstrRest::CallIndirect(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            InstrRest::RefNull(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            InstrRest::RefIsNull(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            InstrRest::RefFunc(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            InstrRest::Drop(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            InstrRest::SelectT(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))),
            InstrRest::GlobalGet(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))),
            InstrRest::GlobalSet(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))),
            InstrRest::TableGet(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))),
            InstrRest::TableSet(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))),
            InstrRest::I64Load(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))),
            InstrRest::F32Load(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))),
            InstrRest::F64Load(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))),
            InstrRest::I32Load8S(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))),
            InstrRest::I32Load8U(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))),
            InstrRest::I32Load16S(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I32Load16U(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Load8S(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Load8U(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Load16S(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Load16U(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Load32S(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Load32U(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Store(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::F32Store(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::F64Store(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I32Store8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I32Store16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Store8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Store16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Store32(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::MemorySize(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::MemoryGrow(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::I64Const(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::F32Const(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::F64Const(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::OpcodeFC(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::OpcodeFD(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            InstrRest::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
        }
    }

}

impl<'a> From<InstrRestInner<'a>> for InstrRest<'a> {
    fn ex_from(m: InstrRestInner<'a>) -> InstrRest<'a> {
        match m {
            Either::Left(m) => InstrRest::LocalGet(m),
            Either::Right(Either::Left(m)) => InstrRest::I32Const(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrRest::LocalTee(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrRest::I32Add(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => InstrRest::End(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => InstrRest::LocalSet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => InstrRest::I32Store(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => InstrRest::I32Load(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => InstrRest::BrIf(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => InstrRest::I32And(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => InstrRest::If(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => InstrRest::Block(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => InstrRest::I32Eqz(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => InstrRest::I32Sub(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => InstrRest::Br(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => InstrRest::Call(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => InstrRest::I32Or(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => InstrRest::Select(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => InstrRest::I32ShrU(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => InstrRest::I32Shl(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => InstrRest::Unreachable(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => InstrRest::Nop(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => InstrRest::Loop(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => InstrRest::BrTable(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => InstrRest::Ret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => InstrRest::CallIndirect(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => InstrRest::RefNull(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => InstrRest::RefIsNull(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => InstrRest::RefFunc(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => InstrRest::Drop(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))) => InstrRest::SelectT(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))) => InstrRest::GlobalGet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))) => InstrRest::GlobalSet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))) => InstrRest::TableGet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))) => InstrRest::TableSet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))) => InstrRest::I64Load(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))) => InstrRest::F32Load(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))) => InstrRest::F64Load(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))) => InstrRest::I32Load8S(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))) => InstrRest::I32Load8U(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))) => InstrRest::I32Load16S(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))) => InstrRest::I32Load16U(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Load8S(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Load8U(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Load16S(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Load16U(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Load32S(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Load32U(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Store(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::F32Store(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::F64Store(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I32Store8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I32Store16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Store8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Store16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Store32(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::MemorySize(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::MemoryGrow(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::I64Const(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::F32Const(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::F64Const(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::OpcodeFC(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::OpcodeFD(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => InstrRest::Unrecognized(m),
        }
    }
    
}


pub struct InstrRestMapper<'a>(PhantomData<&'a ()>);
impl<'a> InstrRestMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        InstrRestMapper(PhantomData)
    }
    pub fn new() -> Self {
        InstrRestMapper(PhantomData)
    }
}
impl View for InstrRestMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrRestMapper<'_> {
    type Src = SpecInstrRestInner;
    type Dst = SpecInstrRest;
}
impl SpecIsoProof for InstrRestMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for InstrRestMapper<'a> {
    type Src = InstrRestInner<'a>;
    type Dst = InstrRest<'a>;
}


pub struct SpecInstrRestCombinator(SpecInstrRestCombinatorAlias);

impl SpecCombinator for SpecInstrRestCombinator {
    type Type = SpecInstrRest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrRestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrRestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecInstrRestCombinatorAlias = Mapped<Choice<Cond<SpecLocalidxCombinator>, Choice<Cond<UnsignedLEB128>, Choice<Cond<SpecLocalidxCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecLocalidxCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecLabelidxCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecBlocktypeCombinator>, Choice<Cond<SpecBlocktypeCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecLabelidxCombinator>, Choice<Cond<SpecFuncidxCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecBlocktypeCombinator>, Choice<Cond<SpecBrTableCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecCallIndirectCombinator>, Choice<Cond<SpecReftypeCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecFuncidxCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecSelectTCombinator>, Choice<Cond<SpecGlobalidxCombinator>, Choice<Cond<SpecGlobalidxCombinator>, Choice<Cond<SpecTableidxCombinator>, Choice<Cond<SpecTableidxCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecByteZeroCombinator>, Choice<Cond<SpecByteZeroCombinator>, Choice<Cond<UnsignedLEB128>, Choice<Cond<SpecF32Combinator>, Choice<Cond<SpecF64Combinator>, Choice<Cond<SpecInstrWithFcCombinator>, Choice<Cond<SpecInstrWithFdCombinator>, Cond<SpecEmptyCombinator>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>, InstrRestMapper<'static>>;

pub struct InstrRestCombinator<'a>(InstrRestCombinatorAlias<'a>);

impl<'a> View for InstrRestCombinator<'a> {
    type V = SpecInstrRestCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrRestCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for InstrRestCombinator<'a> {
    type Type = InstrRest<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type InstrRestCombinatorAlias<'a> = Mapped<Choice<Cond<LocalidxCombinator>, Choice<Cond<UnsignedLEB128>, Choice<Cond<LocalidxCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<LocalidxCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<LabelidxCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<BlocktypeCombinator<'a>>, Choice<Cond<BlocktypeCombinator<'a>>, Choice<Cond<EmptyCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<LabelidxCombinator>, Choice<Cond<FuncidxCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<BlocktypeCombinator<'a>>, Choice<Cond<BrTableCombinator<'a>>, Choice<Cond<EmptyCombinator>, Choice<Cond<CallIndirectCombinator>, Choice<Cond<ReftypeCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<FuncidxCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<SelectTCombinator<'a>>, Choice<Cond<GlobalidxCombinator>, Choice<Cond<GlobalidxCombinator>, Choice<Cond<TableidxCombinator>, Choice<Cond<TableidxCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<ByteZeroCombinator>, Choice<Cond<ByteZeroCombinator>, Choice<Cond<UnsignedLEB128>, Choice<Cond<F32Combinator>, Choice<Cond<F64Combinator>, Choice<Cond<InstrWithFcCombinator<'a>>, Choice<Cond<InstrWithFdCombinator<'a>>, Cond<EmptyCombinator>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>, InstrRestMapper<'a>>;


pub closed spec fn spec_instr_rest(opcode: SpecInstrBytecode) -> SpecInstrRestCombinator {
    SpecInstrRestCombinator(Mapped { inner: Choice(Cond { cond: opcode == 32, inner: spec_localidx() }, Choice(Cond { cond: opcode == 65, inner: UnsignedLEB128 }, Choice(Cond { cond: opcode == 34, inner: spec_localidx() }, Choice(Cond { cond: opcode == 106, inner: spec_empty() }, Choice(Cond { cond: opcode == 11, inner: spec_empty() }, Choice(Cond { cond: opcode == 33, inner: spec_localidx() }, Choice(Cond { cond: opcode == 54, inner: spec_memarg() }, Choice(Cond { cond: opcode == 40, inner: spec_memarg() }, Choice(Cond { cond: opcode == 13, inner: spec_labelidx() }, Choice(Cond { cond: opcode == 113, inner: spec_empty() }, Choice(Cond { cond: opcode == 4, inner: spec_blocktype() }, Choice(Cond { cond: opcode == 2, inner: spec_blocktype() }, Choice(Cond { cond: opcode == 69, inner: spec_empty() }, Choice(Cond { cond: opcode == 107, inner: spec_empty() }, Choice(Cond { cond: opcode == 12, inner: spec_labelidx() }, Choice(Cond { cond: opcode == 16, inner: spec_funcidx() }, Choice(Cond { cond: opcode == 114, inner: spec_empty() }, Choice(Cond { cond: opcode == 27, inner: spec_empty() }, Choice(Cond { cond: opcode == 118, inner: spec_empty() }, Choice(Cond { cond: opcode == 116, inner: spec_empty() }, Choice(Cond { cond: opcode == 0, inner: spec_empty() }, Choice(Cond { cond: opcode == 1, inner: spec_empty() }, Choice(Cond { cond: opcode == 3, inner: spec_blocktype() }, Choice(Cond { cond: opcode == 14, inner: spec_br_table() }, Choice(Cond { cond: opcode == 15, inner: spec_empty() }, Choice(Cond { cond: opcode == 17, inner: spec_call_indirect() }, Choice(Cond { cond: opcode == 208, inner: spec_reftype() }, Choice(Cond { cond: opcode == 209, inner: spec_empty() }, Choice(Cond { cond: opcode == 210, inner: spec_funcidx() }, Choice(Cond { cond: opcode == 26, inner: spec_empty() }, Choice(Cond { cond: opcode == 28, inner: spec_select_t() }, Choice(Cond { cond: opcode == 35, inner: spec_globalidx() }, Choice(Cond { cond: opcode == 36, inner: spec_globalidx() }, Choice(Cond { cond: opcode == 37, inner: spec_tableidx() }, Choice(Cond { cond: opcode == 38, inner: spec_tableidx() }, Choice(Cond { cond: opcode == 41, inner: spec_memarg() }, Choice(Cond { cond: opcode == 42, inner: spec_memarg() }, Choice(Cond { cond: opcode == 43, inner: spec_memarg() }, Choice(Cond { cond: opcode == 44, inner: spec_memarg() }, Choice(Cond { cond: opcode == 45, inner: spec_memarg() }, Choice(Cond { cond: opcode == 46, inner: spec_memarg() }, Choice(Cond { cond: opcode == 47, inner: spec_memarg() }, Choice(Cond { cond: opcode == 48, inner: spec_memarg() }, Choice(Cond { cond: opcode == 49, inner: spec_memarg() }, Choice(Cond { cond: opcode == 50, inner: spec_memarg() }, Choice(Cond { cond: opcode == 51, inner: spec_memarg() }, Choice(Cond { cond: opcode == 52, inner: spec_memarg() }, Choice(Cond { cond: opcode == 53, inner: spec_memarg() }, Choice(Cond { cond: opcode == 55, inner: spec_memarg() }, Choice(Cond { cond: opcode == 56, inner: spec_memarg() }, Choice(Cond { cond: opcode == 57, inner: spec_memarg() }, Choice(Cond { cond: opcode == 58, inner: spec_memarg() }, Choice(Cond { cond: opcode == 59, inner: spec_memarg() }, Choice(Cond { cond: opcode == 60, inner: spec_memarg() }, Choice(Cond { cond: opcode == 61, inner: spec_memarg() }, Choice(Cond { cond: opcode == 62, inner: spec_memarg() }, Choice(Cond { cond: opcode == 63, inner: spec_byte_zero() }, Choice(Cond { cond: opcode == 64, inner: spec_byte_zero() }, Choice(Cond { cond: opcode == 66, inner: UnsignedLEB128 }, Choice(Cond { cond: opcode == 67, inner: spec_f32() }, Choice(Cond { cond: opcode == 68, inner: spec_f64() }, Choice(Cond { cond: opcode == 252, inner: spec_instr_with_fc() }, Choice(Cond { cond: opcode == 253, inner: spec_instr_with_fd() }, Cond { cond: !(opcode == 32 || opcode == 65 || opcode == 34 || opcode == 106 || opcode == 11 || opcode == 33 || opcode == 54 || opcode == 40 || opcode == 13 || opcode == 113 || opcode == 4 || opcode == 2 || opcode == 69 || opcode == 107 || opcode == 12 || opcode == 16 || opcode == 114 || opcode == 27 || opcode == 118 || opcode == 116 || opcode == 0 || opcode == 1 || opcode == 3 || opcode == 14 || opcode == 15 || opcode == 17 || opcode == 208 || opcode == 209 || opcode == 210 || opcode == 26 || opcode == 28 || opcode == 35 || opcode == 36 || opcode == 37 || opcode == 38 || opcode == 41 || opcode == 42 || opcode == 43 || opcode == 44 || opcode == 45 || opcode == 46 || opcode == 47 || opcode == 48 || opcode == 49 || opcode == 50 || opcode == 51 || opcode == 52 || opcode == 53 || opcode == 55 || opcode == 56 || opcode == 57 || opcode == 58 || opcode == 59 || opcode == 60 || opcode == 61 || opcode == 62 || opcode == 63 || opcode == 64 || opcode == 66 || opcode == 67 || opcode == 68 || opcode == 252 || opcode == 253), inner: spec_empty() }))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), mapper: InstrRestMapper::spec_new() })
}

pub fn instr_rest<'a>(opcode: InstrBytecode) -> (o: InstrRestCombinator<'a>)
    ensures o@ == spec_instr_rest(opcode@),
{
    InstrRestCombinator(Mapped { inner: Choice::new(Cond { cond: opcode == 32, inner: localidx() }, Choice::new(Cond { cond: opcode == 65, inner: UnsignedLEB128 }, Choice::new(Cond { cond: opcode == 34, inner: localidx() }, Choice::new(Cond { cond: opcode == 106, inner: empty() }, Choice::new(Cond { cond: opcode == 11, inner: empty() }, Choice::new(Cond { cond: opcode == 33, inner: localidx() }, Choice::new(Cond { cond: opcode == 54, inner: memarg() }, Choice::new(Cond { cond: opcode == 40, inner: memarg() }, Choice::new(Cond { cond: opcode == 13, inner: labelidx() }, Choice::new(Cond { cond: opcode == 113, inner: empty() }, Choice::new(Cond { cond: opcode == 4, inner: blocktype() }, Choice::new(Cond { cond: opcode == 2, inner: blocktype() }, Choice::new(Cond { cond: opcode == 69, inner: empty() }, Choice::new(Cond { cond: opcode == 107, inner: empty() }, Choice::new(Cond { cond: opcode == 12, inner: labelidx() }, Choice::new(Cond { cond: opcode == 16, inner: funcidx() }, Choice::new(Cond { cond: opcode == 114, inner: empty() }, Choice::new(Cond { cond: opcode == 27, inner: empty() }, Choice::new(Cond { cond: opcode == 118, inner: empty() }, Choice::new(Cond { cond: opcode == 116, inner: empty() }, Choice::new(Cond { cond: opcode == 0, inner: empty() }, Choice::new(Cond { cond: opcode == 1, inner: empty() }, Choice::new(Cond { cond: opcode == 3, inner: blocktype() }, Choice::new(Cond { cond: opcode == 14, inner: br_table() }, Choice::new(Cond { cond: opcode == 15, inner: empty() }, Choice::new(Cond { cond: opcode == 17, inner: call_indirect() }, Choice::new(Cond { cond: opcode == 208, inner: reftype() }, Choice::new(Cond { cond: opcode == 209, inner: empty() }, Choice::new(Cond { cond: opcode == 210, inner: funcidx() }, Choice::new(Cond { cond: opcode == 26, inner: empty() }, Choice::new(Cond { cond: opcode == 28, inner: select_t() }, Choice::new(Cond { cond: opcode == 35, inner: globalidx() }, Choice::new(Cond { cond: opcode == 36, inner: globalidx() }, Choice::new(Cond { cond: opcode == 37, inner: tableidx() }, Choice::new(Cond { cond: opcode == 38, inner: tableidx() }, Choice::new(Cond { cond: opcode == 41, inner: memarg() }, Choice::new(Cond { cond: opcode == 42, inner: memarg() }, Choice::new(Cond { cond: opcode == 43, inner: memarg() }, Choice::new(Cond { cond: opcode == 44, inner: memarg() }, Choice::new(Cond { cond: opcode == 45, inner: memarg() }, Choice::new(Cond { cond: opcode == 46, inner: memarg() }, Choice::new(Cond { cond: opcode == 47, inner: memarg() }, Choice::new(Cond { cond: opcode == 48, inner: memarg() }, Choice::new(Cond { cond: opcode == 49, inner: memarg() }, Choice::new(Cond { cond: opcode == 50, inner: memarg() }, Choice::new(Cond { cond: opcode == 51, inner: memarg() }, Choice::new(Cond { cond: opcode == 52, inner: memarg() }, Choice::new(Cond { cond: opcode == 53, inner: memarg() }, Choice::new(Cond { cond: opcode == 55, inner: memarg() }, Choice::new(Cond { cond: opcode == 56, inner: memarg() }, Choice::new(Cond { cond: opcode == 57, inner: memarg() }, Choice::new(Cond { cond: opcode == 58, inner: memarg() }, Choice::new(Cond { cond: opcode == 59, inner: memarg() }, Choice::new(Cond { cond: opcode == 60, inner: memarg() }, Choice::new(Cond { cond: opcode == 61, inner: memarg() }, Choice::new(Cond { cond: opcode == 62, inner: memarg() }, Choice::new(Cond { cond: opcode == 63, inner: byte_zero() }, Choice::new(Cond { cond: opcode == 64, inner: byte_zero() }, Choice::new(Cond { cond: opcode == 66, inner: UnsignedLEB128 }, Choice::new(Cond { cond: opcode == 67, inner: f32() }, Choice::new(Cond { cond: opcode == 68, inner: f64() }, Choice::new(Cond { cond: opcode == 252, inner: instr_with_fc() }, Choice::new(Cond { cond: opcode == 253, inner: instr_with_fd() }, Cond { cond: !(opcode == 32 || opcode == 65 || opcode == 34 || opcode == 106 || opcode == 11 || opcode == 33 || opcode == 54 || opcode == 40 || opcode == 13 || opcode == 113 || opcode == 4 || opcode == 2 || opcode == 69 || opcode == 107 || opcode == 12 || opcode == 16 || opcode == 114 || opcode == 27 || opcode == 118 || opcode == 116 || opcode == 0 || opcode == 1 || opcode == 3 || opcode == 14 || opcode == 15 || opcode == 17 || opcode == 208 || opcode == 209 || opcode == 210 || opcode == 26 || opcode == 28 || opcode == 35 || opcode == 36 || opcode == 37 || opcode == 38 || opcode == 41 || opcode == 42 || opcode == 43 || opcode == 44 || opcode == 45 || opcode == 46 || opcode == 47 || opcode == 48 || opcode == 49 || opcode == 50 || opcode == 51 || opcode == 52 || opcode == 53 || opcode == 55 || opcode == 56 || opcode == 57 || opcode == 58 || opcode == 59 || opcode == 60 || opcode == 61 || opcode == 62 || opcode == 63 || opcode == 64 || opcode == 66 || opcode == 67 || opcode == 68 || opcode == 252 || opcode == 253), inner: empty() }))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), mapper: InstrRestMapper::new() })
}


pub struct SpecInstr {
    pub opcode: SpecInstrBytecode,
    pub rest: SpecInstrRest,
}

pub type SpecInstrInner = (SpecInstrBytecode, SpecInstrRest);
impl SpecFrom<SpecInstr> for SpecInstrInner {
    open spec fn spec_from(m: SpecInstr) -> SpecInstrInner {
        (m.opcode, m.rest)
    }
}
impl SpecFrom<SpecInstrInner> for SpecInstr {
    open spec fn spec_from(m: SpecInstrInner) -> SpecInstr {
        let (opcode, rest) = m;
        SpecInstr { opcode, rest }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Instr<'a> {
    pub opcode: InstrBytecode,
    pub rest: InstrRest<'a>,
}

impl View for Instr<'_> {
    type V = SpecInstr;

    open spec fn view(&self) -> Self::V {
        SpecInstr {
            opcode: self.opcode@,
            rest: self.rest@,
        }
    }
}
pub type InstrInner<'a> = (InstrBytecode, InstrRest<'a>);
impl<'a> From<Instr<'a>> for InstrInner<'a> {
    fn ex_from(m: Instr) -> InstrInner {
        (m.opcode, m.rest)
    }
}
impl<'a> From<InstrInner<'a>> for Instr<'a> {
    fn ex_from(m: InstrInner) -> Instr {
        let (opcode, rest) = m;
        Instr { opcode, rest }
    }
}

pub struct InstrMapper<'a>(PhantomData<&'a ()>);
impl<'a> InstrMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        InstrMapper(PhantomData)
    }
    pub fn new() -> Self {
        InstrMapper(PhantomData)
    }
}
impl View for InstrMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrMapper<'_> {
    type Src = SpecInstrInner;
    type Dst = SpecInstr;
}
impl SpecIsoProof for InstrMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for InstrMapper<'a> {
    type Src = InstrInner<'a>;
    type Dst = Instr<'a>;
}

pub struct SpecInstrCombinator(SpecInstrCombinatorAlias);

impl SpecCombinator for SpecInstrCombinator {
    type Type = SpecInstr;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecInstrCombinatorAlias = Mapped<SpecPair<SpecInstrBytecodeCombinator, SpecInstrRestCombinator>, InstrMapper<'static>>;

pub struct InstrCombinator<'a>(InstrCombinatorAlias<'a>);

impl<'a> View for InstrCombinator<'a> {
    type V = SpecInstrCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for InstrCombinator<'a> {
    type Type = Instr<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type InstrCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, InstrBytecodeCombinator, InstrRestCombinator<'a>, InstrCont0<'a>>, InstrMapper<'a>>;


pub closed spec fn spec_instr() -> SpecInstrCombinator {
    SpecInstrCombinator(
    Mapped {
        inner: SpecPair { fst: spec_instr_bytecode(), snd: |deps| spec_instr_cont0(deps) },
        mapper: InstrMapper::spec_new(),
    })
}

pub open spec fn spec_instr_cont0(deps: SpecInstrBytecode) -> SpecInstrRestCombinator {
    let opcode = deps;
    spec_instr_rest(opcode)
}
                
pub fn instr<'a>() -> (o: InstrCombinator<'a>)
    ensures o@ == spec_instr(),
{
    InstrCombinator(
    Mapped {
        inner: Pair { fst: instr_bytecode(), snd: InstrCont0::new(), spec_snd: Ghost(|deps| spec_instr_cont0(deps)) },
        mapper: InstrMapper::new(),
    })
}

pub struct InstrCont0<'a>(PhantomData<&'a ()>);
impl<'a> InstrCont0<'a> {
    pub fn new() -> Self {
        InstrCont0(PhantomData)
    }
}
impl<'a> Continuation<&InstrBytecode> for InstrCont0<'a> {
    type Output = InstrRestCombinator<'a>;

    open spec fn requires(&self, deps: &InstrBytecode) -> bool { true }

    open spec fn ensures(&self, deps: &InstrBytecode, o: Self::Output) -> bool {
        o@ == spec_instr_cont0(deps@)
    }

    fn apply(&self, deps: &InstrBytecode) -> Self::Output {
        let opcode = *deps;
        instr_rest(opcode)
    }
}
                

pub struct SpecExprInner {
    pub l: u64,
    pub v: Seq<SpecInstr>,
}

pub type SpecExprInnerInner = (u64, Seq<SpecInstr>);
impl SpecFrom<SpecExprInner> for SpecExprInnerInner {
    open spec fn spec_from(m: SpecExprInner) -> SpecExprInnerInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecExprInnerInner> for SpecExprInner {
    open spec fn spec_from(m: SpecExprInnerInner) -> SpecExprInner {
        let (l, v) = m;
        SpecExprInner { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ExprInner<'a> {
    pub l: u64,
    pub v: RepeatResult<Instr<'a>>,
}

impl View for ExprInner<'_> {
    type V = SpecExprInner;

    open spec fn view(&self) -> Self::V {
        SpecExprInner {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ExprInnerInner<'a> = (u64, RepeatResult<Instr<'a>>);
impl<'a> From<ExprInner<'a>> for ExprInnerInner<'a> {
    fn ex_from(m: ExprInner) -> ExprInnerInner {
        (m.l, m.v)
    }
}
impl<'a> From<ExprInnerInner<'a>> for ExprInner<'a> {
    fn ex_from(m: ExprInnerInner) -> ExprInner {
        let (l, v) = m;
        ExprInner { l, v }
    }
}

pub struct ExprInnerMapper<'a>(PhantomData<&'a ()>);
impl<'a> ExprInnerMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ExprInnerMapper(PhantomData)
    }
    pub fn new() -> Self {
        ExprInnerMapper(PhantomData)
    }
}
impl View for ExprInnerMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExprInnerMapper<'_> {
    type Src = SpecExprInnerInner;
    type Dst = SpecExprInner;
}
impl SpecIsoProof for ExprInnerMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ExprInnerMapper<'a> {
    type Src = ExprInnerInner<'a>;
    type Dst = ExprInner<'a>;
}

pub struct SpecExprInnerCombinator(SpecExprInnerCombinatorAlias);

impl SpecCombinator for SpecExprInnerCombinator {
    type Type = SpecExprInner;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExprInnerCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExprInnerCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecExprInnerCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecInstrCombinator>>, ExprInnerMapper<'static>>;

pub struct ExprInnerCombinator<'a>(ExprInnerCombinatorAlias<'a>);

impl<'a> View for ExprInnerCombinator<'a> {
    type V = SpecExprInnerCombinator;
    closed spec fn view(&self) -> Self::V { SpecExprInnerCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ExprInnerCombinator<'a> {
    type Type = ExprInner<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ExprInnerCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<InstrCombinator<'a>>, ExprInnerCont0<'a>>, ExprInnerMapper<'a>>;


pub closed spec fn spec_expr_inner() -> SpecExprInnerCombinator {
    SpecExprInnerCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_expr_inner_cont0(deps) },
        mapper: ExprInnerMapper::spec_new(),
    })
}

pub open spec fn spec_expr_inner_cont0(deps: u64) -> RepeatN<SpecInstrCombinator> {
    let l = deps;
    RepeatN(spec_instr(), l.spec_into())
}
                
pub fn expr_inner<'a>() -> (o: ExprInnerCombinator<'a>)
    ensures o@ == spec_expr_inner(),
{
    ExprInnerCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: ExprInnerCont0::new(), spec_snd: Ghost(|deps| spec_expr_inner_cont0(deps)) },
        mapper: ExprInnerMapper::new(),
    })
}

pub struct ExprInnerCont0<'a>(PhantomData<&'a ()>);
impl<'a> ExprInnerCont0<'a> {
    pub fn new() -> Self {
        ExprInnerCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for ExprInnerCont0<'a> {
    type Output = RepeatN<InstrCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_expr_inner_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(instr(), l.ex_into())
    }
}
                
pub type SpecExpr = SpecExprInner;
pub type Expr<'a> = ExprInner<'a>;


pub const Expr_0_BACK_CONST: u8 = 11;

pub struct SpecExprCombinator(SpecExprCombinatorAlias);

impl SpecCombinator for SpecExprCombinator {
    type Type = SpecExpr;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExprCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExprCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecExprCombinatorAlias = Terminated<SpecExprInnerCombinator, Tag<U8, u8>>;


pub struct ExprCombinator<'a>(ExprCombinatorAlias<'a>);

impl<'a> View for ExprCombinator<'a> {
    type V = SpecExprCombinator;
    closed spec fn view(&self) -> Self::V { SpecExprCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ExprCombinator<'a> {
    type Type = Expr<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ExprCombinatorAlias<'a> = Terminated<ExprInnerCombinator<'a>, Tag<U8, u8>>;


pub closed spec fn spec_expr() -> SpecExprCombinator {
    SpecExprCombinator(Terminated(spec_expr_inner(), Tag::spec_new(U8, Expr_0_BACK_CONST)))
}

                
pub fn expr<'a>() -> (o: ExprCombinator<'a>)
    ensures o@ == spec_expr(),
{
    ExprCombinator(Terminated(expr_inner(), Tag::new(U8, Expr_0_BACK_CONST)))
}

                

pub struct SpecFuncidxs {
    pub l: u64,
    pub v: Seq<SpecFuncidx>,
}

pub type SpecFuncidxsInner = (u64, Seq<SpecFuncidx>);
impl SpecFrom<SpecFuncidxs> for SpecFuncidxsInner {
    open spec fn spec_from(m: SpecFuncidxs) -> SpecFuncidxsInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecFuncidxsInner> for SpecFuncidxs {
    open spec fn spec_from(m: SpecFuncidxsInner) -> SpecFuncidxs {
        let (l, v) = m;
        SpecFuncidxs { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Funcidxs {
    pub l: u64,
    pub v: RepeatResult<Funcidx>,
}

impl View for Funcidxs {
    type V = SpecFuncidxs;

    open spec fn view(&self) -> Self::V {
        SpecFuncidxs {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type FuncidxsInner = (u64, RepeatResult<Funcidx>);
impl From<Funcidxs> for FuncidxsInner {
    fn ex_from(m: Funcidxs) -> FuncidxsInner {
        (m.l, m.v)
    }
}
impl From<FuncidxsInner> for Funcidxs {
    fn ex_from(m: FuncidxsInner) -> Funcidxs {
        let (l, v) = m;
        Funcidxs { l, v }
    }
}

pub struct FuncidxsMapper;
impl FuncidxsMapper {
    pub closed spec fn spec_new() -> Self {
        FuncidxsMapper
    }
    pub fn new() -> Self {
        FuncidxsMapper
    }
}
impl View for FuncidxsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FuncidxsMapper {
    type Src = SpecFuncidxsInner;
    type Dst = SpecFuncidxs;
}
impl SpecIsoProof for FuncidxsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for FuncidxsMapper {
    type Src = FuncidxsInner;
    type Dst = Funcidxs;
}

pub struct SpecFuncidxsCombinator(SpecFuncidxsCombinatorAlias);

impl SpecCombinator for SpecFuncidxsCombinator {
    type Type = SpecFuncidxs;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFuncidxsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFuncidxsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecFuncidxsCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecFuncidxCombinator>>, FuncidxsMapper>;

pub struct FuncidxsCombinator<'a>(FuncidxsCombinatorAlias<'a>);

impl<'a> View for FuncidxsCombinator<'a> {
    type V = SpecFuncidxsCombinator;
    closed spec fn view(&self) -> Self::V { SpecFuncidxsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for FuncidxsCombinator<'a> {
    type Type = Funcidxs;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type FuncidxsCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<FuncidxCombinator>, FuncidxsCont0<'a>>, FuncidxsMapper>;


pub closed spec fn spec_funcidxs() -> SpecFuncidxsCombinator {
    SpecFuncidxsCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_funcidxs_cont0(deps) },
        mapper: FuncidxsMapper::spec_new(),
    })
}

pub open spec fn spec_funcidxs_cont0(deps: u64) -> RepeatN<SpecFuncidxCombinator> {
    let l = deps;
    RepeatN(spec_funcidx(), l.spec_into())
}
                
pub fn funcidxs<'a>() -> (o: FuncidxsCombinator<'a>)
    ensures o@ == spec_funcidxs(),
{
    FuncidxsCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: FuncidxsCont0::new(), spec_snd: Ghost(|deps| spec_funcidxs_cont0(deps)) },
        mapper: FuncidxsMapper::new(),
    })
}

pub struct FuncidxsCont0<'a>(PhantomData<&'a ()>);
impl<'a> FuncidxsCont0<'a> {
    pub fn new() -> Self {
        FuncidxsCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for FuncidxsCont0<'a> {
    type Output = RepeatN<FuncidxCombinator>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_funcidxs_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(funcidx(), l.ex_into())
    }
}
                

pub struct SpecParsedElem0 {
    pub e: SpecExpr,
    pub init: SpecFuncidxs,
}

pub type SpecParsedElem0Inner = (SpecExpr, SpecFuncidxs);
impl SpecFrom<SpecParsedElem0> for SpecParsedElem0Inner {
    open spec fn spec_from(m: SpecParsedElem0) -> SpecParsedElem0Inner {
        (m.e, m.init)
    }
}
impl SpecFrom<SpecParsedElem0Inner> for SpecParsedElem0 {
    open spec fn spec_from(m: SpecParsedElem0Inner) -> SpecParsedElem0 {
        let (e, init) = m;
        SpecParsedElem0 { e, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem0<'a> {
    pub e: Expr<'a>,
    pub init: Funcidxs,
}

impl View for ParsedElem0<'_> {
    type V = SpecParsedElem0;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem0 {
            e: self.e@,
            init: self.init@,
        }
    }
}
pub type ParsedElem0Inner<'a> = (Expr<'a>, Funcidxs);
impl<'a> From<ParsedElem0<'a>> for ParsedElem0Inner<'a> {
    fn ex_from(m: ParsedElem0) -> ParsedElem0Inner {
        (m.e, m.init)
    }
}
impl<'a> From<ParsedElem0Inner<'a>> for ParsedElem0<'a> {
    fn ex_from(m: ParsedElem0Inner) -> ParsedElem0 {
        let (e, init) = m;
        ParsedElem0 { e, init }
    }
}

pub struct ParsedElem0Mapper<'a>(PhantomData<&'a ()>);
impl<'a> ParsedElem0Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ParsedElem0Mapper(PhantomData)
    }
    pub fn new() -> Self {
        ParsedElem0Mapper(PhantomData)
    }
}
impl View for ParsedElem0Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem0Mapper<'_> {
    type Src = SpecParsedElem0Inner;
    type Dst = SpecParsedElem0;
}
impl SpecIsoProof for ParsedElem0Mapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ParsedElem0Mapper<'a> {
    type Src = ParsedElem0Inner<'a>;
    type Dst = ParsedElem0<'a>;
}

pub struct SpecParsedElem0Combinator(SpecParsedElem0CombinatorAlias);

impl SpecCombinator for SpecParsedElem0Combinator {
    type Type = SpecParsedElem0;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem0Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem0CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecParsedElem0CombinatorAlias = Mapped<(SpecExprCombinator, SpecFuncidxsCombinator), ParsedElem0Mapper<'static>>;

pub struct ParsedElem0Combinator<'a>(ParsedElem0CombinatorAlias<'a>);

impl<'a> View for ParsedElem0Combinator<'a> {
    type V = SpecParsedElem0Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem0Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ParsedElem0Combinator<'a> {
    type Type = ParsedElem0<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ParsedElem0CombinatorAlias<'a> = Mapped<(ExprCombinator<'a>, FuncidxsCombinator<'a>), ParsedElem0Mapper<'a>>;


pub closed spec fn spec_parsed_elem0() -> SpecParsedElem0Combinator {
    SpecParsedElem0Combinator(
    Mapped {
        inner: (spec_expr(), spec_funcidxs()),
        mapper: ParsedElem0Mapper::spec_new(),
    })
}

                
pub fn parsed_elem0<'a>() -> (o: ParsedElem0Combinator<'a>)
    ensures o@ == spec_parsed_elem0(),
{
    ParsedElem0Combinator(
    Mapped {
        inner: (expr(), funcidxs()),
        mapper: ParsedElem0Mapper::new(),
    })
}

                

pub struct SpecParsedElem1 {
    pub et: SpecELEMKIND,
    pub init: SpecFuncidxs,
}

pub type SpecParsedElem1Inner = (SpecELEMKIND, SpecFuncidxs);
impl SpecFrom<SpecParsedElem1> for SpecParsedElem1Inner {
    open spec fn spec_from(m: SpecParsedElem1) -> SpecParsedElem1Inner {
        (m.et, m.init)
    }
}
impl SpecFrom<SpecParsedElem1Inner> for SpecParsedElem1 {
    open spec fn spec_from(m: SpecParsedElem1Inner) -> SpecParsedElem1 {
        let (et, init) = m;
        SpecParsedElem1 { et, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem1 {
    pub et: ELEMKIND,
    pub init: Funcidxs,
}

impl View for ParsedElem1 {
    type V = SpecParsedElem1;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem1 {
            et: self.et@,
            init: self.init@,
        }
    }
}
pub type ParsedElem1Inner = (ELEMKIND, Funcidxs);
impl From<ParsedElem1> for ParsedElem1Inner {
    fn ex_from(m: ParsedElem1) -> ParsedElem1Inner {
        (m.et, m.init)
    }
}
impl From<ParsedElem1Inner> for ParsedElem1 {
    fn ex_from(m: ParsedElem1Inner) -> ParsedElem1 {
        let (et, init) = m;
        ParsedElem1 { et, init }
    }
}

pub struct ParsedElem1Mapper;
impl ParsedElem1Mapper {
    pub closed spec fn spec_new() -> Self {
        ParsedElem1Mapper
    }
    pub fn new() -> Self {
        ParsedElem1Mapper
    }
}
impl View for ParsedElem1Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem1Mapper {
    type Src = SpecParsedElem1Inner;
    type Dst = SpecParsedElem1;
}
impl SpecIsoProof for ParsedElem1Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ParsedElem1Mapper {
    type Src = ParsedElem1Inner;
    type Dst = ParsedElem1;
}

pub struct SpecParsedElem1Combinator(SpecParsedElem1CombinatorAlias);

impl SpecCombinator for SpecParsedElem1Combinator {
    type Type = SpecParsedElem1;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem1Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem1CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecParsedElem1CombinatorAlias = Mapped<(SpecELEMKINDCombinator, SpecFuncidxsCombinator), ParsedElem1Mapper>;

pub struct ParsedElem1Combinator<'a>(ParsedElem1CombinatorAlias<'a>);

impl<'a> View for ParsedElem1Combinator<'a> {
    type V = SpecParsedElem1Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem1Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ParsedElem1Combinator<'a> {
    type Type = ParsedElem1;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ParsedElem1CombinatorAlias<'a> = Mapped<(ELEMKINDCombinator, FuncidxsCombinator<'a>), ParsedElem1Mapper>;


pub closed spec fn spec_parsed_elem1() -> SpecParsedElem1Combinator {
    SpecParsedElem1Combinator(
    Mapped {
        inner: (spec_ELEMKIND(), spec_funcidxs()),
        mapper: ParsedElem1Mapper::spec_new(),
    })
}

                
pub fn parsed_elem1<'a>() -> (o: ParsedElem1Combinator<'a>)
    ensures o@ == spec_parsed_elem1(),
{
    ParsedElem1Combinator(
    Mapped {
        inner: (ELEMKIND(), funcidxs()),
        mapper: ParsedElem1Mapper::new(),
    })
}

                

pub struct SpecParsedElem2 {
    pub table: SpecTableidx,
    pub offset: SpecExpr,
    pub et: SpecELEMKIND,
    pub init: SpecFuncidxs,
}

pub type SpecParsedElem2Inner = (SpecTableidx, (SpecExpr, (SpecELEMKIND, SpecFuncidxs)));
impl SpecFrom<SpecParsedElem2> for SpecParsedElem2Inner {
    open spec fn spec_from(m: SpecParsedElem2) -> SpecParsedElem2Inner {
        (m.table, (m.offset, (m.et, m.init)))
    }
}
impl SpecFrom<SpecParsedElem2Inner> for SpecParsedElem2 {
    open spec fn spec_from(m: SpecParsedElem2Inner) -> SpecParsedElem2 {
        let (table, (offset, (et, init))) = m;
        SpecParsedElem2 { table, offset, et, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem2<'a> {
    pub table: Tableidx,
    pub offset: Expr<'a>,
    pub et: ELEMKIND,
    pub init: Funcidxs,
}

impl View for ParsedElem2<'_> {
    type V = SpecParsedElem2;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem2 {
            table: self.table@,
            offset: self.offset@,
            et: self.et@,
            init: self.init@,
        }
    }
}
pub type ParsedElem2Inner<'a> = (Tableidx, (Expr<'a>, (ELEMKIND, Funcidxs)));
impl<'a> From<ParsedElem2<'a>> for ParsedElem2Inner<'a> {
    fn ex_from(m: ParsedElem2) -> ParsedElem2Inner {
        (m.table, (m.offset, (m.et, m.init)))
    }
}
impl<'a> From<ParsedElem2Inner<'a>> for ParsedElem2<'a> {
    fn ex_from(m: ParsedElem2Inner) -> ParsedElem2 {
        let (table, (offset, (et, init))) = m;
        ParsedElem2 { table, offset, et, init }
    }
}

pub struct ParsedElem2Mapper<'a>(PhantomData<&'a ()>);
impl<'a> ParsedElem2Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ParsedElem2Mapper(PhantomData)
    }
    pub fn new() -> Self {
        ParsedElem2Mapper(PhantomData)
    }
}
impl View for ParsedElem2Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem2Mapper<'_> {
    type Src = SpecParsedElem2Inner;
    type Dst = SpecParsedElem2;
}
impl SpecIsoProof for ParsedElem2Mapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ParsedElem2Mapper<'a> {
    type Src = ParsedElem2Inner<'a>;
    type Dst = ParsedElem2<'a>;
}

pub struct SpecParsedElem2Combinator(SpecParsedElem2CombinatorAlias);

impl SpecCombinator for SpecParsedElem2Combinator {
    type Type = SpecParsedElem2;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem2Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem2CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecParsedElem2CombinatorAlias = Mapped<(SpecTableidxCombinator, (SpecExprCombinator, (SpecELEMKINDCombinator, SpecFuncidxsCombinator))), ParsedElem2Mapper<'static>>;

pub struct ParsedElem2Combinator<'a>(ParsedElem2CombinatorAlias<'a>);

impl<'a> View for ParsedElem2Combinator<'a> {
    type V = SpecParsedElem2Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem2Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ParsedElem2Combinator<'a> {
    type Type = ParsedElem2<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ParsedElem2CombinatorAlias<'a> = Mapped<(TableidxCombinator, (ExprCombinator<'a>, (ELEMKINDCombinator, FuncidxsCombinator<'a>))), ParsedElem2Mapper<'a>>;


pub closed spec fn spec_parsed_elem2() -> SpecParsedElem2Combinator {
    SpecParsedElem2Combinator(
    Mapped {
        inner: (spec_tableidx(), (spec_expr(), (spec_ELEMKIND(), spec_funcidxs()))),
        mapper: ParsedElem2Mapper::spec_new(),
    })
}

                
pub fn parsed_elem2<'a>() -> (o: ParsedElem2Combinator<'a>)
    ensures o@ == spec_parsed_elem2(),
{
    ParsedElem2Combinator(
    Mapped {
        inner: (tableidx(), (expr(), (ELEMKIND(), funcidxs()))),
        mapper: ParsedElem2Mapper::new(),
    })
}

                
pub type SpecParsedElem3 = SpecParsedElem1;
pub type ParsedElem3 = ParsedElem1;


pub struct SpecParsedElem3Combinator(SpecParsedElem3CombinatorAlias);

impl SpecCombinator for SpecParsedElem3Combinator {
    type Type = SpecParsedElem3;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem3Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem3CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecParsedElem3CombinatorAlias = SpecParsedElem1Combinator;

pub struct ParsedElem3Combinator<'a>(ParsedElem3CombinatorAlias<'a>);

impl<'a> View for ParsedElem3Combinator<'a> {
    type V = SpecParsedElem3Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem3Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ParsedElem3Combinator<'a> {
    type Type = ParsedElem3;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ParsedElem3CombinatorAlias<'a> = ParsedElem1Combinator<'a>;


pub closed spec fn spec_parsed_elem3() -> SpecParsedElem3Combinator {
    SpecParsedElem3Combinator(spec_parsed_elem1())
}

                
pub fn parsed_elem3<'a>() -> (o: ParsedElem3Combinator<'a>)
    ensures o@ == spec_parsed_elem3(),
{
    ParsedElem3Combinator(parsed_elem1())
}

                

pub struct SpecExprs {
    pub l: u64,
    pub v: Seq<SpecExpr>,
}

pub type SpecExprsInner = (u64, Seq<SpecExpr>);
impl SpecFrom<SpecExprs> for SpecExprsInner {
    open spec fn spec_from(m: SpecExprs) -> SpecExprsInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecExprsInner> for SpecExprs {
    open spec fn spec_from(m: SpecExprsInner) -> SpecExprs {
        let (l, v) = m;
        SpecExprs { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Exprs<'a> {
    pub l: u64,
    pub v: RepeatResult<Expr<'a>>,
}

impl View for Exprs<'_> {
    type V = SpecExprs;

    open spec fn view(&self) -> Self::V {
        SpecExprs {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ExprsInner<'a> = (u64, RepeatResult<Expr<'a>>);
impl<'a> From<Exprs<'a>> for ExprsInner<'a> {
    fn ex_from(m: Exprs) -> ExprsInner {
        (m.l, m.v)
    }
}
impl<'a> From<ExprsInner<'a>> for Exprs<'a> {
    fn ex_from(m: ExprsInner) -> Exprs {
        let (l, v) = m;
        Exprs { l, v }
    }
}

pub struct ExprsMapper<'a>(PhantomData<&'a ()>);
impl<'a> ExprsMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ExprsMapper(PhantomData)
    }
    pub fn new() -> Self {
        ExprsMapper(PhantomData)
    }
}
impl View for ExprsMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExprsMapper<'_> {
    type Src = SpecExprsInner;
    type Dst = SpecExprs;
}
impl SpecIsoProof for ExprsMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ExprsMapper<'a> {
    type Src = ExprsInner<'a>;
    type Dst = Exprs<'a>;
}

pub struct SpecExprsCombinator(SpecExprsCombinatorAlias);

impl SpecCombinator for SpecExprsCombinator {
    type Type = SpecExprs;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExprsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExprsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecExprsCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecExprCombinator>>, ExprsMapper<'static>>;

pub struct ExprsCombinator<'a>(ExprsCombinatorAlias<'a>);

impl<'a> View for ExprsCombinator<'a> {
    type V = SpecExprsCombinator;
    closed spec fn view(&self) -> Self::V { SpecExprsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ExprsCombinator<'a> {
    type Type = Exprs<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ExprsCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<ExprCombinator<'a>>, ExprsCont0<'a>>, ExprsMapper<'a>>;


pub closed spec fn spec_exprs() -> SpecExprsCombinator {
    SpecExprsCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_exprs_cont0(deps) },
        mapper: ExprsMapper::spec_new(),
    })
}

pub open spec fn spec_exprs_cont0(deps: u64) -> RepeatN<SpecExprCombinator> {
    let l = deps;
    RepeatN(spec_expr(), l.spec_into())
}
                
pub fn exprs<'a>() -> (o: ExprsCombinator<'a>)
    ensures o@ == spec_exprs(),
{
    ExprsCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: ExprsCont0::new(), spec_snd: Ghost(|deps| spec_exprs_cont0(deps)) },
        mapper: ExprsMapper::new(),
    })
}

pub struct ExprsCont0<'a>(PhantomData<&'a ()>);
impl<'a> ExprsCont0<'a> {
    pub fn new() -> Self {
        ExprsCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for ExprsCont0<'a> {
    type Output = RepeatN<ExprCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_exprs_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(expr(), l.ex_into())
    }
}
                

pub struct SpecParsedElem4 {
    pub offset: SpecExpr,
    pub init: SpecExprs,
}

pub type SpecParsedElem4Inner = (SpecExpr, SpecExprs);
impl SpecFrom<SpecParsedElem4> for SpecParsedElem4Inner {
    open spec fn spec_from(m: SpecParsedElem4) -> SpecParsedElem4Inner {
        (m.offset, m.init)
    }
}
impl SpecFrom<SpecParsedElem4Inner> for SpecParsedElem4 {
    open spec fn spec_from(m: SpecParsedElem4Inner) -> SpecParsedElem4 {
        let (offset, init) = m;
        SpecParsedElem4 { offset, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem4<'a> {
    pub offset: Expr<'a>,
    pub init: Exprs<'a>,
}

impl View for ParsedElem4<'_> {
    type V = SpecParsedElem4;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem4 {
            offset: self.offset@,
            init: self.init@,
        }
    }
}
pub type ParsedElem4Inner<'a> = (Expr<'a>, Exprs<'a>);
impl<'a> From<ParsedElem4<'a>> for ParsedElem4Inner<'a> {
    fn ex_from(m: ParsedElem4) -> ParsedElem4Inner {
        (m.offset, m.init)
    }
}
impl<'a> From<ParsedElem4Inner<'a>> for ParsedElem4<'a> {
    fn ex_from(m: ParsedElem4Inner) -> ParsedElem4 {
        let (offset, init) = m;
        ParsedElem4 { offset, init }
    }
}

pub struct ParsedElem4Mapper<'a>(PhantomData<&'a ()>);
impl<'a> ParsedElem4Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ParsedElem4Mapper(PhantomData)
    }
    pub fn new() -> Self {
        ParsedElem4Mapper(PhantomData)
    }
}
impl View for ParsedElem4Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem4Mapper<'_> {
    type Src = SpecParsedElem4Inner;
    type Dst = SpecParsedElem4;
}
impl SpecIsoProof for ParsedElem4Mapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ParsedElem4Mapper<'a> {
    type Src = ParsedElem4Inner<'a>;
    type Dst = ParsedElem4<'a>;
}

pub struct SpecParsedElem4Combinator(SpecParsedElem4CombinatorAlias);

impl SpecCombinator for SpecParsedElem4Combinator {
    type Type = SpecParsedElem4;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem4Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem4CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecParsedElem4CombinatorAlias = Mapped<(SpecExprCombinator, SpecExprsCombinator), ParsedElem4Mapper<'static>>;

pub struct ParsedElem4Combinator<'a>(ParsedElem4CombinatorAlias<'a>);

impl<'a> View for ParsedElem4Combinator<'a> {
    type V = SpecParsedElem4Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem4Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ParsedElem4Combinator<'a> {
    type Type = ParsedElem4<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ParsedElem4CombinatorAlias<'a> = Mapped<(ExprCombinator<'a>, ExprsCombinator<'a>), ParsedElem4Mapper<'a>>;


pub closed spec fn spec_parsed_elem4() -> SpecParsedElem4Combinator {
    SpecParsedElem4Combinator(
    Mapped {
        inner: (spec_expr(), spec_exprs()),
        mapper: ParsedElem4Mapper::spec_new(),
    })
}

                
pub fn parsed_elem4<'a>() -> (o: ParsedElem4Combinator<'a>)
    ensures o@ == spec_parsed_elem4(),
{
    ParsedElem4Combinator(
    Mapped {
        inner: (expr(), exprs()),
        mapper: ParsedElem4Mapper::new(),
    })
}

                

pub struct SpecParsedElem5 {
    pub et: SpecReftype,
    pub init: SpecExprs,
}

pub type SpecParsedElem5Inner = (SpecReftype, SpecExprs);
impl SpecFrom<SpecParsedElem5> for SpecParsedElem5Inner {
    open spec fn spec_from(m: SpecParsedElem5) -> SpecParsedElem5Inner {
        (m.et, m.init)
    }
}
impl SpecFrom<SpecParsedElem5Inner> for SpecParsedElem5 {
    open spec fn spec_from(m: SpecParsedElem5Inner) -> SpecParsedElem5 {
        let (et, init) = m;
        SpecParsedElem5 { et, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem5<'a> {
    pub et: Reftype,
    pub init: Exprs<'a>,
}

impl View for ParsedElem5<'_> {
    type V = SpecParsedElem5;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem5 {
            et: self.et@,
            init: self.init@,
        }
    }
}
pub type ParsedElem5Inner<'a> = (Reftype, Exprs<'a>);
impl<'a> From<ParsedElem5<'a>> for ParsedElem5Inner<'a> {
    fn ex_from(m: ParsedElem5) -> ParsedElem5Inner {
        (m.et, m.init)
    }
}
impl<'a> From<ParsedElem5Inner<'a>> for ParsedElem5<'a> {
    fn ex_from(m: ParsedElem5Inner) -> ParsedElem5 {
        let (et, init) = m;
        ParsedElem5 { et, init }
    }
}

pub struct ParsedElem5Mapper<'a>(PhantomData<&'a ()>);
impl<'a> ParsedElem5Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ParsedElem5Mapper(PhantomData)
    }
    pub fn new() -> Self {
        ParsedElem5Mapper(PhantomData)
    }
}
impl View for ParsedElem5Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem5Mapper<'_> {
    type Src = SpecParsedElem5Inner;
    type Dst = SpecParsedElem5;
}
impl SpecIsoProof for ParsedElem5Mapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ParsedElem5Mapper<'a> {
    type Src = ParsedElem5Inner<'a>;
    type Dst = ParsedElem5<'a>;
}

pub struct SpecParsedElem5Combinator(SpecParsedElem5CombinatorAlias);

impl SpecCombinator for SpecParsedElem5Combinator {
    type Type = SpecParsedElem5;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem5Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem5CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecParsedElem5CombinatorAlias = Mapped<(SpecReftypeCombinator, SpecExprsCombinator), ParsedElem5Mapper<'static>>;

pub struct ParsedElem5Combinator<'a>(ParsedElem5CombinatorAlias<'a>);

impl<'a> View for ParsedElem5Combinator<'a> {
    type V = SpecParsedElem5Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem5Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ParsedElem5Combinator<'a> {
    type Type = ParsedElem5<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ParsedElem5CombinatorAlias<'a> = Mapped<(ReftypeCombinator, ExprsCombinator<'a>), ParsedElem5Mapper<'a>>;


pub closed spec fn spec_parsed_elem5() -> SpecParsedElem5Combinator {
    SpecParsedElem5Combinator(
    Mapped {
        inner: (spec_reftype(), spec_exprs()),
        mapper: ParsedElem5Mapper::spec_new(),
    })
}

                
pub fn parsed_elem5<'a>() -> (o: ParsedElem5Combinator<'a>)
    ensures o@ == spec_parsed_elem5(),
{
    ParsedElem5Combinator(
    Mapped {
        inner: (reftype(), exprs()),
        mapper: ParsedElem5Mapper::new(),
    })
}

                

pub struct SpecParsedElem6 {
    pub table: SpecTableidx,
    pub offset: SpecExpr,
    pub et: SpecReftype,
    pub init: SpecExprs,
}

pub type SpecParsedElem6Inner = (SpecTableidx, (SpecExpr, (SpecReftype, SpecExprs)));
impl SpecFrom<SpecParsedElem6> for SpecParsedElem6Inner {
    open spec fn spec_from(m: SpecParsedElem6) -> SpecParsedElem6Inner {
        (m.table, (m.offset, (m.et, m.init)))
    }
}
impl SpecFrom<SpecParsedElem6Inner> for SpecParsedElem6 {
    open spec fn spec_from(m: SpecParsedElem6Inner) -> SpecParsedElem6 {
        let (table, (offset, (et, init))) = m;
        SpecParsedElem6 { table, offset, et, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem6<'a> {
    pub table: Tableidx,
    pub offset: Expr<'a>,
    pub et: Reftype,
    pub init: Exprs<'a>,
}

impl View for ParsedElem6<'_> {
    type V = SpecParsedElem6;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem6 {
            table: self.table@,
            offset: self.offset@,
            et: self.et@,
            init: self.init@,
        }
    }
}
pub type ParsedElem6Inner<'a> = (Tableidx, (Expr<'a>, (Reftype, Exprs<'a>)));
impl<'a> From<ParsedElem6<'a>> for ParsedElem6Inner<'a> {
    fn ex_from(m: ParsedElem6) -> ParsedElem6Inner {
        (m.table, (m.offset, (m.et, m.init)))
    }
}
impl<'a> From<ParsedElem6Inner<'a>> for ParsedElem6<'a> {
    fn ex_from(m: ParsedElem6Inner) -> ParsedElem6 {
        let (table, (offset, (et, init))) = m;
        ParsedElem6 { table, offset, et, init }
    }
}

pub struct ParsedElem6Mapper<'a>(PhantomData<&'a ()>);
impl<'a> ParsedElem6Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ParsedElem6Mapper(PhantomData)
    }
    pub fn new() -> Self {
        ParsedElem6Mapper(PhantomData)
    }
}
impl View for ParsedElem6Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem6Mapper<'_> {
    type Src = SpecParsedElem6Inner;
    type Dst = SpecParsedElem6;
}
impl SpecIsoProof for ParsedElem6Mapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ParsedElem6Mapper<'a> {
    type Src = ParsedElem6Inner<'a>;
    type Dst = ParsedElem6<'a>;
}

pub struct SpecParsedElem6Combinator(SpecParsedElem6CombinatorAlias);

impl SpecCombinator for SpecParsedElem6Combinator {
    type Type = SpecParsedElem6;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem6Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem6CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecParsedElem6CombinatorAlias = Mapped<(SpecTableidxCombinator, (SpecExprCombinator, (SpecReftypeCombinator, SpecExprsCombinator))), ParsedElem6Mapper<'static>>;

pub struct ParsedElem6Combinator<'a>(ParsedElem6CombinatorAlias<'a>);

impl<'a> View for ParsedElem6Combinator<'a> {
    type V = SpecParsedElem6Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem6Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ParsedElem6Combinator<'a> {
    type Type = ParsedElem6<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ParsedElem6CombinatorAlias<'a> = Mapped<(TableidxCombinator, (ExprCombinator<'a>, (ReftypeCombinator, ExprsCombinator<'a>))), ParsedElem6Mapper<'a>>;


pub closed spec fn spec_parsed_elem6() -> SpecParsedElem6Combinator {
    SpecParsedElem6Combinator(
    Mapped {
        inner: (spec_tableidx(), (spec_expr(), (spec_reftype(), spec_exprs()))),
        mapper: ParsedElem6Mapper::spec_new(),
    })
}

                
pub fn parsed_elem6<'a>() -> (o: ParsedElem6Combinator<'a>)
    ensures o@ == spec_parsed_elem6(),
{
    ParsedElem6Combinator(
    Mapped {
        inner: (tableidx(), (expr(), (reftype(), exprs()))),
        mapper: ParsedElem6Mapper::new(),
    })
}

                

pub struct SpecParsedElem7 {
    pub et: SpecReftype,
    pub init: SpecExprs,
}

pub type SpecParsedElem7Inner = (SpecReftype, SpecExprs);
impl SpecFrom<SpecParsedElem7> for SpecParsedElem7Inner {
    open spec fn spec_from(m: SpecParsedElem7) -> SpecParsedElem7Inner {
        (m.et, m.init)
    }
}
impl SpecFrom<SpecParsedElem7Inner> for SpecParsedElem7 {
    open spec fn spec_from(m: SpecParsedElem7Inner) -> SpecParsedElem7 {
        let (et, init) = m;
        SpecParsedElem7 { et, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem7<'a> {
    pub et: Reftype,
    pub init: Exprs<'a>,
}

impl View for ParsedElem7<'_> {
    type V = SpecParsedElem7;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem7 {
            et: self.et@,
            init: self.init@,
        }
    }
}
pub type ParsedElem7Inner<'a> = (Reftype, Exprs<'a>);
impl<'a> From<ParsedElem7<'a>> for ParsedElem7Inner<'a> {
    fn ex_from(m: ParsedElem7) -> ParsedElem7Inner {
        (m.et, m.init)
    }
}
impl<'a> From<ParsedElem7Inner<'a>> for ParsedElem7<'a> {
    fn ex_from(m: ParsedElem7Inner) -> ParsedElem7 {
        let (et, init) = m;
        ParsedElem7 { et, init }
    }
}

pub struct ParsedElem7Mapper<'a>(PhantomData<&'a ()>);
impl<'a> ParsedElem7Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ParsedElem7Mapper(PhantomData)
    }
    pub fn new() -> Self {
        ParsedElem7Mapper(PhantomData)
    }
}
impl View for ParsedElem7Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem7Mapper<'_> {
    type Src = SpecParsedElem7Inner;
    type Dst = SpecParsedElem7;
}
impl SpecIsoProof for ParsedElem7Mapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ParsedElem7Mapper<'a> {
    type Src = ParsedElem7Inner<'a>;
    type Dst = ParsedElem7<'a>;
}

pub struct SpecParsedElem7Combinator(SpecParsedElem7CombinatorAlias);

impl SpecCombinator for SpecParsedElem7Combinator {
    type Type = SpecParsedElem7;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem7Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem7CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecParsedElem7CombinatorAlias = Mapped<(SpecReftypeCombinator, SpecExprsCombinator), ParsedElem7Mapper<'static>>;

pub struct ParsedElem7Combinator<'a>(ParsedElem7CombinatorAlias<'a>);

impl<'a> View for ParsedElem7Combinator<'a> {
    type V = SpecParsedElem7Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem7Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ParsedElem7Combinator<'a> {
    type Type = ParsedElem7<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ParsedElem7CombinatorAlias<'a> = Mapped<(ReftypeCombinator, ExprsCombinator<'a>), ParsedElem7Mapper<'a>>;


pub closed spec fn spec_parsed_elem7() -> SpecParsedElem7Combinator {
    SpecParsedElem7Combinator(
    Mapped {
        inner: (spec_reftype(), spec_exprs()),
        mapper: ParsedElem7Mapper::spec_new(),
    })
}

                
pub fn parsed_elem7<'a>() -> (o: ParsedElem7Combinator<'a>)
    ensures o@ == spec_parsed_elem7(),
{
    ParsedElem7Combinator(
    Mapped {
        inner: (reftype(), exprs()),
        mapper: ParsedElem7Mapper::new(),
    })
}

                

pub enum SpecElem {
    Elem0(SpecParsedElem0),
    Elem1(SpecParsedElem1),
    Elem2(SpecParsedElem2),
    Elem3(SpecParsedElem3),
    Elem4(SpecParsedElem4),
    Elem5(SpecParsedElem5),
    Elem6(SpecParsedElem6),
    Elem7(SpecParsedElem7),
}

pub type SpecElemInner = Either<SpecParsedElem0, Either<SpecParsedElem1, Either<SpecParsedElem2, Either<SpecParsedElem3, Either<SpecParsedElem4, Either<SpecParsedElem5, Either<SpecParsedElem6, SpecParsedElem7>>>>>>>;



impl SpecFrom<SpecElem> for SpecElemInner {
    open spec fn spec_from(m: SpecElem) -> SpecElemInner {
        match m {
            SpecElem::Elem0(m) => Either::Left(m),
            SpecElem::Elem1(m) => Either::Right(Either::Left(m)),
            SpecElem::Elem2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecElem::Elem3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecElem::Elem4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecElem::Elem5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecElem::Elem6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecElem::Elem7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))),
        }
    }

}

impl SpecFrom<SpecElemInner> for SpecElem {
    open spec fn spec_from(m: SpecElemInner) -> SpecElem {
        match m {
            Either::Left(m) => SpecElem::Elem0(m),
            Either::Right(Either::Left(m)) => SpecElem::Elem1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecElem::Elem2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecElem::Elem3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecElem::Elem4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecElem::Elem5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecElem::Elem6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))) => SpecElem::Elem7(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Elem<'a> {
    Elem0(ParsedElem0<'a>),
    Elem1(ParsedElem1),
    Elem2(ParsedElem2<'a>),
    Elem3(ParsedElem3),
    Elem4(ParsedElem4<'a>),
    Elem5(ParsedElem5<'a>),
    Elem6(ParsedElem6<'a>),
    Elem7(ParsedElem7<'a>),
}

pub type ElemInner<'a> = Either<ParsedElem0<'a>, Either<ParsedElem1, Either<ParsedElem2<'a>, Either<ParsedElem3, Either<ParsedElem4<'a>, Either<ParsedElem5<'a>, Either<ParsedElem6<'a>, ParsedElem7<'a>>>>>>>>;


impl<'a> View for Elem<'a> {
    type V = SpecElem;
    open spec fn view(&self) -> Self::V {
        match self {
            Elem::Elem0(m) => SpecElem::Elem0(m@),
            Elem::Elem1(m) => SpecElem::Elem1(m@),
            Elem::Elem2(m) => SpecElem::Elem2(m@),
            Elem::Elem3(m) => SpecElem::Elem3(m@),
            Elem::Elem4(m) => SpecElem::Elem4(m@),
            Elem::Elem5(m) => SpecElem::Elem5(m@),
            Elem::Elem6(m) => SpecElem::Elem6(m@),
            Elem::Elem7(m) => SpecElem::Elem7(m@),
        }
    }
}


impl<'a> From<Elem<'a>> for ElemInner<'a> {
    fn ex_from(m: Elem<'a>) -> ElemInner<'a> {
        match m {
            Elem::Elem0(m) => Either::Left(m),
            Elem::Elem1(m) => Either::Right(Either::Left(m)),
            Elem::Elem2(m) => Either::Right(Either::Right(Either::Left(m))),
            Elem::Elem3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            Elem::Elem4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            Elem::Elem5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            Elem::Elem6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            Elem::Elem7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))),
        }
    }

}

impl<'a> From<ElemInner<'a>> for Elem<'a> {
    fn ex_from(m: ElemInner<'a>) -> Elem<'a> {
        match m {
            Either::Left(m) => Elem::Elem0(m),
            Either::Right(Either::Left(m)) => Elem::Elem1(m),
            Either::Right(Either::Right(Either::Left(m))) => Elem::Elem2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => Elem::Elem3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => Elem::Elem4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => Elem::Elem5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => Elem::Elem6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))) => Elem::Elem7(m),
        }
    }
    
}


pub struct ElemMapper<'a>(PhantomData<&'a ()>);
impl<'a> ElemMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ElemMapper(PhantomData)
    }
    pub fn new() -> Self {
        ElemMapper(PhantomData)
    }
}
impl View for ElemMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ElemMapper<'_> {
    type Src = SpecElemInner;
    type Dst = SpecElem;
}
impl SpecIsoProof for ElemMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ElemMapper<'a> {
    type Src = ElemInner<'a>;
    type Dst = Elem<'a>;
}

pub const ELEMELEM0_0_FRONT_CONST: u64 = 0;

pub const ELEMELEM1_0_FRONT_CONST: u64 = 1;

pub const ELEMELEM2_0_FRONT_CONST: u64 = 2;

pub const ELEMELEM3_0_FRONT_CONST: u64 = 3;

pub const ELEMELEM4_0_FRONT_CONST: u64 = 4;

pub const ELEMELEM5_0_FRONT_CONST: u64 = 5;

pub const ELEMELEM6_0_FRONT_CONST: u64 = 6;

pub const ELEMELEM7_0_FRONT_CONST: u64 = 7;


pub struct SpecElemCombinator(SpecElemCombinatorAlias);

impl SpecCombinator for SpecElemCombinator {
    type Type = SpecElem;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecElemCombinatorAlias = Mapped<Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem0Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem1Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem2Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem3Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem4Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem5Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem6Combinator>, Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem7Combinator>>>>>>>>, ElemMapper<'static>>;









pub struct ElemCombinator<'a>(ElemCombinatorAlias<'a>);

impl<'a> View for ElemCombinator<'a> {
    type V = SpecElemCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ElemCombinator<'a> {
    type Type = Elem<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ElemCombinatorAlias<'a> = Mapped<Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem0Combinator<'a>>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem1Combinator<'a>>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem2Combinator<'a>>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem3Combinator<'a>>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem4Combinator<'a>>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem5Combinator<'a>>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem6Combinator<'a>>, Preceded<Tag<UnsignedLEB128, u64>, ParsedElem7Combinator<'a>>>>>>>>>, ElemMapper<'a>>;


pub closed spec fn spec_elem() -> SpecElemCombinator {
    SpecElemCombinator(Mapped { inner: Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM0_0_FRONT_CONST), spec_parsed_elem0()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM1_0_FRONT_CONST), spec_parsed_elem1()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM2_0_FRONT_CONST), spec_parsed_elem2()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM3_0_FRONT_CONST), spec_parsed_elem3()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM4_0_FRONT_CONST), spec_parsed_elem4()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM5_0_FRONT_CONST), spec_parsed_elem5()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM6_0_FRONT_CONST), spec_parsed_elem6()), Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM7_0_FRONT_CONST), spec_parsed_elem7())))))))), mapper: ElemMapper::spec_new() })
}

                
pub fn elem<'a>() -> (o: ElemCombinator<'a>)
    ensures o@ == spec_elem(),
{
    ElemCombinator(Mapped { inner: Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM0_0_FRONT_CONST), parsed_elem0()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM1_0_FRONT_CONST), parsed_elem1()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM2_0_FRONT_CONST), parsed_elem2()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM3_0_FRONT_CONST), parsed_elem3()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM4_0_FRONT_CONST), parsed_elem4()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM5_0_FRONT_CONST), parsed_elem5()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM6_0_FRONT_CONST), parsed_elem6()), Preceded(Tag::new(UnsignedLEB128, ELEMELEM7_0_FRONT_CONST), parsed_elem7())))))))), mapper: ElemMapper::new() })
}

                

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum MutT {
    Const = 0,
Var = 1
}
pub type SpecMutT = MutT;

pub type MutTInner = u8;

impl View for MutT {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<MutTInner> for MutT {
    type Error = ();

    open spec fn spec_try_from(v: MutTInner) -> Result<MutT, ()> {
        match v {
            0u8 => Ok(MutT::Const),
            1u8 => Ok(MutT::Var),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<MutT> for MutTInner {
    type Error = ();

    open spec fn spec_try_from(v: MutT) -> Result<MutTInner, ()> {
        match v {
            MutT::Const => Ok(0u8),
            MutT::Var => Ok(1u8),
        }
    }
}

impl TryFrom<MutTInner> for MutT {
    type Error = ();

    fn ex_try_from(v: MutTInner) -> Result<MutT, ()> {
        match v {
            0u8 => Ok(MutT::Const),
            1u8 => Ok(MutT::Var),
            _ => Err(()),
        }
    }
}

impl TryFrom<MutT> for MutTInner {
    type Error = ();

    fn ex_try_from(v: MutT) -> Result<MutTInner, ()> {
        match v {
            MutT::Const => Ok(0u8),
            MutT::Var => Ok(1u8),
        }
    }
}

pub struct MutTMapper;

impl View for MutTMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for MutTMapper {
    type Src = MutTInner;
    type Dst = MutT;
}

impl SpecPartialIsoProof for MutTMapper {
    proof fn spec_iso(s: Self::Src) { 
        assert(
            Self::spec_apply(s) matches Ok(v) ==> {
            &&& Self::spec_rev_apply(v) is Ok
            &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
        });
    }

    proof fn spec_iso_rev(s: Self::Dst) { 
        assert(
            Self::spec_rev_apply(s) matches Ok(v) ==> {
            &&& Self::spec_apply(v) is Ok
            &&& Self::spec_apply(v) matches Ok(s_) && s == s_
        });
    }
}

impl PartialIso for MutTMapper {
    type Src = MutTInner;
    type Dst = MutT;
}


pub struct SpecMutTCombinator(SpecMutTCombinatorAlias);

impl SpecCombinator for SpecMutTCombinator {
    type Type = SpecMutT;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMutTCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMutTCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMutTCombinatorAlias = TryMap<U8, MutTMapper>;

pub struct MutTCombinator(MutTCombinatorAlias);

impl View for MutTCombinator {
    type V = SpecMutTCombinator;
    closed spec fn view(&self) -> Self::V { SpecMutTCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MutTCombinator {
    type Type = MutT;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MutTCombinatorAlias = TryMap<U8, MutTMapper>;


pub closed spec fn spec_mut_t() -> SpecMutTCombinator {
    SpecMutTCombinator(TryMap { inner: U8, mapper: MutTMapper })
}

                
pub fn mut_t() -> (o: MutTCombinator)
    ensures o@ == spec_mut_t(),
{
    MutTCombinator(TryMap { inner: U8, mapper: MutTMapper })
}

                

pub struct SpecGlobaltype {
    pub t: SpecValtype,
    pub m: SpecMutT,
}

pub type SpecGlobaltypeInner = (SpecValtype, SpecMutT);
impl SpecFrom<SpecGlobaltype> for SpecGlobaltypeInner {
    open spec fn spec_from(m: SpecGlobaltype) -> SpecGlobaltypeInner {
        (m.t, m.m)
    }
}
impl SpecFrom<SpecGlobaltypeInner> for SpecGlobaltype {
    open spec fn spec_from(m: SpecGlobaltypeInner) -> SpecGlobaltype {
        let (t, m) = m;
        SpecGlobaltype { t, m }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Globaltype {
    pub t: Valtype,
    pub m: MutT,
}

impl View for Globaltype {
    type V = SpecGlobaltype;

    open spec fn view(&self) -> Self::V {
        SpecGlobaltype {
            t: self.t@,
            m: self.m@,
        }
    }
}
pub type GlobaltypeInner = (Valtype, MutT);
impl From<Globaltype> for GlobaltypeInner {
    fn ex_from(m: Globaltype) -> GlobaltypeInner {
        (m.t, m.m)
    }
}
impl From<GlobaltypeInner> for Globaltype {
    fn ex_from(m: GlobaltypeInner) -> Globaltype {
        let (t, m) = m;
        Globaltype { t, m }
    }
}

pub struct GlobaltypeMapper;
impl GlobaltypeMapper {
    pub closed spec fn spec_new() -> Self {
        GlobaltypeMapper
    }
    pub fn new() -> Self {
        GlobaltypeMapper
    }
}
impl View for GlobaltypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for GlobaltypeMapper {
    type Src = SpecGlobaltypeInner;
    type Dst = SpecGlobaltype;
}
impl SpecIsoProof for GlobaltypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for GlobaltypeMapper {
    type Src = GlobaltypeInner;
    type Dst = Globaltype;
}

pub struct SpecGlobaltypeCombinator(SpecGlobaltypeCombinatorAlias);

impl SpecCombinator for SpecGlobaltypeCombinator {
    type Type = SpecGlobaltype;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGlobaltypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecGlobaltypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecGlobaltypeCombinatorAlias = Mapped<(SpecValtypeCombinator, SpecMutTCombinator), GlobaltypeMapper>;

pub struct GlobaltypeCombinator(GlobaltypeCombinatorAlias);

impl View for GlobaltypeCombinator {
    type V = SpecGlobaltypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecGlobaltypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for GlobaltypeCombinator {
    type Type = Globaltype;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type GlobaltypeCombinatorAlias = Mapped<(ValtypeCombinator, MutTCombinator), GlobaltypeMapper>;


pub closed spec fn spec_globaltype() -> SpecGlobaltypeCombinator {
    SpecGlobaltypeCombinator(
    Mapped {
        inner: (spec_valtype(), spec_mut_t()),
        mapper: GlobaltypeMapper::spec_new(),
    })
}

                
pub fn globaltype() -> (o: GlobaltypeCombinator)
    ensures o@ == spec_globaltype(),
{
    GlobaltypeCombinator(
    Mapped {
        inner: (valtype(), mut_t()),
        mapper: GlobaltypeMapper::new(),
    })
}

                

pub struct SpecGlobal {
    pub gt: SpecGlobaltype,
    pub init: SpecExpr,
}

pub type SpecGlobalInner = (SpecGlobaltype, SpecExpr);
impl SpecFrom<SpecGlobal> for SpecGlobalInner {
    open spec fn spec_from(m: SpecGlobal) -> SpecGlobalInner {
        (m.gt, m.init)
    }
}
impl SpecFrom<SpecGlobalInner> for SpecGlobal {
    open spec fn spec_from(m: SpecGlobalInner) -> SpecGlobal {
        let (gt, init) = m;
        SpecGlobal { gt, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Global<'a> {
    pub gt: Globaltype,
    pub init: Expr<'a>,
}

impl View for Global<'_> {
    type V = SpecGlobal;

    open spec fn view(&self) -> Self::V {
        SpecGlobal {
            gt: self.gt@,
            init: self.init@,
        }
    }
}
pub type GlobalInner<'a> = (Globaltype, Expr<'a>);
impl<'a> From<Global<'a>> for GlobalInner<'a> {
    fn ex_from(m: Global) -> GlobalInner {
        (m.gt, m.init)
    }
}
impl<'a> From<GlobalInner<'a>> for Global<'a> {
    fn ex_from(m: GlobalInner) -> Global {
        let (gt, init) = m;
        Global { gt, init }
    }
}

pub struct GlobalMapper<'a>(PhantomData<&'a ()>);
impl<'a> GlobalMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        GlobalMapper(PhantomData)
    }
    pub fn new() -> Self {
        GlobalMapper(PhantomData)
    }
}
impl View for GlobalMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for GlobalMapper<'_> {
    type Src = SpecGlobalInner;
    type Dst = SpecGlobal;
}
impl SpecIsoProof for GlobalMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for GlobalMapper<'a> {
    type Src = GlobalInner<'a>;
    type Dst = Global<'a>;
}

pub struct SpecGlobalCombinator(SpecGlobalCombinatorAlias);

impl SpecCombinator for SpecGlobalCombinator {
    type Type = SpecGlobal;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGlobalCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecGlobalCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecGlobalCombinatorAlias = Mapped<(SpecGlobaltypeCombinator, SpecExprCombinator), GlobalMapper<'static>>;

pub struct GlobalCombinator<'a>(GlobalCombinatorAlias<'a>);

impl<'a> View for GlobalCombinator<'a> {
    type V = SpecGlobalCombinator;
    closed spec fn view(&self) -> Self::V { SpecGlobalCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for GlobalCombinator<'a> {
    type Type = Global<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type GlobalCombinatorAlias<'a> = Mapped<(GlobaltypeCombinator, ExprCombinator<'a>), GlobalMapper<'a>>;


pub closed spec fn spec_global() -> SpecGlobalCombinator {
    SpecGlobalCombinator(
    Mapped {
        inner: (spec_globaltype(), spec_expr()),
        mapper: GlobalMapper::spec_new(),
    })
}

                
pub fn global<'a>() -> (o: GlobalCombinator<'a>)
    ensures o@ == spec_global(),
{
    GlobalCombinator(
    Mapped {
        inner: (globaltype(), expr()),
        mapper: GlobalMapper::new(),
    })
}

                

pub struct SpecGlobalsecContent {
    pub l: u64,
    pub v: Seq<SpecGlobal>,
}

pub type SpecGlobalsecContentInner = (u64, Seq<SpecGlobal>);
impl SpecFrom<SpecGlobalsecContent> for SpecGlobalsecContentInner {
    open spec fn spec_from(m: SpecGlobalsecContent) -> SpecGlobalsecContentInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecGlobalsecContentInner> for SpecGlobalsecContent {
    open spec fn spec_from(m: SpecGlobalsecContentInner) -> SpecGlobalsecContent {
        let (l, v) = m;
        SpecGlobalsecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct GlobalsecContent<'a> {
    pub l: u64,
    pub v: RepeatResult<Global<'a>>,
}

impl View for GlobalsecContent<'_> {
    type V = SpecGlobalsecContent;

    open spec fn view(&self) -> Self::V {
        SpecGlobalsecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type GlobalsecContentInner<'a> = (u64, RepeatResult<Global<'a>>);
impl<'a> From<GlobalsecContent<'a>> for GlobalsecContentInner<'a> {
    fn ex_from(m: GlobalsecContent) -> GlobalsecContentInner {
        (m.l, m.v)
    }
}
impl<'a> From<GlobalsecContentInner<'a>> for GlobalsecContent<'a> {
    fn ex_from(m: GlobalsecContentInner) -> GlobalsecContent {
        let (l, v) = m;
        GlobalsecContent { l, v }
    }
}

pub struct GlobalsecContentMapper<'a>(PhantomData<&'a ()>);
impl<'a> GlobalsecContentMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        GlobalsecContentMapper(PhantomData)
    }
    pub fn new() -> Self {
        GlobalsecContentMapper(PhantomData)
    }
}
impl View for GlobalsecContentMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for GlobalsecContentMapper<'_> {
    type Src = SpecGlobalsecContentInner;
    type Dst = SpecGlobalsecContent;
}
impl SpecIsoProof for GlobalsecContentMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for GlobalsecContentMapper<'a> {
    type Src = GlobalsecContentInner<'a>;
    type Dst = GlobalsecContent<'a>;
}

pub struct SpecGlobalsecContentCombinator(SpecGlobalsecContentCombinatorAlias);

impl SpecCombinator for SpecGlobalsecContentCombinator {
    type Type = SpecGlobalsecContent;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGlobalsecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecGlobalsecContentCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecGlobalsecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecGlobalCombinator>>, GlobalsecContentMapper<'static>>;

pub struct GlobalsecContentCombinator<'a>(GlobalsecContentCombinatorAlias<'a>);

impl<'a> View for GlobalsecContentCombinator<'a> {
    type V = SpecGlobalsecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecGlobalsecContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for GlobalsecContentCombinator<'a> {
    type Type = GlobalsecContent<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type GlobalsecContentCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<GlobalCombinator<'a>>, GlobalsecContentCont0<'a>>, GlobalsecContentMapper<'a>>;


pub closed spec fn spec_globalsec_content() -> SpecGlobalsecContentCombinator {
    SpecGlobalsecContentCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_globalsec_content_cont0(deps) },
        mapper: GlobalsecContentMapper::spec_new(),
    })
}

pub open spec fn spec_globalsec_content_cont0(deps: u64) -> RepeatN<SpecGlobalCombinator> {
    let l = deps;
    RepeatN(spec_global(), l.spec_into())
}
                
pub fn globalsec_content<'a>() -> (o: GlobalsecContentCombinator<'a>)
    ensures o@ == spec_globalsec_content(),
{
    GlobalsecContentCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: GlobalsecContentCont0::new(), spec_snd: Ghost(|deps| spec_globalsec_content_cont0(deps)) },
        mapper: GlobalsecContentMapper::new(),
    })
}

pub struct GlobalsecContentCont0<'a>(PhantomData<&'a ()>);
impl<'a> GlobalsecContentCont0<'a> {
    pub fn new() -> Self {
        GlobalsecContentCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for GlobalsecContentCont0<'a> {
    type Output = RepeatN<GlobalCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_globalsec_content_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(global(), l.ex_into())
    }
}
                

pub struct SpecLimitMin {
    pub min: u64,
}

pub type SpecLimitMinInner = u64;
impl SpecFrom<SpecLimitMin> for SpecLimitMinInner {
    open spec fn spec_from(m: SpecLimitMin) -> SpecLimitMinInner {
        m.min
    }
}
impl SpecFrom<SpecLimitMinInner> for SpecLimitMin {
    open spec fn spec_from(m: SpecLimitMinInner) -> SpecLimitMin {
        let min = m;
        SpecLimitMin { min }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct LimitMin {
    pub min: u64,
}

impl View for LimitMin {
    type V = SpecLimitMin;

    open spec fn view(&self) -> Self::V {
        SpecLimitMin {
            min: self.min@,
        }
    }
}
pub type LimitMinInner = u64;
impl From<LimitMin> for LimitMinInner {
    fn ex_from(m: LimitMin) -> LimitMinInner {
        m.min
    }
}
impl From<LimitMinInner> for LimitMin {
    fn ex_from(m: LimitMinInner) -> LimitMin {
        let min = m;
        LimitMin { min }
    }
}

pub struct LimitMinMapper;
impl LimitMinMapper {
    pub closed spec fn spec_new() -> Self {
        LimitMinMapper
    }
    pub fn new() -> Self {
        LimitMinMapper
    }
}
impl View for LimitMinMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LimitMinMapper {
    type Src = SpecLimitMinInner;
    type Dst = SpecLimitMin;
}
impl SpecIsoProof for LimitMinMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for LimitMinMapper {
    type Src = LimitMinInner;
    type Dst = LimitMin;
}

pub struct SpecLimitMinCombinator(SpecLimitMinCombinatorAlias);

impl SpecCombinator for SpecLimitMinCombinator {
    type Type = SpecLimitMin;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLimitMinCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLimitMinCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecLimitMinCombinatorAlias = Mapped<UnsignedLEB128, LimitMinMapper>;

pub struct LimitMinCombinator(LimitMinCombinatorAlias);

impl View for LimitMinCombinator {
    type V = SpecLimitMinCombinator;
    closed spec fn view(&self) -> Self::V { SpecLimitMinCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for LimitMinCombinator {
    type Type = LimitMin;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type LimitMinCombinatorAlias = Mapped<UnsignedLEB128, LimitMinMapper>;


pub closed spec fn spec_limit_min() -> SpecLimitMinCombinator {
    SpecLimitMinCombinator(
    Mapped {
        inner: UnsignedLEB128,
        mapper: LimitMinMapper::spec_new(),
    })
}

                
pub fn limit_min() -> (o: LimitMinCombinator)
    ensures o@ == spec_limit_min(),
{
    LimitMinCombinator(
    Mapped {
        inner: UnsignedLEB128,
        mapper: LimitMinMapper::new(),
    })
}

                

pub struct SpecLimitMinMax {
    pub min: u64,
    pub max: u64,
}

pub type SpecLimitMinMaxInner = (u64, u64);
impl SpecFrom<SpecLimitMinMax> for SpecLimitMinMaxInner {
    open spec fn spec_from(m: SpecLimitMinMax) -> SpecLimitMinMaxInner {
        (m.min, m.max)
    }
}
impl SpecFrom<SpecLimitMinMaxInner> for SpecLimitMinMax {
    open spec fn spec_from(m: SpecLimitMinMaxInner) -> SpecLimitMinMax {
        let (min, max) = m;
        SpecLimitMinMax { min, max }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct LimitMinMax {
    pub min: u64,
    pub max: u64,
}

impl View for LimitMinMax {
    type V = SpecLimitMinMax;

    open spec fn view(&self) -> Self::V {
        SpecLimitMinMax {
            min: self.min@,
            max: self.max@,
        }
    }
}
pub type LimitMinMaxInner = (u64, u64);
impl From<LimitMinMax> for LimitMinMaxInner {
    fn ex_from(m: LimitMinMax) -> LimitMinMaxInner {
        (m.min, m.max)
    }
}
impl From<LimitMinMaxInner> for LimitMinMax {
    fn ex_from(m: LimitMinMaxInner) -> LimitMinMax {
        let (min, max) = m;
        LimitMinMax { min, max }
    }
}

pub struct LimitMinMaxMapper;
impl LimitMinMaxMapper {
    pub closed spec fn spec_new() -> Self {
        LimitMinMaxMapper
    }
    pub fn new() -> Self {
        LimitMinMaxMapper
    }
}
impl View for LimitMinMaxMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LimitMinMaxMapper {
    type Src = SpecLimitMinMaxInner;
    type Dst = SpecLimitMinMax;
}
impl SpecIsoProof for LimitMinMaxMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for LimitMinMaxMapper {
    type Src = LimitMinMaxInner;
    type Dst = LimitMinMax;
}

pub struct SpecLimitMinMaxCombinator(SpecLimitMinMaxCombinatorAlias);

impl SpecCombinator for SpecLimitMinMaxCombinator {
    type Type = SpecLimitMinMax;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLimitMinMaxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLimitMinMaxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecLimitMinMaxCombinatorAlias = Mapped<(UnsignedLEB128, UnsignedLEB128), LimitMinMaxMapper>;

pub struct LimitMinMaxCombinator(LimitMinMaxCombinatorAlias);

impl View for LimitMinMaxCombinator {
    type V = SpecLimitMinMaxCombinator;
    closed spec fn view(&self) -> Self::V { SpecLimitMinMaxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for LimitMinMaxCombinator {
    type Type = LimitMinMax;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type LimitMinMaxCombinatorAlias = Mapped<(UnsignedLEB128, UnsignedLEB128), LimitMinMaxMapper>;


pub closed spec fn spec_limit_min_max() -> SpecLimitMinMaxCombinator {
    SpecLimitMinMaxCombinator(
    Mapped {
        inner: (UnsignedLEB128, UnsignedLEB128),
        mapper: LimitMinMaxMapper::spec_new(),
    })
}

                
pub fn limit_min_max() -> (o: LimitMinMaxCombinator)
    ensures o@ == spec_limit_min_max(),
{
    LimitMinMaxCombinator(
    Mapped {
        inner: (UnsignedLEB128, UnsignedLEB128),
        mapper: LimitMinMaxMapper::new(),
    })
}

                

pub enum SpecLimits {
    NoMax(SpecLimitMin),
    Max(SpecLimitMinMax),
}

pub type SpecLimitsInner = Either<SpecLimitMin, SpecLimitMinMax>;



impl SpecFrom<SpecLimits> for SpecLimitsInner {
    open spec fn spec_from(m: SpecLimits) -> SpecLimitsInner {
        match m {
            SpecLimits::NoMax(m) => Either::Left(m),
            SpecLimits::Max(m) => Either::Right(m),
        }
    }

}

impl SpecFrom<SpecLimitsInner> for SpecLimits {
    open spec fn spec_from(m: SpecLimitsInner) -> SpecLimits {
        match m {
            Either::Left(m) => SpecLimits::NoMax(m),
            Either::Right(m) => SpecLimits::Max(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Limits {
    NoMax(LimitMin),
    Max(LimitMinMax),
}

pub type LimitsInner = Either<LimitMin, LimitMinMax>;


impl View for Limits {
    type V = SpecLimits;
    open spec fn view(&self) -> Self::V {
        match self {
            Limits::NoMax(m) => SpecLimits::NoMax(m@),
            Limits::Max(m) => SpecLimits::Max(m@),
        }
    }
}


impl From<Limits> for LimitsInner {
    fn ex_from(m: Limits) -> LimitsInner {
        match m {
            Limits::NoMax(m) => Either::Left(m),
            Limits::Max(m) => Either::Right(m),
        }
    }

}

impl From<LimitsInner> for Limits {
    fn ex_from(m: LimitsInner) -> Limits {
        match m {
            Either::Left(m) => Limits::NoMax(m),
            Either::Right(m) => Limits::Max(m),
        }
    }
    
}


pub struct LimitsMapper;
impl LimitsMapper {
    pub closed spec fn spec_new() -> Self {
        LimitsMapper
    }
    pub fn new() -> Self {
        LimitsMapper
    }
}
impl View for LimitsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LimitsMapper {
    type Src = SpecLimitsInner;
    type Dst = SpecLimits;
}
impl SpecIsoProof for LimitsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for LimitsMapper {
    type Src = LimitsInner;
    type Dst = Limits;
}

pub const LIMITSNOMAX_0_FRONT_CONST: u8 = 0;

pub const LIMITSMAX_0_FRONT_CONST: u8 = 1;


pub struct SpecLimitsCombinator(SpecLimitsCombinatorAlias);

impl SpecCombinator for SpecLimitsCombinator {
    type Type = SpecLimits;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLimitsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLimitsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecLimitsCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, SpecLimitMinCombinator>, Preceded<Tag<U8, u8>, SpecLimitMinMaxCombinator>>, LimitsMapper>;



pub struct LimitsCombinator(LimitsCombinatorAlias);

impl View for LimitsCombinator {
    type V = SpecLimitsCombinator;
    closed spec fn view(&self) -> Self::V { SpecLimitsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for LimitsCombinator {
    type Type = Limits;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type LimitsCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, LimitMinCombinator>, Preceded<Tag<U8, u8>, LimitMinMaxCombinator>>, LimitsMapper>;


pub closed spec fn spec_limits() -> SpecLimitsCombinator {
    SpecLimitsCombinator(Mapped { inner: Choice(Preceded(Tag::spec_new(U8, LIMITSNOMAX_0_FRONT_CONST), spec_limit_min()), Preceded(Tag::spec_new(U8, LIMITSMAX_0_FRONT_CONST), spec_limit_min_max())), mapper: LimitsMapper::spec_new() })
}

                
pub fn limits() -> (o: LimitsCombinator)
    ensures o@ == spec_limits(),
{
    LimitsCombinator(Mapped { inner: Choice::new(Preceded(Tag::new(U8, LIMITSNOMAX_0_FRONT_CONST), limit_min()), Preceded(Tag::new(U8, LIMITSMAX_0_FRONT_CONST), limit_min_max())), mapper: LimitsMapper::new() })
}

                

pub struct SpecTabletype {
    pub elemtype: SpecReftype,
    pub limits: SpecLimits,
}

pub type SpecTabletypeInner = (SpecReftype, SpecLimits);
impl SpecFrom<SpecTabletype> for SpecTabletypeInner {
    open spec fn spec_from(m: SpecTabletype) -> SpecTabletypeInner {
        (m.elemtype, m.limits)
    }
}
impl SpecFrom<SpecTabletypeInner> for SpecTabletype {
    open spec fn spec_from(m: SpecTabletypeInner) -> SpecTabletype {
        let (elemtype, limits) = m;
        SpecTabletype { elemtype, limits }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Tabletype {
    pub elemtype: Reftype,
    pub limits: Limits,
}

impl View for Tabletype {
    type V = SpecTabletype;

    open spec fn view(&self) -> Self::V {
        SpecTabletype {
            elemtype: self.elemtype@,
            limits: self.limits@,
        }
    }
}
pub type TabletypeInner = (Reftype, Limits);
impl From<Tabletype> for TabletypeInner {
    fn ex_from(m: Tabletype) -> TabletypeInner {
        (m.elemtype, m.limits)
    }
}
impl From<TabletypeInner> for Tabletype {
    fn ex_from(m: TabletypeInner) -> Tabletype {
        let (elemtype, limits) = m;
        Tabletype { elemtype, limits }
    }
}

pub struct TabletypeMapper;
impl TabletypeMapper {
    pub closed spec fn spec_new() -> Self {
        TabletypeMapper
    }
    pub fn new() -> Self {
        TabletypeMapper
    }
}
impl View for TabletypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TabletypeMapper {
    type Src = SpecTabletypeInner;
    type Dst = SpecTabletype;
}
impl SpecIsoProof for TabletypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for TabletypeMapper {
    type Src = TabletypeInner;
    type Dst = Tabletype;
}

pub struct SpecTabletypeCombinator(SpecTabletypeCombinatorAlias);

impl SpecCombinator for SpecTabletypeCombinator {
    type Type = SpecTabletype;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTabletypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTabletypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTabletypeCombinatorAlias = Mapped<(SpecReftypeCombinator, SpecLimitsCombinator), TabletypeMapper>;

pub struct TabletypeCombinator(TabletypeCombinatorAlias);

impl View for TabletypeCombinator {
    type V = SpecTabletypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecTabletypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TabletypeCombinator {
    type Type = Tabletype;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TabletypeCombinatorAlias = Mapped<(ReftypeCombinator, LimitsCombinator), TabletypeMapper>;


pub closed spec fn spec_tabletype() -> SpecTabletypeCombinator {
    SpecTabletypeCombinator(
    Mapped {
        inner: (spec_reftype(), spec_limits()),
        mapper: TabletypeMapper::spec_new(),
    })
}

                
pub fn tabletype() -> (o: TabletypeCombinator)
    ensures o@ == spec_tabletype(),
{
    TabletypeCombinator(
    Mapped {
        inner: (reftype(), limits()),
        mapper: TabletypeMapper::new(),
    })
}

                

pub struct SpecTable {
    pub ty: SpecTabletype,
}

pub type SpecTableInner = SpecTabletype;
impl SpecFrom<SpecTable> for SpecTableInner {
    open spec fn spec_from(m: SpecTable) -> SpecTableInner {
        m.ty
    }
}
impl SpecFrom<SpecTableInner> for SpecTable {
    open spec fn spec_from(m: SpecTableInner) -> SpecTable {
        let ty = m;
        SpecTable { ty }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Table {
    pub ty: Tabletype,
}

impl View for Table {
    type V = SpecTable;

    open spec fn view(&self) -> Self::V {
        SpecTable {
            ty: self.ty@,
        }
    }
}
pub type TableInner = Tabletype;
impl From<Table> for TableInner {
    fn ex_from(m: Table) -> TableInner {
        m.ty
    }
}
impl From<TableInner> for Table {
    fn ex_from(m: TableInner) -> Table {
        let ty = m;
        Table { ty }
    }
}

pub struct TableMapper;
impl TableMapper {
    pub closed spec fn spec_new() -> Self {
        TableMapper
    }
    pub fn new() -> Self {
        TableMapper
    }
}
impl View for TableMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TableMapper {
    type Src = SpecTableInner;
    type Dst = SpecTable;
}
impl SpecIsoProof for TableMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for TableMapper {
    type Src = TableInner;
    type Dst = Table;
}

pub struct SpecTableCombinator(SpecTableCombinatorAlias);

impl SpecCombinator for SpecTableCombinator {
    type Type = SpecTable;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTableCombinatorAlias = Mapped<SpecTabletypeCombinator, TableMapper>;

pub struct TableCombinator(TableCombinatorAlias);

impl View for TableCombinator {
    type V = SpecTableCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TableCombinator {
    type Type = Table;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TableCombinatorAlias = Mapped<TabletypeCombinator, TableMapper>;


pub closed spec fn spec_table() -> SpecTableCombinator {
    SpecTableCombinator(
    Mapped {
        inner: spec_tabletype(),
        mapper: TableMapper::spec_new(),
    })
}

                
pub fn table() -> (o: TableCombinator)
    ensures o@ == spec_table(),
{
    TableCombinator(
    Mapped {
        inner: tabletype(),
        mapper: TableMapper::new(),
    })
}

                

pub struct SpecTablesecContent {
    pub l: u64,
    pub v: Seq<SpecTable>,
}

pub type SpecTablesecContentInner = (u64, Seq<SpecTable>);
impl SpecFrom<SpecTablesecContent> for SpecTablesecContentInner {
    open spec fn spec_from(m: SpecTablesecContent) -> SpecTablesecContentInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecTablesecContentInner> for SpecTablesecContent {
    open spec fn spec_from(m: SpecTablesecContentInner) -> SpecTablesecContent {
        let (l, v) = m;
        SpecTablesecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TablesecContent {
    pub l: u64,
    pub v: RepeatResult<Table>,
}

impl View for TablesecContent {
    type V = SpecTablesecContent;

    open spec fn view(&self) -> Self::V {
        SpecTablesecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type TablesecContentInner = (u64, RepeatResult<Table>);
impl From<TablesecContent> for TablesecContentInner {
    fn ex_from(m: TablesecContent) -> TablesecContentInner {
        (m.l, m.v)
    }
}
impl From<TablesecContentInner> for TablesecContent {
    fn ex_from(m: TablesecContentInner) -> TablesecContent {
        let (l, v) = m;
        TablesecContent { l, v }
    }
}

pub struct TablesecContentMapper;
impl TablesecContentMapper {
    pub closed spec fn spec_new() -> Self {
        TablesecContentMapper
    }
    pub fn new() -> Self {
        TablesecContentMapper
    }
}
impl View for TablesecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TablesecContentMapper {
    type Src = SpecTablesecContentInner;
    type Dst = SpecTablesecContent;
}
impl SpecIsoProof for TablesecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for TablesecContentMapper {
    type Src = TablesecContentInner;
    type Dst = TablesecContent;
}

pub struct SpecTablesecContentCombinator(SpecTablesecContentCombinatorAlias);

impl SpecCombinator for SpecTablesecContentCombinator {
    type Type = SpecTablesecContent;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTablesecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTablesecContentCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTablesecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecTableCombinator>>, TablesecContentMapper>;

pub struct TablesecContentCombinator<'a>(TablesecContentCombinatorAlias<'a>);

impl<'a> View for TablesecContentCombinator<'a> {
    type V = SpecTablesecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecTablesecContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TablesecContentCombinator<'a> {
    type Type = TablesecContent;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TablesecContentCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<TableCombinator>, TablesecContentCont0<'a>>, TablesecContentMapper>;


pub closed spec fn spec_tablesec_content() -> SpecTablesecContentCombinator {
    SpecTablesecContentCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_tablesec_content_cont0(deps) },
        mapper: TablesecContentMapper::spec_new(),
    })
}

pub open spec fn spec_tablesec_content_cont0(deps: u64) -> RepeatN<SpecTableCombinator> {
    let l = deps;
    RepeatN(spec_table(), l.spec_into())
}
                
pub fn tablesec_content<'a>() -> (o: TablesecContentCombinator<'a>)
    ensures o@ == spec_tablesec_content(),
{
    TablesecContentCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: TablesecContentCont0::new(), spec_snd: Ghost(|deps| spec_tablesec_content_cont0(deps)) },
        mapper: TablesecContentMapper::new(),
    })
}

pub struct TablesecContentCont0<'a>(PhantomData<&'a ()>);
impl<'a> TablesecContentCont0<'a> {
    pub fn new() -> Self {
        TablesecContentCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for TablesecContentCont0<'a> {
    type Output = RepeatN<TableCombinator>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_tablesec_content_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(table(), l.ex_into())
    }
}
                
pub type SpecELEMKIND = u8;
pub type ELEMKIND = u8;

pub const ELEMKIND_CONST: u8 = 0;
pub type SpecELEMKINDCombinator = Refined<U8, TagPred<u8>>;
pub type ELEMKINDCombinator = Refined<U8, TagPred<u8>>;


pub closed spec fn spec_ELEMKIND() -> SpecELEMKINDCombinator {
    Refined { inner: U8, predicate: TagPred(ELEMKIND_CONST) }
}

pub fn ELEMKIND() -> (o: ELEMKINDCombinator)
    ensures o@ == spec_ELEMKIND(),
{
    Refined { inner: U8, predicate: TagPred(ELEMKIND_CONST) }
}


pub struct SpecByteVec {
    pub l: u64,
    pub v: Seq<u8>,
}

pub type SpecByteVecInner = (u64, Seq<u8>);
impl SpecFrom<SpecByteVec> for SpecByteVecInner {
    open spec fn spec_from(m: SpecByteVec) -> SpecByteVecInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecByteVecInner> for SpecByteVec {
    open spec fn spec_from(m: SpecByteVecInner) -> SpecByteVec {
        let (l, v) = m;
        SpecByteVec { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ByteVec {
    pub l: u64,
    pub v: RepeatResult<u8>,
}

impl View for ByteVec {
    type V = SpecByteVec;

    open spec fn view(&self) -> Self::V {
        SpecByteVec {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ByteVecInner = (u64, RepeatResult<u8>);
impl From<ByteVec> for ByteVecInner {
    fn ex_from(m: ByteVec) -> ByteVecInner {
        (m.l, m.v)
    }
}
impl From<ByteVecInner> for ByteVec {
    fn ex_from(m: ByteVecInner) -> ByteVec {
        let (l, v) = m;
        ByteVec { l, v }
    }
}

pub struct ByteVecMapper;
impl ByteVecMapper {
    pub closed spec fn spec_new() -> Self {
        ByteVecMapper
    }
    pub fn new() -> Self {
        ByteVecMapper
    }
}
impl View for ByteVecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ByteVecMapper {
    type Src = SpecByteVecInner;
    type Dst = SpecByteVec;
}
impl SpecIsoProof for ByteVecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ByteVecMapper {
    type Src = ByteVecInner;
    type Dst = ByteVec;
}

pub struct SpecByteVecCombinator(SpecByteVecCombinatorAlias);

impl SpecCombinator for SpecByteVecCombinator {
    type Type = SpecByteVec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecByteVecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecByteVecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecByteVecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<U8>>, ByteVecMapper>;

pub struct ByteVecCombinator<'a>(ByteVecCombinatorAlias<'a>);

impl<'a> View for ByteVecCombinator<'a> {
    type V = SpecByteVecCombinator;
    closed spec fn view(&self) -> Self::V { SpecByteVecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ByteVecCombinator<'a> {
    type Type = ByteVec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ByteVecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<U8>, ByteVecCont0<'a>>, ByteVecMapper>;


pub closed spec fn spec_byte_vec() -> SpecByteVecCombinator {
    SpecByteVecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_byte_vec_cont0(deps) },
        mapper: ByteVecMapper::spec_new(),
    })
}

pub open spec fn spec_byte_vec_cont0(deps: u64) -> RepeatN<U8> {
    let l = deps;
    RepeatN(U8, l.spec_into())
}
                
pub fn byte_vec<'a>() -> (o: ByteVecCombinator<'a>)
    ensures o@ == spec_byte_vec(),
{
    ByteVecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: ByteVecCont0::new(), spec_snd: Ghost(|deps| spec_byte_vec_cont0(deps)) },
        mapper: ByteVecMapper::new(),
    })
}

pub struct ByteVecCont0<'a>(PhantomData<&'a ()>);
impl<'a> ByteVecCont0<'a> {
    pub fn new() -> Self {
        ByteVecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for ByteVecCont0<'a> {
    type Output = RepeatN<U8>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_byte_vec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(U8, l.ex_into())
    }
}
                
pub type SpecName = SpecByteVec;
pub type Name = ByteVec;


pub struct SpecNameCombinator(SpecNameCombinatorAlias);

impl SpecCombinator for SpecNameCombinator {
    type Type = SpecName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecNameCombinatorAlias = SpecByteVecCombinator;

pub struct NameCombinator<'a>(NameCombinatorAlias<'a>);

impl<'a> View for NameCombinator<'a> {
    type V = SpecNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecNameCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NameCombinator<'a> {
    type Type = Name;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NameCombinatorAlias<'a> = ByteVecCombinator<'a>;


pub closed spec fn spec_name() -> SpecNameCombinator {
    SpecNameCombinator(spec_byte_vec())
}

                
pub fn name<'a>() -> (o: NameCombinator<'a>)
    ensures o@ == spec_name(),
{
    NameCombinator(byte_vec())
}

                
pub type SpecMemtype = SpecLimits;
pub type Memtype = Limits;


pub struct SpecMemtypeCombinator(SpecMemtypeCombinatorAlias);

impl SpecCombinator for SpecMemtypeCombinator {
    type Type = SpecMemtype;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemtypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemtypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMemtypeCombinatorAlias = SpecLimitsCombinator;

pub struct MemtypeCombinator(MemtypeCombinatorAlias);

impl View for MemtypeCombinator {
    type V = SpecMemtypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemtypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MemtypeCombinator {
    type Type = Memtype;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MemtypeCombinatorAlias = LimitsCombinator;


pub closed spec fn spec_memtype() -> SpecMemtypeCombinator {
    SpecMemtypeCombinator(spec_limits())
}

                
pub fn memtype() -> (o: MemtypeCombinator)
    ensures o@ == spec_memtype(),
{
    MemtypeCombinator(limits())
}

                

pub enum SpecImportdesc {
    Func(SpecTypeidx),
    Table(SpecTabletype),
    Mem(SpecMemtype),
    Global(SpecGlobaltype),
}

pub type SpecImportdescInner = Either<SpecTypeidx, Either<SpecTabletype, Either<SpecMemtype, SpecGlobaltype>>>;



impl SpecFrom<SpecImportdesc> for SpecImportdescInner {
    open spec fn spec_from(m: SpecImportdesc) -> SpecImportdescInner {
        match m {
            SpecImportdesc::Func(m) => Either::Left(m),
            SpecImportdesc::Table(m) => Either::Right(Either::Left(m)),
            SpecImportdesc::Mem(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecImportdesc::Global(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl SpecFrom<SpecImportdescInner> for SpecImportdesc {
    open spec fn spec_from(m: SpecImportdescInner) -> SpecImportdesc {
        match m {
            Either::Left(m) => SpecImportdesc::Func(m),
            Either::Right(Either::Left(m)) => SpecImportdesc::Table(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecImportdesc::Mem(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecImportdesc::Global(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Importdesc {
    Func(Typeidx),
    Table(Tabletype),
    Mem(Memtype),
    Global(Globaltype),
}

pub type ImportdescInner = Either<Typeidx, Either<Tabletype, Either<Memtype, Globaltype>>>;


impl View for Importdesc {
    type V = SpecImportdesc;
    open spec fn view(&self) -> Self::V {
        match self {
            Importdesc::Func(m) => SpecImportdesc::Func(m@),
            Importdesc::Table(m) => SpecImportdesc::Table(m@),
            Importdesc::Mem(m) => SpecImportdesc::Mem(m@),
            Importdesc::Global(m) => SpecImportdesc::Global(m@),
        }
    }
}


impl From<Importdesc> for ImportdescInner {
    fn ex_from(m: Importdesc) -> ImportdescInner {
        match m {
            Importdesc::Func(m) => Either::Left(m),
            Importdesc::Table(m) => Either::Right(Either::Left(m)),
            Importdesc::Mem(m) => Either::Right(Either::Right(Either::Left(m))),
            Importdesc::Global(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl From<ImportdescInner> for Importdesc {
    fn ex_from(m: ImportdescInner) -> Importdesc {
        match m {
            Either::Left(m) => Importdesc::Func(m),
            Either::Right(Either::Left(m)) => Importdesc::Table(m),
            Either::Right(Either::Right(Either::Left(m))) => Importdesc::Mem(m),
            Either::Right(Either::Right(Either::Right(m))) => Importdesc::Global(m),
        }
    }
    
}


pub struct ImportdescMapper;
impl ImportdescMapper {
    pub closed spec fn spec_new() -> Self {
        ImportdescMapper
    }
    pub fn new() -> Self {
        ImportdescMapper
    }
}
impl View for ImportdescMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ImportdescMapper {
    type Src = SpecImportdescInner;
    type Dst = SpecImportdesc;
}
impl SpecIsoProof for ImportdescMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ImportdescMapper {
    type Src = ImportdescInner;
    type Dst = Importdesc;
}

pub const IMPORTDESCFUNC_0_FRONT_CONST: u8 = 0;

pub const IMPORTDESCTABLE_0_FRONT_CONST: u8 = 1;

pub const IMPORTDESCMEM_0_FRONT_CONST: u8 = 2;

pub const IMPORTDESCGLOBAL_0_FRONT_CONST: u8 = 3;


pub struct SpecImportdescCombinator(SpecImportdescCombinatorAlias);

impl SpecCombinator for SpecImportdescCombinator {
    type Type = SpecImportdesc;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecImportdescCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecImportdescCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecImportdescCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, SpecTypeidxCombinator>, Choice<Preceded<Tag<U8, u8>, SpecTabletypeCombinator>, Choice<Preceded<Tag<U8, u8>, SpecMemtypeCombinator>, Preceded<Tag<U8, u8>, SpecGlobaltypeCombinator>>>>, ImportdescMapper>;





pub struct ImportdescCombinator(ImportdescCombinatorAlias);

impl View for ImportdescCombinator {
    type V = SpecImportdescCombinator;
    closed spec fn view(&self) -> Self::V { SpecImportdescCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ImportdescCombinator {
    type Type = Importdesc;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ImportdescCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, TypeidxCombinator>, Choice<Preceded<Tag<U8, u8>, TabletypeCombinator>, Choice<Preceded<Tag<U8, u8>, MemtypeCombinator>, Preceded<Tag<U8, u8>, GlobaltypeCombinator>>>>, ImportdescMapper>;


pub closed spec fn spec_importdesc() -> SpecImportdescCombinator {
    SpecImportdescCombinator(Mapped { inner: Choice(Preceded(Tag::spec_new(U8, IMPORTDESCFUNC_0_FRONT_CONST), spec_typeidx()), Choice(Preceded(Tag::spec_new(U8, IMPORTDESCTABLE_0_FRONT_CONST), spec_tabletype()), Choice(Preceded(Tag::spec_new(U8, IMPORTDESCMEM_0_FRONT_CONST), spec_memtype()), Preceded(Tag::spec_new(U8, IMPORTDESCGLOBAL_0_FRONT_CONST), spec_globaltype())))), mapper: ImportdescMapper::spec_new() })
}

                
pub fn importdesc() -> (o: ImportdescCombinator)
    ensures o@ == spec_importdesc(),
{
    ImportdescCombinator(Mapped { inner: Choice::new(Preceded(Tag::new(U8, IMPORTDESCFUNC_0_FRONT_CONST), typeidx()), Choice::new(Preceded(Tag::new(U8, IMPORTDESCTABLE_0_FRONT_CONST), tabletype()), Choice::new(Preceded(Tag::new(U8, IMPORTDESCMEM_0_FRONT_CONST), memtype()), Preceded(Tag::new(U8, IMPORTDESCGLOBAL_0_FRONT_CONST), globaltype())))), mapper: ImportdescMapper::new() })
}

                

pub struct SpecImport {
    pub module: SpecName,
    pub name: SpecName,
    pub desc: SpecImportdesc,
}

pub type SpecImportInner = (SpecName, (SpecName, SpecImportdesc));
impl SpecFrom<SpecImport> for SpecImportInner {
    open spec fn spec_from(m: SpecImport) -> SpecImportInner {
        (m.module, (m.name, m.desc))
    }
}
impl SpecFrom<SpecImportInner> for SpecImport {
    open spec fn spec_from(m: SpecImportInner) -> SpecImport {
        let (module, (name, desc)) = m;
        SpecImport { module, name, desc }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Import {
    pub module: Name,
    pub name: Name,
    pub desc: Importdesc,
}

impl View for Import {
    type V = SpecImport;

    open spec fn view(&self) -> Self::V {
        SpecImport {
            module: self.module@,
            name: self.name@,
            desc: self.desc@,
        }
    }
}
pub type ImportInner = (Name, (Name, Importdesc));
impl From<Import> for ImportInner {
    fn ex_from(m: Import) -> ImportInner {
        (m.module, (m.name, m.desc))
    }
}
impl From<ImportInner> for Import {
    fn ex_from(m: ImportInner) -> Import {
        let (module, (name, desc)) = m;
        Import { module, name, desc }
    }
}

pub struct ImportMapper;
impl ImportMapper {
    pub closed spec fn spec_new() -> Self {
        ImportMapper
    }
    pub fn new() -> Self {
        ImportMapper
    }
}
impl View for ImportMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ImportMapper {
    type Src = SpecImportInner;
    type Dst = SpecImport;
}
impl SpecIsoProof for ImportMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ImportMapper {
    type Src = ImportInner;
    type Dst = Import;
}

pub struct SpecImportCombinator(SpecImportCombinatorAlias);

impl SpecCombinator for SpecImportCombinator {
    type Type = SpecImport;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecImportCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecImportCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecImportCombinatorAlias = Mapped<(SpecNameCombinator, (SpecNameCombinator, SpecImportdescCombinator)), ImportMapper>;

pub struct ImportCombinator<'a>(ImportCombinatorAlias<'a>);

impl<'a> View for ImportCombinator<'a> {
    type V = SpecImportCombinator;
    closed spec fn view(&self) -> Self::V { SpecImportCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ImportCombinator<'a> {
    type Type = Import;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ImportCombinatorAlias<'a> = Mapped<(NameCombinator<'a>, (NameCombinator<'a>, ImportdescCombinator)), ImportMapper>;


pub closed spec fn spec_import() -> SpecImportCombinator {
    SpecImportCombinator(
    Mapped {
        inner: (spec_name(), (spec_name(), spec_importdesc())),
        mapper: ImportMapper::spec_new(),
    })
}

                
pub fn import<'a>() -> (o: ImportCombinator<'a>)
    ensures o@ == spec_import(),
{
    ImportCombinator(
    Mapped {
        inner: (name(), (name(), importdesc())),
        mapper: ImportMapper::new(),
    })
}

                

pub struct SpecImports {
    pub l: u64,
    pub v: Seq<SpecImport>,
}

pub type SpecImportsInner = (u64, Seq<SpecImport>);
impl SpecFrom<SpecImports> for SpecImportsInner {
    open spec fn spec_from(m: SpecImports) -> SpecImportsInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecImportsInner> for SpecImports {
    open spec fn spec_from(m: SpecImportsInner) -> SpecImports {
        let (l, v) = m;
        SpecImports { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Imports {
    pub l: u64,
    pub v: RepeatResult<Import>,
}

impl View for Imports {
    type V = SpecImports;

    open spec fn view(&self) -> Self::V {
        SpecImports {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ImportsInner = (u64, RepeatResult<Import>);
impl From<Imports> for ImportsInner {
    fn ex_from(m: Imports) -> ImportsInner {
        (m.l, m.v)
    }
}
impl From<ImportsInner> for Imports {
    fn ex_from(m: ImportsInner) -> Imports {
        let (l, v) = m;
        Imports { l, v }
    }
}

pub struct ImportsMapper;
impl ImportsMapper {
    pub closed spec fn spec_new() -> Self {
        ImportsMapper
    }
    pub fn new() -> Self {
        ImportsMapper
    }
}
impl View for ImportsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ImportsMapper {
    type Src = SpecImportsInner;
    type Dst = SpecImports;
}
impl SpecIsoProof for ImportsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ImportsMapper {
    type Src = ImportsInner;
    type Dst = Imports;
}

pub struct SpecImportsCombinator(SpecImportsCombinatorAlias);

impl SpecCombinator for SpecImportsCombinator {
    type Type = SpecImports;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecImportsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecImportsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecImportsCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecImportCombinator>>, ImportsMapper>;

pub struct ImportsCombinator<'a>(ImportsCombinatorAlias<'a>);

impl<'a> View for ImportsCombinator<'a> {
    type V = SpecImportsCombinator;
    closed spec fn view(&self) -> Self::V { SpecImportsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ImportsCombinator<'a> {
    type Type = Imports;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ImportsCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<ImportCombinator<'a>>, ImportsCont0<'a>>, ImportsMapper>;


pub closed spec fn spec_imports() -> SpecImportsCombinator {
    SpecImportsCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_imports_cont0(deps) },
        mapper: ImportsMapper::spec_new(),
    })
}

pub open spec fn spec_imports_cont0(deps: u64) -> RepeatN<SpecImportCombinator> {
    let l = deps;
    RepeatN(spec_import(), l.spec_into())
}
                
pub fn imports<'a>() -> (o: ImportsCombinator<'a>)
    ensures o@ == spec_imports(),
{
    ImportsCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: ImportsCont0::new(), spec_snd: Ghost(|deps| spec_imports_cont0(deps)) },
        mapper: ImportsMapper::new(),
    })
}

pub struct ImportsCont0<'a>(PhantomData<&'a ()>);
impl<'a> ImportsCont0<'a> {
    pub fn new() -> Self {
        ImportsCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for ImportsCont0<'a> {
    type Output = RepeatN<ImportCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_imports_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(import(), l.ex_into())
    }
}
                
pub type SpecMemidx = u64;
pub type Memidx = u64;


pub struct SpecMemidxCombinator(SpecMemidxCombinatorAlias);

impl SpecCombinator for SpecMemidxCombinator {
    type Type = SpecMemidx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemidxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMemidxCombinatorAlias = UnsignedLEB128;

pub struct MemidxCombinator(MemidxCombinatorAlias);

impl View for MemidxCombinator {
    type V = SpecMemidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemidxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MemidxCombinator {
    type Type = Memidx;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MemidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_memidx() -> SpecMemidxCombinator {
    SpecMemidxCombinator(UnsignedLEB128)
}

                
pub fn memidx() -> (o: MemidxCombinator)
    ensures o@ == spec_memidx(),
{
    MemidxCombinator(UnsignedLEB128)
}

                

pub struct SpecActiveDatax {
    pub memory: SpecMemidx,
    pub offset: SpecExpr,
    pub init: SpecByteVec,
}

pub type SpecActiveDataxInner = (SpecMemidx, (SpecExpr, SpecByteVec));
impl SpecFrom<SpecActiveDatax> for SpecActiveDataxInner {
    open spec fn spec_from(m: SpecActiveDatax) -> SpecActiveDataxInner {
        (m.memory, (m.offset, m.init))
    }
}
impl SpecFrom<SpecActiveDataxInner> for SpecActiveDatax {
    open spec fn spec_from(m: SpecActiveDataxInner) -> SpecActiveDatax {
        let (memory, (offset, init)) = m;
        SpecActiveDatax { memory, offset, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ActiveDatax<'a> {
    pub memory: Memidx,
    pub offset: Expr<'a>,
    pub init: ByteVec,
}

impl View for ActiveDatax<'_> {
    type V = SpecActiveDatax;

    open spec fn view(&self) -> Self::V {
        SpecActiveDatax {
            memory: self.memory@,
            offset: self.offset@,
            init: self.init@,
        }
    }
}
pub type ActiveDataxInner<'a> = (Memidx, (Expr<'a>, ByteVec));
impl<'a> From<ActiveDatax<'a>> for ActiveDataxInner<'a> {
    fn ex_from(m: ActiveDatax) -> ActiveDataxInner {
        (m.memory, (m.offset, m.init))
    }
}
impl<'a> From<ActiveDataxInner<'a>> for ActiveDatax<'a> {
    fn ex_from(m: ActiveDataxInner) -> ActiveDatax {
        let (memory, (offset, init)) = m;
        ActiveDatax { memory, offset, init }
    }
}

pub struct ActiveDataxMapper<'a>(PhantomData<&'a ()>);
impl<'a> ActiveDataxMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ActiveDataxMapper(PhantomData)
    }
    pub fn new() -> Self {
        ActiveDataxMapper(PhantomData)
    }
}
impl View for ActiveDataxMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ActiveDataxMapper<'_> {
    type Src = SpecActiveDataxInner;
    type Dst = SpecActiveDatax;
}
impl SpecIsoProof for ActiveDataxMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ActiveDataxMapper<'a> {
    type Src = ActiveDataxInner<'a>;
    type Dst = ActiveDatax<'a>;
}

pub struct SpecActiveDataxCombinator(SpecActiveDataxCombinatorAlias);

impl SpecCombinator for SpecActiveDataxCombinator {
    type Type = SpecActiveDatax;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecActiveDataxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecActiveDataxCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecActiveDataxCombinatorAlias = Mapped<(SpecMemidxCombinator, (SpecExprCombinator, SpecByteVecCombinator)), ActiveDataxMapper<'static>>;

pub struct ActiveDataxCombinator<'a>(ActiveDataxCombinatorAlias<'a>);

impl<'a> View for ActiveDataxCombinator<'a> {
    type V = SpecActiveDataxCombinator;
    closed spec fn view(&self) -> Self::V { SpecActiveDataxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ActiveDataxCombinator<'a> {
    type Type = ActiveDatax<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ActiveDataxCombinatorAlias<'a> = Mapped<(MemidxCombinator, (ExprCombinator<'a>, ByteVecCombinator<'a>)), ActiveDataxMapper<'a>>;


pub closed spec fn spec_active_datax() -> SpecActiveDataxCombinator {
    SpecActiveDataxCombinator(
    Mapped {
        inner: (spec_memidx(), (spec_expr(), spec_byte_vec())),
        mapper: ActiveDataxMapper::spec_new(),
    })
}

                
pub fn active_datax<'a>() -> (o: ActiveDataxCombinator<'a>)
    ensures o@ == spec_active_datax(),
{
    ActiveDataxCombinator(
    Mapped {
        inner: (memidx(), (expr(), byte_vec())),
        mapper: ActiveDataxMapper::new(),
    })
}

                

pub struct SpecStart {
    pub func: SpecFuncidx,
}

pub type SpecStartInner = SpecFuncidx;
impl SpecFrom<SpecStart> for SpecStartInner {
    open spec fn spec_from(m: SpecStart) -> SpecStartInner {
        m.func
    }
}
impl SpecFrom<SpecStartInner> for SpecStart {
    open spec fn spec_from(m: SpecStartInner) -> SpecStart {
        let func = m;
        SpecStart { func }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Start {
    pub func: Funcidx,
}

impl View for Start {
    type V = SpecStart;

    open spec fn view(&self) -> Self::V {
        SpecStart {
            func: self.func@,
        }
    }
}
pub type StartInner = Funcidx;
impl From<Start> for StartInner {
    fn ex_from(m: Start) -> StartInner {
        m.func
    }
}
impl From<StartInner> for Start {
    fn ex_from(m: StartInner) -> Start {
        let func = m;
        Start { func }
    }
}

pub struct StartMapper;
impl StartMapper {
    pub closed spec fn spec_new() -> Self {
        StartMapper
    }
    pub fn new() -> Self {
        StartMapper
    }
}
impl View for StartMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for StartMapper {
    type Src = SpecStartInner;
    type Dst = SpecStart;
}
impl SpecIsoProof for StartMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for StartMapper {
    type Src = StartInner;
    type Dst = Start;
}

pub struct SpecStartCombinator(SpecStartCombinatorAlias);

impl SpecCombinator for SpecStartCombinator {
    type Type = SpecStart;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecStartCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecStartCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecStartCombinatorAlias = Mapped<SpecFuncidxCombinator, StartMapper>;

pub struct StartCombinator(StartCombinatorAlias);

impl View for StartCombinator {
    type V = SpecStartCombinator;
    closed spec fn view(&self) -> Self::V { SpecStartCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for StartCombinator {
    type Type = Start;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type StartCombinatorAlias = Mapped<FuncidxCombinator, StartMapper>;


pub closed spec fn spec_start() -> SpecStartCombinator {
    SpecStartCombinator(
    Mapped {
        inner: spec_funcidx(),
        mapper: StartMapper::spec_new(),
    })
}

                
pub fn start() -> (o: StartCombinator)
    ensures o@ == spec_start(),
{
    StartCombinator(
    Mapped {
        inner: funcidx(),
        mapper: StartMapper::new(),
    })
}

                

pub struct SpecResulttype {
    pub l: u64,
    pub v: Seq<SpecValtype>,
}

pub type SpecResulttypeInner = (u64, Seq<SpecValtype>);
impl SpecFrom<SpecResulttype> for SpecResulttypeInner {
    open spec fn spec_from(m: SpecResulttype) -> SpecResulttypeInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecResulttypeInner> for SpecResulttype {
    open spec fn spec_from(m: SpecResulttypeInner) -> SpecResulttype {
        let (l, v) = m;
        SpecResulttype { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Resulttype {
    pub l: u64,
    pub v: RepeatResult<Valtype>,
}

impl View for Resulttype {
    type V = SpecResulttype;

    open spec fn view(&self) -> Self::V {
        SpecResulttype {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ResulttypeInner = (u64, RepeatResult<Valtype>);
impl From<Resulttype> for ResulttypeInner {
    fn ex_from(m: Resulttype) -> ResulttypeInner {
        (m.l, m.v)
    }
}
impl From<ResulttypeInner> for Resulttype {
    fn ex_from(m: ResulttypeInner) -> Resulttype {
        let (l, v) = m;
        Resulttype { l, v }
    }
}

pub struct ResulttypeMapper;
impl ResulttypeMapper {
    pub closed spec fn spec_new() -> Self {
        ResulttypeMapper
    }
    pub fn new() -> Self {
        ResulttypeMapper
    }
}
impl View for ResulttypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ResulttypeMapper {
    type Src = SpecResulttypeInner;
    type Dst = SpecResulttype;
}
impl SpecIsoProof for ResulttypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ResulttypeMapper {
    type Src = ResulttypeInner;
    type Dst = Resulttype;
}

pub struct SpecResulttypeCombinator(SpecResulttypeCombinatorAlias);

impl SpecCombinator for SpecResulttypeCombinator {
    type Type = SpecResulttype;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecResulttypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResulttypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecResulttypeCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecValtypeCombinator>>, ResulttypeMapper>;

pub struct ResulttypeCombinator<'a>(ResulttypeCombinatorAlias<'a>);

impl<'a> View for ResulttypeCombinator<'a> {
    type V = SpecResulttypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecResulttypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ResulttypeCombinator<'a> {
    type Type = Resulttype;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ResulttypeCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<ValtypeCombinator>, ResulttypeCont0<'a>>, ResulttypeMapper>;


pub closed spec fn spec_resulttype() -> SpecResulttypeCombinator {
    SpecResulttypeCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_resulttype_cont0(deps) },
        mapper: ResulttypeMapper::spec_new(),
    })
}

pub open spec fn spec_resulttype_cont0(deps: u64) -> RepeatN<SpecValtypeCombinator> {
    let l = deps;
    RepeatN(spec_valtype(), l.spec_into())
}
                
pub fn resulttype<'a>() -> (o: ResulttypeCombinator<'a>)
    ensures o@ == spec_resulttype(),
{
    ResulttypeCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: ResulttypeCont0::new(), spec_snd: Ghost(|deps| spec_resulttype_cont0(deps)) },
        mapper: ResulttypeMapper::new(),
    })
}

pub struct ResulttypeCont0<'a>(PhantomData<&'a ()>);
impl<'a> ResulttypeCont0<'a> {
    pub fn new() -> Self {
        ResulttypeCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for ResulttypeCont0<'a> {
    type Output = RepeatN<ValtypeCombinator>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_resulttype_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(valtype(), l.ex_into())
    }
}
                

pub struct SpecFunctype {
    pub tag: u8,
    pub params: SpecResulttype,
    pub results: SpecResulttype,
}

pub type SpecFunctypeInner = (u8, (SpecResulttype, SpecResulttype));
impl SpecFrom<SpecFunctype> for SpecFunctypeInner {
    open spec fn spec_from(m: SpecFunctype) -> SpecFunctypeInner {
        (m.tag, (m.params, m.results))
    }
}
impl SpecFrom<SpecFunctypeInner> for SpecFunctype {
    open spec fn spec_from(m: SpecFunctypeInner) -> SpecFunctype {
        let (tag, (params, results)) = m;
        SpecFunctype { tag, params, results }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Functype {
    pub tag: u8,
    pub params: Resulttype,
    pub results: Resulttype,
}

impl View for Functype {
    type V = SpecFunctype;

    open spec fn view(&self) -> Self::V {
        SpecFunctype {
            tag: self.tag@,
            params: self.params@,
            results: self.results@,
        }
    }
}
pub type FunctypeInner = (u8, (Resulttype, Resulttype));
impl From<Functype> for FunctypeInner {
    fn ex_from(m: Functype) -> FunctypeInner {
        (m.tag, (m.params, m.results))
    }
}
impl From<FunctypeInner> for Functype {
    fn ex_from(m: FunctypeInner) -> Functype {
        let (tag, (params, results)) = m;
        Functype { tag, params, results }
    }
}

pub struct FunctypeMapper;
impl FunctypeMapper {
    pub closed spec fn spec_new() -> Self {
        FunctypeMapper
    }
    pub fn new() -> Self {
        FunctypeMapper
    }
}
impl View for FunctypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FunctypeMapper {
    type Src = SpecFunctypeInner;
    type Dst = SpecFunctype;
}
impl SpecIsoProof for FunctypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for FunctypeMapper {
    type Src = FunctypeInner;
    type Dst = Functype;
}
pub const FUNCTYPETAG_CONST: u8 = 96;

pub struct SpecFunctypeCombinator(SpecFunctypeCombinatorAlias);

impl SpecCombinator for SpecFunctypeCombinator {
    type Type = SpecFunctype;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFunctypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFunctypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecFunctypeCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (SpecResulttypeCombinator, SpecResulttypeCombinator)), FunctypeMapper>;

pub struct FunctypeCombinator<'a>(FunctypeCombinatorAlias<'a>);

impl<'a> View for FunctypeCombinator<'a> {
    type V = SpecFunctypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecFunctypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for FunctypeCombinator<'a> {
    type Type = Functype;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type FunctypeCombinatorAlias<'a> = Mapped<(Refined<U8, TagPred<u8>>, (ResulttypeCombinator<'a>, ResulttypeCombinator<'a>)), FunctypeMapper>;


pub closed spec fn spec_functype() -> SpecFunctypeCombinator {
    SpecFunctypeCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(FUNCTYPETAG_CONST) }, (spec_resulttype(), spec_resulttype())),
        mapper: FunctypeMapper::spec_new(),
    })
}

                
pub fn functype<'a>() -> (o: FunctypeCombinator<'a>)
    ensures o@ == spec_functype(),
{
    FunctypeCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(FUNCTYPETAG_CONST) }, (resulttype(), resulttype())),
        mapper: FunctypeMapper::new(),
    })
}

                

pub struct SpecLocalCompressed {
    pub count: u64,
    pub vt: SpecValtype,
}

pub type SpecLocalCompressedInner = (u64, SpecValtype);
impl SpecFrom<SpecLocalCompressed> for SpecLocalCompressedInner {
    open spec fn spec_from(m: SpecLocalCompressed) -> SpecLocalCompressedInner {
        (m.count, m.vt)
    }
}
impl SpecFrom<SpecLocalCompressedInner> for SpecLocalCompressed {
    open spec fn spec_from(m: SpecLocalCompressedInner) -> SpecLocalCompressed {
        let (count, vt) = m;
        SpecLocalCompressed { count, vt }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct LocalCompressed {
    pub count: u64,
    pub vt: Valtype,
}

impl View for LocalCompressed {
    type V = SpecLocalCompressed;

    open spec fn view(&self) -> Self::V {
        SpecLocalCompressed {
            count: self.count@,
            vt: self.vt@,
        }
    }
}
pub type LocalCompressedInner = (u64, Valtype);
impl From<LocalCompressed> for LocalCompressedInner {
    fn ex_from(m: LocalCompressed) -> LocalCompressedInner {
        (m.count, m.vt)
    }
}
impl From<LocalCompressedInner> for LocalCompressed {
    fn ex_from(m: LocalCompressedInner) -> LocalCompressed {
        let (count, vt) = m;
        LocalCompressed { count, vt }
    }
}

pub struct LocalCompressedMapper;
impl LocalCompressedMapper {
    pub closed spec fn spec_new() -> Self {
        LocalCompressedMapper
    }
    pub fn new() -> Self {
        LocalCompressedMapper
    }
}
impl View for LocalCompressedMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LocalCompressedMapper {
    type Src = SpecLocalCompressedInner;
    type Dst = SpecLocalCompressed;
}
impl SpecIsoProof for LocalCompressedMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for LocalCompressedMapper {
    type Src = LocalCompressedInner;
    type Dst = LocalCompressed;
}

pub struct SpecLocalCompressedCombinator(SpecLocalCompressedCombinatorAlias);

impl SpecCombinator for SpecLocalCompressedCombinator {
    type Type = SpecLocalCompressed;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLocalCompressedCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLocalCompressedCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecLocalCompressedCombinatorAlias = Mapped<(UnsignedLEB128, SpecValtypeCombinator), LocalCompressedMapper>;

pub struct LocalCompressedCombinator(LocalCompressedCombinatorAlias);

impl View for LocalCompressedCombinator {
    type V = SpecLocalCompressedCombinator;
    closed spec fn view(&self) -> Self::V { SpecLocalCompressedCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for LocalCompressedCombinator {
    type Type = LocalCompressed;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type LocalCompressedCombinatorAlias = Mapped<(UnsignedLEB128, ValtypeCombinator), LocalCompressedMapper>;


pub closed spec fn spec_local_compressed() -> SpecLocalCompressedCombinator {
    SpecLocalCompressedCombinator(
    Mapped {
        inner: (UnsignedLEB128, spec_valtype()),
        mapper: LocalCompressedMapper::spec_new(),
    })
}

                
pub fn local_compressed() -> (o: LocalCompressedCombinator)
    ensures o@ == spec_local_compressed(),
{
    LocalCompressedCombinator(
    Mapped {
        inner: (UnsignedLEB128, valtype()),
        mapper: LocalCompressedMapper::new(),
    })
}

                

pub struct SpecLocals {
    pub l: u64,
    pub v: Seq<SpecLocalCompressed>,
}

pub type SpecLocalsInner = (u64, Seq<SpecLocalCompressed>);
impl SpecFrom<SpecLocals> for SpecLocalsInner {
    open spec fn spec_from(m: SpecLocals) -> SpecLocalsInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecLocalsInner> for SpecLocals {
    open spec fn spec_from(m: SpecLocalsInner) -> SpecLocals {
        let (l, v) = m;
        SpecLocals { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Locals {
    pub l: u64,
    pub v: RepeatResult<LocalCompressed>,
}

impl View for Locals {
    type V = SpecLocals;

    open spec fn view(&self) -> Self::V {
        SpecLocals {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type LocalsInner = (u64, RepeatResult<LocalCompressed>);
impl From<Locals> for LocalsInner {
    fn ex_from(m: Locals) -> LocalsInner {
        (m.l, m.v)
    }
}
impl From<LocalsInner> for Locals {
    fn ex_from(m: LocalsInner) -> Locals {
        let (l, v) = m;
        Locals { l, v }
    }
}

pub struct LocalsMapper;
impl LocalsMapper {
    pub closed spec fn spec_new() -> Self {
        LocalsMapper
    }
    pub fn new() -> Self {
        LocalsMapper
    }
}
impl View for LocalsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LocalsMapper {
    type Src = SpecLocalsInner;
    type Dst = SpecLocals;
}
impl SpecIsoProof for LocalsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for LocalsMapper {
    type Src = LocalsInner;
    type Dst = Locals;
}

pub struct SpecLocalsCombinator(SpecLocalsCombinatorAlias);

impl SpecCombinator for SpecLocalsCombinator {
    type Type = SpecLocals;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLocalsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLocalsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecLocalsCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecLocalCompressedCombinator>>, LocalsMapper>;

pub struct LocalsCombinator<'a>(LocalsCombinatorAlias<'a>);

impl<'a> View for LocalsCombinator<'a> {
    type V = SpecLocalsCombinator;
    closed spec fn view(&self) -> Self::V { SpecLocalsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for LocalsCombinator<'a> {
    type Type = Locals;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type LocalsCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<LocalCompressedCombinator>, LocalsCont0<'a>>, LocalsMapper>;


pub closed spec fn spec_locals() -> SpecLocalsCombinator {
    SpecLocalsCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_locals_cont0(deps) },
        mapper: LocalsMapper::spec_new(),
    })
}

pub open spec fn spec_locals_cont0(deps: u64) -> RepeatN<SpecLocalCompressedCombinator> {
    let l = deps;
    RepeatN(spec_local_compressed(), l.spec_into())
}
                
pub fn locals<'a>() -> (o: LocalsCombinator<'a>)
    ensures o@ == spec_locals(),
{
    LocalsCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: LocalsCont0::new(), spec_snd: Ghost(|deps| spec_locals_cont0(deps)) },
        mapper: LocalsMapper::new(),
    })
}

pub struct LocalsCont0<'a>(PhantomData<&'a ()>);
impl<'a> LocalsCont0<'a> {
    pub fn new() -> Self {
        LocalsCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for LocalsCont0<'a> {
    type Output = RepeatN<LocalCompressedCombinator>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_locals_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(local_compressed(), l.ex_into())
    }
}
                

pub struct SpecFunc {
    pub locals: SpecLocals,
    pub body: SpecExpr,
}

pub type SpecFuncInner = (SpecLocals, SpecExpr);
impl SpecFrom<SpecFunc> for SpecFuncInner {
    open spec fn spec_from(m: SpecFunc) -> SpecFuncInner {
        (m.locals, m.body)
    }
}
impl SpecFrom<SpecFuncInner> for SpecFunc {
    open spec fn spec_from(m: SpecFuncInner) -> SpecFunc {
        let (locals, body) = m;
        SpecFunc { locals, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Func<'a> {
    pub locals: Locals,
    pub body: Expr<'a>,
}

impl View for Func<'_> {
    type V = SpecFunc;

    open spec fn view(&self) -> Self::V {
        SpecFunc {
            locals: self.locals@,
            body: self.body@,
        }
    }
}
pub type FuncInner<'a> = (Locals, Expr<'a>);
impl<'a> From<Func<'a>> for FuncInner<'a> {
    fn ex_from(m: Func) -> FuncInner {
        (m.locals, m.body)
    }
}
impl<'a> From<FuncInner<'a>> for Func<'a> {
    fn ex_from(m: FuncInner) -> Func {
        let (locals, body) = m;
        Func { locals, body }
    }
}

pub struct FuncMapper<'a>(PhantomData<&'a ()>);
impl<'a> FuncMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        FuncMapper(PhantomData)
    }
    pub fn new() -> Self {
        FuncMapper(PhantomData)
    }
}
impl View for FuncMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FuncMapper<'_> {
    type Src = SpecFuncInner;
    type Dst = SpecFunc;
}
impl SpecIsoProof for FuncMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for FuncMapper<'a> {
    type Src = FuncInner<'a>;
    type Dst = Func<'a>;
}

pub struct SpecFuncCombinator(SpecFuncCombinatorAlias);

impl SpecCombinator for SpecFuncCombinator {
    type Type = SpecFunc;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFuncCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFuncCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecFuncCombinatorAlias = Mapped<(SpecLocalsCombinator, SpecExprCombinator), FuncMapper<'static>>;

pub struct FuncCombinator<'a>(FuncCombinatorAlias<'a>);

impl<'a> View for FuncCombinator<'a> {
    type V = SpecFuncCombinator;
    closed spec fn view(&self) -> Self::V { SpecFuncCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for FuncCombinator<'a> {
    type Type = Func<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type FuncCombinatorAlias<'a> = Mapped<(LocalsCombinator<'a>, ExprCombinator<'a>), FuncMapper<'a>>;


pub closed spec fn spec_func() -> SpecFuncCombinator {
    SpecFuncCombinator(
    Mapped {
        inner: (spec_locals(), spec_expr()),
        mapper: FuncMapper::spec_new(),
    })
}

                
pub fn func<'a>() -> (o: FuncCombinator<'a>)
    ensures o@ == spec_func(),
{
    FuncCombinator(
    Mapped {
        inner: (locals(), expr()),
        mapper: FuncMapper::new(),
    })
}

                

pub struct SpecCode {
    pub size: u64,
    pub code: SpecFunc,
}

pub type SpecCodeInner = (u64, SpecFunc);
impl SpecFrom<SpecCode> for SpecCodeInner {
    open spec fn spec_from(m: SpecCode) -> SpecCodeInner {
        (m.size, m.code)
    }
}
impl SpecFrom<SpecCodeInner> for SpecCode {
    open spec fn spec_from(m: SpecCodeInner) -> SpecCode {
        let (size, code) = m;
        SpecCode { size, code }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Code<'a> {
    pub size: u64,
    pub code: Func<'a>,
}

impl View for Code<'_> {
    type V = SpecCode;

    open spec fn view(&self) -> Self::V {
        SpecCode {
            size: self.size@,
            code: self.code@,
        }
    }
}
pub type CodeInner<'a> = (u64, Func<'a>);
impl<'a> From<Code<'a>> for CodeInner<'a> {
    fn ex_from(m: Code) -> CodeInner {
        (m.size, m.code)
    }
}
impl<'a> From<CodeInner<'a>> for Code<'a> {
    fn ex_from(m: CodeInner) -> Code {
        let (size, code) = m;
        Code { size, code }
    }
}

pub struct CodeMapper<'a>(PhantomData<&'a ()>);
impl<'a> CodeMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CodeMapper(PhantomData)
    }
    pub fn new() -> Self {
        CodeMapper(PhantomData)
    }
}
impl View for CodeMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CodeMapper<'_> {
    type Src = SpecCodeInner;
    type Dst = SpecCode;
}
impl SpecIsoProof for CodeMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CodeMapper<'a> {
    type Src = CodeInner<'a>;
    type Dst = Code<'a>;
}

pub struct SpecCodeCombinator(SpecCodeCombinatorAlias);

impl SpecCombinator for SpecCodeCombinator {
    type Type = SpecCode;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCodeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCodeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecCodeCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecFuncCombinator>>, CodeMapper<'static>>;

pub struct CodeCombinator<'a>(CodeCombinatorAlias<'a>);

impl<'a> View for CodeCombinator<'a> {
    type V = SpecCodeCombinator;
    closed spec fn view(&self) -> Self::V { SpecCodeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CodeCombinator<'a> {
    type Type = Code<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CodeCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, FuncCombinator<'a>>, CodeCont0<'a>>, CodeMapper<'a>>;


pub closed spec fn spec_code() -> SpecCodeCombinator {
    SpecCodeCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_code_cont0(deps) },
        mapper: CodeMapper::spec_new(),
    })
}

pub open spec fn spec_code_cont0(deps: u64) -> AndThen<bytes::Variable, SpecFuncCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_func())
}
                
pub fn code<'a>() -> (o: CodeCombinator<'a>)
    ensures o@ == spec_code(),
{
    CodeCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: CodeCont0::new(), spec_snd: Ghost(|deps| spec_code_cont0(deps)) },
        mapper: CodeMapper::new(),
    })
}

pub struct CodeCont0<'a>(PhantomData<&'a ()>);
impl<'a> CodeCont0<'a> {
    pub fn new() -> Self {
        CodeCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for CodeCont0<'a> {
    type Output = AndThen<bytes::Variable, FuncCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_code_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), func())
    }
}
                

pub struct SpecCodesecContent {
    pub l: u64,
    pub v: Seq<SpecCode>,
}

pub type SpecCodesecContentInner = (u64, Seq<SpecCode>);
impl SpecFrom<SpecCodesecContent> for SpecCodesecContentInner {
    open spec fn spec_from(m: SpecCodesecContent) -> SpecCodesecContentInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecCodesecContentInner> for SpecCodesecContent {
    open spec fn spec_from(m: SpecCodesecContentInner) -> SpecCodesecContent {
        let (l, v) = m;
        SpecCodesecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CodesecContent<'a> {
    pub l: u64,
    pub v: RepeatResult<Code<'a>>,
}

impl View for CodesecContent<'_> {
    type V = SpecCodesecContent;

    open spec fn view(&self) -> Self::V {
        SpecCodesecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type CodesecContentInner<'a> = (u64, RepeatResult<Code<'a>>);
impl<'a> From<CodesecContent<'a>> for CodesecContentInner<'a> {
    fn ex_from(m: CodesecContent) -> CodesecContentInner {
        (m.l, m.v)
    }
}
impl<'a> From<CodesecContentInner<'a>> for CodesecContent<'a> {
    fn ex_from(m: CodesecContentInner) -> CodesecContent {
        let (l, v) = m;
        CodesecContent { l, v }
    }
}

pub struct CodesecContentMapper<'a>(PhantomData<&'a ()>);
impl<'a> CodesecContentMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CodesecContentMapper(PhantomData)
    }
    pub fn new() -> Self {
        CodesecContentMapper(PhantomData)
    }
}
impl View for CodesecContentMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CodesecContentMapper<'_> {
    type Src = SpecCodesecContentInner;
    type Dst = SpecCodesecContent;
}
impl SpecIsoProof for CodesecContentMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CodesecContentMapper<'a> {
    type Src = CodesecContentInner<'a>;
    type Dst = CodesecContent<'a>;
}

pub struct SpecCodesecContentCombinator(SpecCodesecContentCombinatorAlias);

impl SpecCombinator for SpecCodesecContentCombinator {
    type Type = SpecCodesecContent;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCodesecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCodesecContentCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecCodesecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecCodeCombinator>>, CodesecContentMapper<'static>>;

pub struct CodesecContentCombinator<'a>(CodesecContentCombinatorAlias<'a>);

impl<'a> View for CodesecContentCombinator<'a> {
    type V = SpecCodesecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecCodesecContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CodesecContentCombinator<'a> {
    type Type = CodesecContent<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CodesecContentCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<CodeCombinator<'a>>, CodesecContentCont0<'a>>, CodesecContentMapper<'a>>;


pub closed spec fn spec_codesec_content() -> SpecCodesecContentCombinator {
    SpecCodesecContentCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_codesec_content_cont0(deps) },
        mapper: CodesecContentMapper::spec_new(),
    })
}

pub open spec fn spec_codesec_content_cont0(deps: u64) -> RepeatN<SpecCodeCombinator> {
    let l = deps;
    RepeatN(spec_code(), l.spec_into())
}
                
pub fn codesec_content<'a>() -> (o: CodesecContentCombinator<'a>)
    ensures o@ == spec_codesec_content(),
{
    CodesecContentCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: CodesecContentCont0::new(), spec_snd: Ghost(|deps| spec_codesec_content_cont0(deps)) },
        mapper: CodesecContentMapper::new(),
    })
}

pub struct CodesecContentCont0<'a>(PhantomData<&'a ()>);
impl<'a> CodesecContentCont0<'a> {
    pub fn new() -> Self {
        CodesecContentCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for CodesecContentCont0<'a> {
    type Output = RepeatN<CodeCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_codesec_content_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(code(), l.ex_into())
    }
}
                

pub struct SpecCodesec {
    pub size: u64,
    pub cont: SpecCodesecContent,
}

pub type SpecCodesecInner = (u64, SpecCodesecContent);
impl SpecFrom<SpecCodesec> for SpecCodesecInner {
    open spec fn spec_from(m: SpecCodesec) -> SpecCodesecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecCodesecInner> for SpecCodesec {
    open spec fn spec_from(m: SpecCodesecInner) -> SpecCodesec {
        let (size, cont) = m;
        SpecCodesec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Codesec<'a> {
    pub size: u64,
    pub cont: CodesecContent<'a>,
}

impl View for Codesec<'_> {
    type V = SpecCodesec;

    open spec fn view(&self) -> Self::V {
        SpecCodesec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type CodesecInner<'a> = (u64, CodesecContent<'a>);
impl<'a> From<Codesec<'a>> for CodesecInner<'a> {
    fn ex_from(m: Codesec) -> CodesecInner {
        (m.size, m.cont)
    }
}
impl<'a> From<CodesecInner<'a>> for Codesec<'a> {
    fn ex_from(m: CodesecInner) -> Codesec {
        let (size, cont) = m;
        Codesec { size, cont }
    }
}

pub struct CodesecMapper<'a>(PhantomData<&'a ()>);
impl<'a> CodesecMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CodesecMapper(PhantomData)
    }
    pub fn new() -> Self {
        CodesecMapper(PhantomData)
    }
}
impl View for CodesecMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CodesecMapper<'_> {
    type Src = SpecCodesecInner;
    type Dst = SpecCodesec;
}
impl SpecIsoProof for CodesecMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CodesecMapper<'a> {
    type Src = CodesecInner<'a>;
    type Dst = Codesec<'a>;
}

pub struct SpecCodesecCombinator(SpecCodesecCombinatorAlias);

impl SpecCombinator for SpecCodesecCombinator {
    type Type = SpecCodesec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCodesecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCodesecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecCodesecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecCodesecContentCombinator>>, CodesecMapper<'static>>;

pub struct CodesecCombinator<'a>(CodesecCombinatorAlias<'a>);

impl<'a> View for CodesecCombinator<'a> {
    type V = SpecCodesecCombinator;
    closed spec fn view(&self) -> Self::V { SpecCodesecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CodesecCombinator<'a> {
    type Type = Codesec<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CodesecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, CodesecContentCombinator<'a>>, CodesecCont0<'a>>, CodesecMapper<'a>>;


pub closed spec fn spec_codesec() -> SpecCodesecCombinator {
    SpecCodesecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_codesec_cont0(deps) },
        mapper: CodesecMapper::spec_new(),
    })
}

pub open spec fn spec_codesec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecCodesecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_codesec_content())
}
                
pub fn codesec<'a>() -> (o: CodesecCombinator<'a>)
    ensures o@ == spec_codesec(),
{
    CodesecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: CodesecCont0::new(), spec_snd: Ghost(|deps| spec_codesec_cont0(deps)) },
        mapper: CodesecMapper::new(),
    })
}

pub struct CodesecCont0<'a>(PhantomData<&'a ()>);
impl<'a> CodesecCont0<'a> {
    pub fn new() -> Self {
        CodesecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for CodesecCont0<'a> {
    type Output = AndThen<bytes::Variable, CodesecContentCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_codesec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), codesec_content())
    }
}
                

pub struct SpecTablesec {
    pub size: u64,
    pub cont: SpecTablesecContent,
}

pub type SpecTablesecInner = (u64, SpecTablesecContent);
impl SpecFrom<SpecTablesec> for SpecTablesecInner {
    open spec fn spec_from(m: SpecTablesec) -> SpecTablesecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecTablesecInner> for SpecTablesec {
    open spec fn spec_from(m: SpecTablesecInner) -> SpecTablesec {
        let (size, cont) = m;
        SpecTablesec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Tablesec {
    pub size: u64,
    pub cont: TablesecContent,
}

impl View for Tablesec {
    type V = SpecTablesec;

    open spec fn view(&self) -> Self::V {
        SpecTablesec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type TablesecInner = (u64, TablesecContent);
impl From<Tablesec> for TablesecInner {
    fn ex_from(m: Tablesec) -> TablesecInner {
        (m.size, m.cont)
    }
}
impl From<TablesecInner> for Tablesec {
    fn ex_from(m: TablesecInner) -> Tablesec {
        let (size, cont) = m;
        Tablesec { size, cont }
    }
}

pub struct TablesecMapper;
impl TablesecMapper {
    pub closed spec fn spec_new() -> Self {
        TablesecMapper
    }
    pub fn new() -> Self {
        TablesecMapper
    }
}
impl View for TablesecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TablesecMapper {
    type Src = SpecTablesecInner;
    type Dst = SpecTablesec;
}
impl SpecIsoProof for TablesecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for TablesecMapper {
    type Src = TablesecInner;
    type Dst = Tablesec;
}

pub struct SpecTablesecCombinator(SpecTablesecCombinatorAlias);

impl SpecCombinator for SpecTablesecCombinator {
    type Type = SpecTablesec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTablesecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTablesecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTablesecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecTablesecContentCombinator>>, TablesecMapper>;

pub struct TablesecCombinator<'a>(TablesecCombinatorAlias<'a>);

impl<'a> View for TablesecCombinator<'a> {
    type V = SpecTablesecCombinator;
    closed spec fn view(&self) -> Self::V { SpecTablesecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TablesecCombinator<'a> {
    type Type = Tablesec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TablesecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, TablesecContentCombinator<'a>>, TablesecCont0<'a>>, TablesecMapper>;


pub closed spec fn spec_tablesec() -> SpecTablesecCombinator {
    SpecTablesecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_tablesec_cont0(deps) },
        mapper: TablesecMapper::spec_new(),
    })
}

pub open spec fn spec_tablesec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecTablesecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_tablesec_content())
}
                
pub fn tablesec<'a>() -> (o: TablesecCombinator<'a>)
    ensures o@ == spec_tablesec(),
{
    TablesecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: TablesecCont0::new(), spec_snd: Ghost(|deps| spec_tablesec_cont0(deps)) },
        mapper: TablesecMapper::new(),
    })
}

pub struct TablesecCont0<'a>(PhantomData<&'a ()>);
impl<'a> TablesecCont0<'a> {
    pub fn new() -> Self {
        TablesecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for TablesecCont0<'a> {
    type Output = AndThen<bytes::Variable, TablesecContentCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_tablesec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), tablesec_content())
    }
}
                

pub struct SpecElemsecContent {
    pub l: u64,
    pub v: Seq<SpecElem>,
}

pub type SpecElemsecContentInner = (u64, Seq<SpecElem>);
impl SpecFrom<SpecElemsecContent> for SpecElemsecContentInner {
    open spec fn spec_from(m: SpecElemsecContent) -> SpecElemsecContentInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecElemsecContentInner> for SpecElemsecContent {
    open spec fn spec_from(m: SpecElemsecContentInner) -> SpecElemsecContent {
        let (l, v) = m;
        SpecElemsecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ElemsecContent<'a> {
    pub l: u64,
    pub v: RepeatResult<Elem<'a>>,
}

impl View for ElemsecContent<'_> {
    type V = SpecElemsecContent;

    open spec fn view(&self) -> Self::V {
        SpecElemsecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ElemsecContentInner<'a> = (u64, RepeatResult<Elem<'a>>);
impl<'a> From<ElemsecContent<'a>> for ElemsecContentInner<'a> {
    fn ex_from(m: ElemsecContent) -> ElemsecContentInner {
        (m.l, m.v)
    }
}
impl<'a> From<ElemsecContentInner<'a>> for ElemsecContent<'a> {
    fn ex_from(m: ElemsecContentInner) -> ElemsecContent {
        let (l, v) = m;
        ElemsecContent { l, v }
    }
}

pub struct ElemsecContentMapper<'a>(PhantomData<&'a ()>);
impl<'a> ElemsecContentMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ElemsecContentMapper(PhantomData)
    }
    pub fn new() -> Self {
        ElemsecContentMapper(PhantomData)
    }
}
impl View for ElemsecContentMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ElemsecContentMapper<'_> {
    type Src = SpecElemsecContentInner;
    type Dst = SpecElemsecContent;
}
impl SpecIsoProof for ElemsecContentMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ElemsecContentMapper<'a> {
    type Src = ElemsecContentInner<'a>;
    type Dst = ElemsecContent<'a>;
}

pub struct SpecElemsecContentCombinator(SpecElemsecContentCombinatorAlias);

impl SpecCombinator for SpecElemsecContentCombinator {
    type Type = SpecElemsecContent;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemsecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemsecContentCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecElemsecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecElemCombinator>>, ElemsecContentMapper<'static>>;

pub struct ElemsecContentCombinator<'a>(ElemsecContentCombinatorAlias<'a>);

impl<'a> View for ElemsecContentCombinator<'a> {
    type V = SpecElemsecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemsecContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ElemsecContentCombinator<'a> {
    type Type = ElemsecContent<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ElemsecContentCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<ElemCombinator<'a>>, ElemsecContentCont0<'a>>, ElemsecContentMapper<'a>>;


pub closed spec fn spec_elemsec_content() -> SpecElemsecContentCombinator {
    SpecElemsecContentCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_elemsec_content_cont0(deps) },
        mapper: ElemsecContentMapper::spec_new(),
    })
}

pub open spec fn spec_elemsec_content_cont0(deps: u64) -> RepeatN<SpecElemCombinator> {
    let l = deps;
    RepeatN(spec_elem(), l.spec_into())
}
                
pub fn elemsec_content<'a>() -> (o: ElemsecContentCombinator<'a>)
    ensures o@ == spec_elemsec_content(),
{
    ElemsecContentCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: ElemsecContentCont0::new(), spec_snd: Ghost(|deps| spec_elemsec_content_cont0(deps)) },
        mapper: ElemsecContentMapper::new(),
    })
}

pub struct ElemsecContentCont0<'a>(PhantomData<&'a ()>);
impl<'a> ElemsecContentCont0<'a> {
    pub fn new() -> Self {
        ElemsecContentCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for ElemsecContentCont0<'a> {
    type Output = RepeatN<ElemCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_elemsec_content_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(elem(), l.ex_into())
    }
}
                

pub enum SpecExportdesc {
    Func(SpecFuncidx),
    Table(SpecTableidx),
    Mem(SpecMemidx),
    Global(SpecGlobalidx),
}

pub type SpecExportdescInner = Either<SpecFuncidx, Either<SpecTableidx, Either<SpecMemidx, SpecGlobalidx>>>;



impl SpecFrom<SpecExportdesc> for SpecExportdescInner {
    open spec fn spec_from(m: SpecExportdesc) -> SpecExportdescInner {
        match m {
            SpecExportdesc::Func(m) => Either::Left(m),
            SpecExportdesc::Table(m) => Either::Right(Either::Left(m)),
            SpecExportdesc::Mem(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecExportdesc::Global(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl SpecFrom<SpecExportdescInner> for SpecExportdesc {
    open spec fn spec_from(m: SpecExportdescInner) -> SpecExportdesc {
        match m {
            Either::Left(m) => SpecExportdesc::Func(m),
            Either::Right(Either::Left(m)) => SpecExportdesc::Table(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecExportdesc::Mem(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecExportdesc::Global(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exportdesc {
    Func(Funcidx),
    Table(Tableidx),
    Mem(Memidx),
    Global(Globalidx),
}

pub type ExportdescInner = Either<Funcidx, Either<Tableidx, Either<Memidx, Globalidx>>>;


impl View for Exportdesc {
    type V = SpecExportdesc;
    open spec fn view(&self) -> Self::V {
        match self {
            Exportdesc::Func(m) => SpecExportdesc::Func(m@),
            Exportdesc::Table(m) => SpecExportdesc::Table(m@),
            Exportdesc::Mem(m) => SpecExportdesc::Mem(m@),
            Exportdesc::Global(m) => SpecExportdesc::Global(m@),
        }
    }
}


impl From<Exportdesc> for ExportdescInner {
    fn ex_from(m: Exportdesc) -> ExportdescInner {
        match m {
            Exportdesc::Func(m) => Either::Left(m),
            Exportdesc::Table(m) => Either::Right(Either::Left(m)),
            Exportdesc::Mem(m) => Either::Right(Either::Right(Either::Left(m))),
            Exportdesc::Global(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl From<ExportdescInner> for Exportdesc {
    fn ex_from(m: ExportdescInner) -> Exportdesc {
        match m {
            Either::Left(m) => Exportdesc::Func(m),
            Either::Right(Either::Left(m)) => Exportdesc::Table(m),
            Either::Right(Either::Right(Either::Left(m))) => Exportdesc::Mem(m),
            Either::Right(Either::Right(Either::Right(m))) => Exportdesc::Global(m),
        }
    }
    
}


pub struct ExportdescMapper;
impl ExportdescMapper {
    pub closed spec fn spec_new() -> Self {
        ExportdescMapper
    }
    pub fn new() -> Self {
        ExportdescMapper
    }
}
impl View for ExportdescMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExportdescMapper {
    type Src = SpecExportdescInner;
    type Dst = SpecExportdesc;
}
impl SpecIsoProof for ExportdescMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ExportdescMapper {
    type Src = ExportdescInner;
    type Dst = Exportdesc;
}

pub const EXPORTDESCFUNC_0_FRONT_CONST: u8 = 0;

pub const EXPORTDESCTABLE_0_FRONT_CONST: u8 = 1;

pub const EXPORTDESCMEM_0_FRONT_CONST: u8 = 2;

pub const EXPORTDESCGLOBAL_0_FRONT_CONST: u8 = 3;


pub struct SpecExportdescCombinator(SpecExportdescCombinatorAlias);

impl SpecCombinator for SpecExportdescCombinator {
    type Type = SpecExportdesc;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExportdescCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExportdescCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecExportdescCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, SpecFuncidxCombinator>, Choice<Preceded<Tag<U8, u8>, SpecTableidxCombinator>, Choice<Preceded<Tag<U8, u8>, SpecMemidxCombinator>, Preceded<Tag<U8, u8>, SpecGlobalidxCombinator>>>>, ExportdescMapper>;





pub struct ExportdescCombinator(ExportdescCombinatorAlias);

impl View for ExportdescCombinator {
    type V = SpecExportdescCombinator;
    closed spec fn view(&self) -> Self::V { SpecExportdescCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ExportdescCombinator {
    type Type = Exportdesc;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ExportdescCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, FuncidxCombinator>, Choice<Preceded<Tag<U8, u8>, TableidxCombinator>, Choice<Preceded<Tag<U8, u8>, MemidxCombinator>, Preceded<Tag<U8, u8>, GlobalidxCombinator>>>>, ExportdescMapper>;


pub closed spec fn spec_exportdesc() -> SpecExportdescCombinator {
    SpecExportdescCombinator(Mapped { inner: Choice(Preceded(Tag::spec_new(U8, EXPORTDESCFUNC_0_FRONT_CONST), spec_funcidx()), Choice(Preceded(Tag::spec_new(U8, EXPORTDESCTABLE_0_FRONT_CONST), spec_tableidx()), Choice(Preceded(Tag::spec_new(U8, EXPORTDESCMEM_0_FRONT_CONST), spec_memidx()), Preceded(Tag::spec_new(U8, EXPORTDESCGLOBAL_0_FRONT_CONST), spec_globalidx())))), mapper: ExportdescMapper::spec_new() })
}

                
pub fn exportdesc() -> (o: ExportdescCombinator)
    ensures o@ == spec_exportdesc(),
{
    ExportdescCombinator(Mapped { inner: Choice::new(Preceded(Tag::new(U8, EXPORTDESCFUNC_0_FRONT_CONST), funcidx()), Choice::new(Preceded(Tag::new(U8, EXPORTDESCTABLE_0_FRONT_CONST), tableidx()), Choice::new(Preceded(Tag::new(U8, EXPORTDESCMEM_0_FRONT_CONST), memidx()), Preceded(Tag::new(U8, EXPORTDESCGLOBAL_0_FRONT_CONST), globalidx())))), mapper: ExportdescMapper::new() })
}

                

pub struct SpecExport {
    pub nm: SpecName,
    pub d: SpecExportdesc,
}

pub type SpecExportInner = (SpecName, SpecExportdesc);
impl SpecFrom<SpecExport> for SpecExportInner {
    open spec fn spec_from(m: SpecExport) -> SpecExportInner {
        (m.nm, m.d)
    }
}
impl SpecFrom<SpecExportInner> for SpecExport {
    open spec fn spec_from(m: SpecExportInner) -> SpecExport {
        let (nm, d) = m;
        SpecExport { nm, d }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Export {
    pub nm: Name,
    pub d: Exportdesc,
}

impl View for Export {
    type V = SpecExport;

    open spec fn view(&self) -> Self::V {
        SpecExport {
            nm: self.nm@,
            d: self.d@,
        }
    }
}
pub type ExportInner = (Name, Exportdesc);
impl From<Export> for ExportInner {
    fn ex_from(m: Export) -> ExportInner {
        (m.nm, m.d)
    }
}
impl From<ExportInner> for Export {
    fn ex_from(m: ExportInner) -> Export {
        let (nm, d) = m;
        Export { nm, d }
    }
}

pub struct ExportMapper;
impl ExportMapper {
    pub closed spec fn spec_new() -> Self {
        ExportMapper
    }
    pub fn new() -> Self {
        ExportMapper
    }
}
impl View for ExportMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExportMapper {
    type Src = SpecExportInner;
    type Dst = SpecExport;
}
impl SpecIsoProof for ExportMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ExportMapper {
    type Src = ExportInner;
    type Dst = Export;
}

pub struct SpecExportCombinator(SpecExportCombinatorAlias);

impl SpecCombinator for SpecExportCombinator {
    type Type = SpecExport;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExportCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExportCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecExportCombinatorAlias = Mapped<(SpecNameCombinator, SpecExportdescCombinator), ExportMapper>;

pub struct ExportCombinator<'a>(ExportCombinatorAlias<'a>);

impl<'a> View for ExportCombinator<'a> {
    type V = SpecExportCombinator;
    closed spec fn view(&self) -> Self::V { SpecExportCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ExportCombinator<'a> {
    type Type = Export;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ExportCombinatorAlias<'a> = Mapped<(NameCombinator<'a>, ExportdescCombinator), ExportMapper>;


pub closed spec fn spec_export() -> SpecExportCombinator {
    SpecExportCombinator(
    Mapped {
        inner: (spec_name(), spec_exportdesc()),
        mapper: ExportMapper::spec_new(),
    })
}

                
pub fn export<'a>() -> (o: ExportCombinator<'a>)
    ensures o@ == spec_export(),
{
    ExportCombinator(
    Mapped {
        inner: (name(), exportdesc()),
        mapper: ExportMapper::new(),
    })
}

                

pub struct SpecExports {
    pub l: u64,
    pub v: Seq<SpecExport>,
}

pub type SpecExportsInner = (u64, Seq<SpecExport>);
impl SpecFrom<SpecExports> for SpecExportsInner {
    open spec fn spec_from(m: SpecExports) -> SpecExportsInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecExportsInner> for SpecExports {
    open spec fn spec_from(m: SpecExportsInner) -> SpecExports {
        let (l, v) = m;
        SpecExports { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Exports {
    pub l: u64,
    pub v: RepeatResult<Export>,
}

impl View for Exports {
    type V = SpecExports;

    open spec fn view(&self) -> Self::V {
        SpecExports {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ExportsInner = (u64, RepeatResult<Export>);
impl From<Exports> for ExportsInner {
    fn ex_from(m: Exports) -> ExportsInner {
        (m.l, m.v)
    }
}
impl From<ExportsInner> for Exports {
    fn ex_from(m: ExportsInner) -> Exports {
        let (l, v) = m;
        Exports { l, v }
    }
}

pub struct ExportsMapper;
impl ExportsMapper {
    pub closed spec fn spec_new() -> Self {
        ExportsMapper
    }
    pub fn new() -> Self {
        ExportsMapper
    }
}
impl View for ExportsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExportsMapper {
    type Src = SpecExportsInner;
    type Dst = SpecExports;
}
impl SpecIsoProof for ExportsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ExportsMapper {
    type Src = ExportsInner;
    type Dst = Exports;
}

pub struct SpecExportsCombinator(SpecExportsCombinatorAlias);

impl SpecCombinator for SpecExportsCombinator {
    type Type = SpecExports;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExportsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExportsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecExportsCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecExportCombinator>>, ExportsMapper>;

pub struct ExportsCombinator<'a>(ExportsCombinatorAlias<'a>);

impl<'a> View for ExportsCombinator<'a> {
    type V = SpecExportsCombinator;
    closed spec fn view(&self) -> Self::V { SpecExportsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ExportsCombinator<'a> {
    type Type = Exports;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ExportsCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<ExportCombinator<'a>>, ExportsCont0<'a>>, ExportsMapper>;


pub closed spec fn spec_exports() -> SpecExportsCombinator {
    SpecExportsCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_exports_cont0(deps) },
        mapper: ExportsMapper::spec_new(),
    })
}

pub open spec fn spec_exports_cont0(deps: u64) -> RepeatN<SpecExportCombinator> {
    let l = deps;
    RepeatN(spec_export(), l.spec_into())
}
                
pub fn exports<'a>() -> (o: ExportsCombinator<'a>)
    ensures o@ == spec_exports(),
{
    ExportsCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: ExportsCont0::new(), spec_snd: Ghost(|deps| spec_exports_cont0(deps)) },
        mapper: ExportsMapper::new(),
    })
}

pub struct ExportsCont0<'a>(PhantomData<&'a ()>);
impl<'a> ExportsCont0<'a> {
    pub fn new() -> Self {
        ExportsCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for ExportsCont0<'a> {
    type Output = RepeatN<ExportCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_exports_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(export(), l.ex_into())
    }
}
                

pub struct SpecExportsec {
    pub size: u64,
    pub cont: SpecExports,
}

pub type SpecExportsecInner = (u64, SpecExports);
impl SpecFrom<SpecExportsec> for SpecExportsecInner {
    open spec fn spec_from(m: SpecExportsec) -> SpecExportsecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecExportsecInner> for SpecExportsec {
    open spec fn spec_from(m: SpecExportsecInner) -> SpecExportsec {
        let (size, cont) = m;
        SpecExportsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Exportsec {
    pub size: u64,
    pub cont: Exports,
}

impl View for Exportsec {
    type V = SpecExportsec;

    open spec fn view(&self) -> Self::V {
        SpecExportsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type ExportsecInner = (u64, Exports);
impl From<Exportsec> for ExportsecInner {
    fn ex_from(m: Exportsec) -> ExportsecInner {
        (m.size, m.cont)
    }
}
impl From<ExportsecInner> for Exportsec {
    fn ex_from(m: ExportsecInner) -> Exportsec {
        let (size, cont) = m;
        Exportsec { size, cont }
    }
}

pub struct ExportsecMapper;
impl ExportsecMapper {
    pub closed spec fn spec_new() -> Self {
        ExportsecMapper
    }
    pub fn new() -> Self {
        ExportsecMapper
    }
}
impl View for ExportsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExportsecMapper {
    type Src = SpecExportsecInner;
    type Dst = SpecExportsec;
}
impl SpecIsoProof for ExportsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ExportsecMapper {
    type Src = ExportsecInner;
    type Dst = Exportsec;
}

pub struct SpecExportsecCombinator(SpecExportsecCombinatorAlias);

impl SpecCombinator for SpecExportsecCombinator {
    type Type = SpecExportsec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExportsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExportsecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecExportsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecExportsCombinator>>, ExportsecMapper>;

pub struct ExportsecCombinator<'a>(ExportsecCombinatorAlias<'a>);

impl<'a> View for ExportsecCombinator<'a> {
    type V = SpecExportsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecExportsecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ExportsecCombinator<'a> {
    type Type = Exportsec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ExportsecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, ExportsCombinator<'a>>, ExportsecCont0<'a>>, ExportsecMapper>;


pub closed spec fn spec_exportsec() -> SpecExportsecCombinator {
    SpecExportsecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_exportsec_cont0(deps) },
        mapper: ExportsecMapper::spec_new(),
    })
}

pub open spec fn spec_exportsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecExportsCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_exports())
}
                
pub fn exportsec<'a>() -> (o: ExportsecCombinator<'a>)
    ensures o@ == spec_exportsec(),
{
    ExportsecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: ExportsecCont0::new(), spec_snd: Ghost(|deps| spec_exportsec_cont0(deps)) },
        mapper: ExportsecMapper::new(),
    })
}

pub struct ExportsecCont0<'a>(PhantomData<&'a ()>);
impl<'a> ExportsecCont0<'a> {
    pub fn new() -> Self {
        ExportsecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for ExportsecCont0<'a> {
    type Output = AndThen<bytes::Variable, ExportsCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_exportsec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), exports())
    }
}
                

pub struct SpecActiveData0 {
    pub offset: SpecExpr,
    pub init: SpecByteVec,
}

pub type SpecActiveData0Inner = (SpecExpr, SpecByteVec);
impl SpecFrom<SpecActiveData0> for SpecActiveData0Inner {
    open spec fn spec_from(m: SpecActiveData0) -> SpecActiveData0Inner {
        (m.offset, m.init)
    }
}
impl SpecFrom<SpecActiveData0Inner> for SpecActiveData0 {
    open spec fn spec_from(m: SpecActiveData0Inner) -> SpecActiveData0 {
        let (offset, init) = m;
        SpecActiveData0 { offset, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ActiveData0<'a> {
    pub offset: Expr<'a>,
    pub init: ByteVec,
}

impl View for ActiveData0<'_> {
    type V = SpecActiveData0;

    open spec fn view(&self) -> Self::V {
        SpecActiveData0 {
            offset: self.offset@,
            init: self.init@,
        }
    }
}
pub type ActiveData0Inner<'a> = (Expr<'a>, ByteVec);
impl<'a> From<ActiveData0<'a>> for ActiveData0Inner<'a> {
    fn ex_from(m: ActiveData0) -> ActiveData0Inner {
        (m.offset, m.init)
    }
}
impl<'a> From<ActiveData0Inner<'a>> for ActiveData0<'a> {
    fn ex_from(m: ActiveData0Inner) -> ActiveData0 {
        let (offset, init) = m;
        ActiveData0 { offset, init }
    }
}

pub struct ActiveData0Mapper<'a>(PhantomData<&'a ()>);
impl<'a> ActiveData0Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ActiveData0Mapper(PhantomData)
    }
    pub fn new() -> Self {
        ActiveData0Mapper(PhantomData)
    }
}
impl View for ActiveData0Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ActiveData0Mapper<'_> {
    type Src = SpecActiveData0Inner;
    type Dst = SpecActiveData0;
}
impl SpecIsoProof for ActiveData0Mapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ActiveData0Mapper<'a> {
    type Src = ActiveData0Inner<'a>;
    type Dst = ActiveData0<'a>;
}

pub struct SpecActiveData0Combinator(SpecActiveData0CombinatorAlias);

impl SpecCombinator for SpecActiveData0Combinator {
    type Type = SpecActiveData0;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecActiveData0Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecActiveData0CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecActiveData0CombinatorAlias = Mapped<(SpecExprCombinator, SpecByteVecCombinator), ActiveData0Mapper<'static>>;

pub struct ActiveData0Combinator<'a>(ActiveData0CombinatorAlias<'a>);

impl<'a> View for ActiveData0Combinator<'a> {
    type V = SpecActiveData0Combinator;
    closed spec fn view(&self) -> Self::V { SpecActiveData0Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ActiveData0Combinator<'a> {
    type Type = ActiveData0<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ActiveData0CombinatorAlias<'a> = Mapped<(ExprCombinator<'a>, ByteVecCombinator<'a>), ActiveData0Mapper<'a>>;


pub closed spec fn spec_active_data0() -> SpecActiveData0Combinator {
    SpecActiveData0Combinator(
    Mapped {
        inner: (spec_expr(), spec_byte_vec()),
        mapper: ActiveData0Mapper::spec_new(),
    })
}

                
pub fn active_data0<'a>() -> (o: ActiveData0Combinator<'a>)
    ensures o@ == spec_active_data0(),
{
    ActiveData0Combinator(
    Mapped {
        inner: (expr(), byte_vec()),
        mapper: ActiveData0Mapper::new(),
    })
}

                
pub type SpecPassiveData = SpecByteVec;
pub type PassiveData = ByteVec;


pub struct SpecPassiveDataCombinator(SpecPassiveDataCombinatorAlias);

impl SpecCombinator for SpecPassiveDataCombinator {
    type Type = SpecPassiveData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPassiveDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPassiveDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecPassiveDataCombinatorAlias = SpecByteVecCombinator;

pub struct PassiveDataCombinator<'a>(PassiveDataCombinatorAlias<'a>);

impl<'a> View for PassiveDataCombinator<'a> {
    type V = SpecPassiveDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecPassiveDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PassiveDataCombinator<'a> {
    type Type = PassiveData;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PassiveDataCombinatorAlias<'a> = ByteVecCombinator<'a>;


pub closed spec fn spec_passive_data() -> SpecPassiveDataCombinator {
    SpecPassiveDataCombinator(spec_byte_vec())
}

                
pub fn passive_data<'a>() -> (o: PassiveDataCombinator<'a>)
    ensures o@ == spec_passive_data(),
{
    PassiveDataCombinator(byte_vec())
}

                

pub enum SpecData {
    ActiveData0(SpecActiveData0),
    PassiveData(SpecPassiveData),
    ActiveDataX(SpecActiveDatax),
}

pub type SpecDataInner = Either<SpecActiveData0, Either<SpecPassiveData, SpecActiveDatax>>;



impl SpecFrom<SpecData> for SpecDataInner {
    open spec fn spec_from(m: SpecData) -> SpecDataInner {
        match m {
            SpecData::ActiveData0(m) => Either::Left(m),
            SpecData::PassiveData(m) => Either::Right(Either::Left(m)),
            SpecData::ActiveDataX(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl SpecFrom<SpecDataInner> for SpecData {
    open spec fn spec_from(m: SpecDataInner) -> SpecData {
        match m {
            Either::Left(m) => SpecData::ActiveData0(m),
            Either::Right(Either::Left(m)) => SpecData::PassiveData(m),
            Either::Right(Either::Right(m)) => SpecData::ActiveDataX(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Data<'a> {
    ActiveData0(ActiveData0<'a>),
    PassiveData(PassiveData),
    ActiveDataX(ActiveDatax<'a>),
}

pub type DataInner<'a> = Either<ActiveData0<'a>, Either<PassiveData, ActiveDatax<'a>>>;


impl<'a> View for Data<'a> {
    type V = SpecData;
    open spec fn view(&self) -> Self::V {
        match self {
            Data::ActiveData0(m) => SpecData::ActiveData0(m@),
            Data::PassiveData(m) => SpecData::PassiveData(m@),
            Data::ActiveDataX(m) => SpecData::ActiveDataX(m@),
        }
    }
}


impl<'a> From<Data<'a>> for DataInner<'a> {
    fn ex_from(m: Data<'a>) -> DataInner<'a> {
        match m {
            Data::ActiveData0(m) => Either::Left(m),
            Data::PassiveData(m) => Either::Right(Either::Left(m)),
            Data::ActiveDataX(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<DataInner<'a>> for Data<'a> {
    fn ex_from(m: DataInner<'a>) -> Data<'a> {
        match m {
            Either::Left(m) => Data::ActiveData0(m),
            Either::Right(Either::Left(m)) => Data::PassiveData(m),
            Either::Right(Either::Right(m)) => Data::ActiveDataX(m),
        }
    }
    
}


pub struct DataMapper<'a>(PhantomData<&'a ()>);
impl<'a> DataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        DataMapper(PhantomData)
    }
    pub fn new() -> Self {
        DataMapper(PhantomData)
    }
}
impl View for DataMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DataMapper<'_> {
    type Src = SpecDataInner;
    type Dst = SpecData;
}
impl SpecIsoProof for DataMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for DataMapper<'a> {
    type Src = DataInner<'a>;
    type Dst = Data<'a>;
}

pub const DATAACTIVEDATA0_0_FRONT_CONST: u64 = 0;

pub const DATAPASSIVEDATA_0_FRONT_CONST: u64 = 1;

pub const DATAACTIVEDATAX_0_FRONT_CONST: u64 = 2;


pub struct SpecDataCombinator(SpecDataCombinatorAlias);

impl SpecCombinator for SpecDataCombinator {
    type Type = SpecData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecDataCombinatorAlias = Mapped<Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecActiveData0Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecPassiveDataCombinator>, Preceded<Tag<UnsignedLEB128, u64>, SpecActiveDataxCombinator>>>, DataMapper<'static>>;




pub struct DataCombinator<'a>(DataCombinatorAlias<'a>);

impl<'a> View for DataCombinator<'a> {
    type V = SpecDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for DataCombinator<'a> {
    type Type = Data<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type DataCombinatorAlias<'a> = Mapped<Choice<Preceded<Tag<UnsignedLEB128, u64>, ActiveData0Combinator<'a>>, Choice<Preceded<Tag<UnsignedLEB128, u64>, PassiveDataCombinator<'a>>, Preceded<Tag<UnsignedLEB128, u64>, ActiveDataxCombinator<'a>>>>, DataMapper<'a>>;


pub closed spec fn spec_data() -> SpecDataCombinator {
    SpecDataCombinator(Mapped { inner: Choice(Preceded(Tag::spec_new(UnsignedLEB128, DATAACTIVEDATA0_0_FRONT_CONST), spec_active_data0()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, DATAPASSIVEDATA_0_FRONT_CONST), spec_passive_data()), Preceded(Tag::spec_new(UnsignedLEB128, DATAACTIVEDATAX_0_FRONT_CONST), spec_active_datax()))), mapper: DataMapper::spec_new() })
}

                
pub fn data<'a>() -> (o: DataCombinator<'a>)
    ensures o@ == spec_data(),
{
    DataCombinator(Mapped { inner: Choice::new(Preceded(Tag::new(UnsignedLEB128, DATAACTIVEDATA0_0_FRONT_CONST), active_data0()), Choice::new(Preceded(Tag::new(UnsignedLEB128, DATAPASSIVEDATA_0_FRONT_CONST), passive_data()), Preceded(Tag::new(UnsignedLEB128, DATAACTIVEDATAX_0_FRONT_CONST), active_datax()))), mapper: DataMapper::new() })
}

                
pub type SpecSigned64 = Seq<u8>;
pub type Signed64<'a> = &'a [u8];


pub struct SpecSigned64Combinator(SpecSigned64CombinatorAlias);

impl SpecCombinator for SpecSigned64Combinator {
    type Type = SpecSigned64;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSigned64Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSigned64CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecSigned64CombinatorAlias = bytes::Fixed<8>;

pub struct Signed64Combinator(Signed64CombinatorAlias);

impl View for Signed64Combinator {
    type V = SpecSigned64Combinator;
    closed spec fn view(&self) -> Self::V { SpecSigned64Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Signed64Combinator {
    type Type = Signed64<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Signed64CombinatorAlias = bytes::Fixed<8>;


pub closed spec fn spec_signed_64() -> SpecSigned64Combinator {
    SpecSigned64Combinator(bytes::Fixed::<8>)
}

                
pub fn signed_64() -> (o: Signed64Combinator)
    ensures o@ == spec_signed_64(),
{
    Signed64Combinator(bytes::Fixed::<8>)
}

                

pub struct SpecDatasecContent {
    pub l: u64,
    pub v: Seq<SpecData>,
}

pub type SpecDatasecContentInner = (u64, Seq<SpecData>);
impl SpecFrom<SpecDatasecContent> for SpecDatasecContentInner {
    open spec fn spec_from(m: SpecDatasecContent) -> SpecDatasecContentInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecDatasecContentInner> for SpecDatasecContent {
    open spec fn spec_from(m: SpecDatasecContentInner) -> SpecDatasecContent {
        let (l, v) = m;
        SpecDatasecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct DatasecContent<'a> {
    pub l: u64,
    pub v: RepeatResult<Data<'a>>,
}

impl View for DatasecContent<'_> {
    type V = SpecDatasecContent;

    open spec fn view(&self) -> Self::V {
        SpecDatasecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type DatasecContentInner<'a> = (u64, RepeatResult<Data<'a>>);
impl<'a> From<DatasecContent<'a>> for DatasecContentInner<'a> {
    fn ex_from(m: DatasecContent) -> DatasecContentInner {
        (m.l, m.v)
    }
}
impl<'a> From<DatasecContentInner<'a>> for DatasecContent<'a> {
    fn ex_from(m: DatasecContentInner) -> DatasecContent {
        let (l, v) = m;
        DatasecContent { l, v }
    }
}

pub struct DatasecContentMapper<'a>(PhantomData<&'a ()>);
impl<'a> DatasecContentMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        DatasecContentMapper(PhantomData)
    }
    pub fn new() -> Self {
        DatasecContentMapper(PhantomData)
    }
}
impl View for DatasecContentMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DatasecContentMapper<'_> {
    type Src = SpecDatasecContentInner;
    type Dst = SpecDatasecContent;
}
impl SpecIsoProof for DatasecContentMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for DatasecContentMapper<'a> {
    type Src = DatasecContentInner<'a>;
    type Dst = DatasecContent<'a>;
}

pub struct SpecDatasecContentCombinator(SpecDatasecContentCombinatorAlias);

impl SpecCombinator for SpecDatasecContentCombinator {
    type Type = SpecDatasecContent;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDatasecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDatasecContentCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecDatasecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecDataCombinator>>, DatasecContentMapper<'static>>;

pub struct DatasecContentCombinator<'a>(DatasecContentCombinatorAlias<'a>);

impl<'a> View for DatasecContentCombinator<'a> {
    type V = SpecDatasecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecDatasecContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for DatasecContentCombinator<'a> {
    type Type = DatasecContent<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type DatasecContentCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<DataCombinator<'a>>, DatasecContentCont0<'a>>, DatasecContentMapper<'a>>;


pub closed spec fn spec_datasec_content() -> SpecDatasecContentCombinator {
    SpecDatasecContentCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_datasec_content_cont0(deps) },
        mapper: DatasecContentMapper::spec_new(),
    })
}

pub open spec fn spec_datasec_content_cont0(deps: u64) -> RepeatN<SpecDataCombinator> {
    let l = deps;
    RepeatN(spec_data(), l.spec_into())
}
                
pub fn datasec_content<'a>() -> (o: DatasecContentCombinator<'a>)
    ensures o@ == spec_datasec_content(),
{
    DatasecContentCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: DatasecContentCont0::new(), spec_snd: Ghost(|deps| spec_datasec_content_cont0(deps)) },
        mapper: DatasecContentMapper::new(),
    })
}

pub struct DatasecContentCont0<'a>(PhantomData<&'a ()>);
impl<'a> DatasecContentCont0<'a> {
    pub fn new() -> Self {
        DatasecContentCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for DatasecContentCont0<'a> {
    type Output = RepeatN<DataCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_datasec_content_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(data(), l.ex_into())
    }
}
                

pub struct SpecStartsec {
    pub size: u64,
    pub cont: SpecStart,
}

pub type SpecStartsecInner = (u64, SpecStart);
impl SpecFrom<SpecStartsec> for SpecStartsecInner {
    open spec fn spec_from(m: SpecStartsec) -> SpecStartsecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecStartsecInner> for SpecStartsec {
    open spec fn spec_from(m: SpecStartsecInner) -> SpecStartsec {
        let (size, cont) = m;
        SpecStartsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Startsec {
    pub size: u64,
    pub cont: Start,
}

impl View for Startsec {
    type V = SpecStartsec;

    open spec fn view(&self) -> Self::V {
        SpecStartsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type StartsecInner = (u64, Start);
impl From<Startsec> for StartsecInner {
    fn ex_from(m: Startsec) -> StartsecInner {
        (m.size, m.cont)
    }
}
impl From<StartsecInner> for Startsec {
    fn ex_from(m: StartsecInner) -> Startsec {
        let (size, cont) = m;
        Startsec { size, cont }
    }
}

pub struct StartsecMapper;
impl StartsecMapper {
    pub closed spec fn spec_new() -> Self {
        StartsecMapper
    }
    pub fn new() -> Self {
        StartsecMapper
    }
}
impl View for StartsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for StartsecMapper {
    type Src = SpecStartsecInner;
    type Dst = SpecStartsec;
}
impl SpecIsoProof for StartsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for StartsecMapper {
    type Src = StartsecInner;
    type Dst = Startsec;
}

pub struct SpecStartsecCombinator(SpecStartsecCombinatorAlias);

impl SpecCombinator for SpecStartsecCombinator {
    type Type = SpecStartsec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecStartsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecStartsecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecStartsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecStartCombinator>>, StartsecMapper>;

pub struct StartsecCombinator<'a>(StartsecCombinatorAlias<'a>);

impl<'a> View for StartsecCombinator<'a> {
    type V = SpecStartsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecStartsecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for StartsecCombinator<'a> {
    type Type = Startsec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type StartsecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, StartCombinator>, StartsecCont0<'a>>, StartsecMapper>;


pub closed spec fn spec_startsec() -> SpecStartsecCombinator {
    SpecStartsecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_startsec_cont0(deps) },
        mapper: StartsecMapper::spec_new(),
    })
}

pub open spec fn spec_startsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecStartCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_start())
}
                
pub fn startsec<'a>() -> (o: StartsecCombinator<'a>)
    ensures o@ == spec_startsec(),
{
    StartsecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: StartsecCont0::new(), spec_snd: Ghost(|deps| spec_startsec_cont0(deps)) },
        mapper: StartsecMapper::new(),
    })
}

pub struct StartsecCont0<'a>(PhantomData<&'a ()>);
impl<'a> StartsecCont0<'a> {
    pub fn new() -> Self {
        StartsecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for StartsecCont0<'a> {
    type Output = AndThen<bytes::Variable, StartCombinator>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_startsec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), start())
    }
}
                

pub struct SpecGlobalsec {
    pub size: u64,
    pub cont: SpecGlobalsecContent,
}

pub type SpecGlobalsecInner = (u64, SpecGlobalsecContent);
impl SpecFrom<SpecGlobalsec> for SpecGlobalsecInner {
    open spec fn spec_from(m: SpecGlobalsec) -> SpecGlobalsecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecGlobalsecInner> for SpecGlobalsec {
    open spec fn spec_from(m: SpecGlobalsecInner) -> SpecGlobalsec {
        let (size, cont) = m;
        SpecGlobalsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Globalsec<'a> {
    pub size: u64,
    pub cont: GlobalsecContent<'a>,
}

impl View for Globalsec<'_> {
    type V = SpecGlobalsec;

    open spec fn view(&self) -> Self::V {
        SpecGlobalsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type GlobalsecInner<'a> = (u64, GlobalsecContent<'a>);
impl<'a> From<Globalsec<'a>> for GlobalsecInner<'a> {
    fn ex_from(m: Globalsec) -> GlobalsecInner {
        (m.size, m.cont)
    }
}
impl<'a> From<GlobalsecInner<'a>> for Globalsec<'a> {
    fn ex_from(m: GlobalsecInner) -> Globalsec {
        let (size, cont) = m;
        Globalsec { size, cont }
    }
}

pub struct GlobalsecMapper<'a>(PhantomData<&'a ()>);
impl<'a> GlobalsecMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        GlobalsecMapper(PhantomData)
    }
    pub fn new() -> Self {
        GlobalsecMapper(PhantomData)
    }
}
impl View for GlobalsecMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for GlobalsecMapper<'_> {
    type Src = SpecGlobalsecInner;
    type Dst = SpecGlobalsec;
}
impl SpecIsoProof for GlobalsecMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for GlobalsecMapper<'a> {
    type Src = GlobalsecInner<'a>;
    type Dst = Globalsec<'a>;
}

pub struct SpecGlobalsecCombinator(SpecGlobalsecCombinatorAlias);

impl SpecCombinator for SpecGlobalsecCombinator {
    type Type = SpecGlobalsec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGlobalsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecGlobalsecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecGlobalsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecGlobalsecContentCombinator>>, GlobalsecMapper<'static>>;

pub struct GlobalsecCombinator<'a>(GlobalsecCombinatorAlias<'a>);

impl<'a> View for GlobalsecCombinator<'a> {
    type V = SpecGlobalsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecGlobalsecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for GlobalsecCombinator<'a> {
    type Type = Globalsec<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type GlobalsecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, GlobalsecContentCombinator<'a>>, GlobalsecCont0<'a>>, GlobalsecMapper<'a>>;


pub closed spec fn spec_globalsec() -> SpecGlobalsecCombinator {
    SpecGlobalsecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_globalsec_cont0(deps) },
        mapper: GlobalsecMapper::spec_new(),
    })
}

pub open spec fn spec_globalsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecGlobalsecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_globalsec_content())
}
                
pub fn globalsec<'a>() -> (o: GlobalsecCombinator<'a>)
    ensures o@ == spec_globalsec(),
{
    GlobalsecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: GlobalsecCont0::new(), spec_snd: Ghost(|deps| spec_globalsec_cont0(deps)) },
        mapper: GlobalsecMapper::new(),
    })
}

pub struct GlobalsecCont0<'a>(PhantomData<&'a ()>);
impl<'a> GlobalsecCont0<'a> {
    pub fn new() -> Self {
        GlobalsecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for GlobalsecCont0<'a> {
    type Output = AndThen<bytes::Variable, GlobalsecContentCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_globalsec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), globalsec_content())
    }
}
                
pub type SpecSigned32 = Seq<u8>;
pub type Signed32<'a> = &'a [u8];


pub struct SpecSigned32Combinator(SpecSigned32CombinatorAlias);

impl SpecCombinator for SpecSigned32Combinator {
    type Type = SpecSigned32;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSigned32Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSigned32CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecSigned32CombinatorAlias = bytes::Fixed<4>;

pub struct Signed32Combinator(Signed32CombinatorAlias);

impl View for Signed32Combinator {
    type V = SpecSigned32Combinator;
    closed spec fn view(&self) -> Self::V { SpecSigned32Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Signed32Combinator {
    type Type = Signed32<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Signed32CombinatorAlias = bytes::Fixed<4>;


pub closed spec fn spec_signed_32() -> SpecSigned32Combinator {
    SpecSigned32Combinator(bytes::Fixed::<4>)
}

                
pub fn signed_32() -> (o: Signed32Combinator)
    ensures o@ == spec_signed_32(),
{
    Signed32Combinator(bytes::Fixed::<4>)
}

                

pub struct SpecMem {
    pub ty: SpecMemtype,
}

pub type SpecMemInner = SpecMemtype;
impl SpecFrom<SpecMem> for SpecMemInner {
    open spec fn spec_from(m: SpecMem) -> SpecMemInner {
        m.ty
    }
}
impl SpecFrom<SpecMemInner> for SpecMem {
    open spec fn spec_from(m: SpecMemInner) -> SpecMem {
        let ty = m;
        SpecMem { ty }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Mem {
    pub ty: Memtype,
}

impl View for Mem {
    type V = SpecMem;

    open spec fn view(&self) -> Self::V {
        SpecMem {
            ty: self.ty@,
        }
    }
}
pub type MemInner = Memtype;
impl From<Mem> for MemInner {
    fn ex_from(m: Mem) -> MemInner {
        m.ty
    }
}
impl From<MemInner> for Mem {
    fn ex_from(m: MemInner) -> Mem {
        let ty = m;
        Mem { ty }
    }
}

pub struct MemMapper;
impl MemMapper {
    pub closed spec fn spec_new() -> Self {
        MemMapper
    }
    pub fn new() -> Self {
        MemMapper
    }
}
impl View for MemMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemMapper {
    type Src = SpecMemInner;
    type Dst = SpecMem;
}
impl SpecIsoProof for MemMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for MemMapper {
    type Src = MemInner;
    type Dst = Mem;
}

pub struct SpecMemCombinator(SpecMemCombinatorAlias);

impl SpecCombinator for SpecMemCombinator {
    type Type = SpecMem;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMemCombinatorAlias = Mapped<SpecMemtypeCombinator, MemMapper>;

pub struct MemCombinator(MemCombinatorAlias);

impl View for MemCombinator {
    type V = SpecMemCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MemCombinator {
    type Type = Mem;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MemCombinatorAlias = Mapped<MemtypeCombinator, MemMapper>;


pub closed spec fn spec_mem() -> SpecMemCombinator {
    SpecMemCombinator(
    Mapped {
        inner: spec_memtype(),
        mapper: MemMapper::spec_new(),
    })
}

                
pub fn mem() -> (o: MemCombinator)
    ensures o@ == spec_mem(),
{
    MemCombinator(
    Mapped {
        inner: memtype(),
        mapper: MemMapper::new(),
    })
}

                

pub struct SpecMemsecContent {
    pub l: u64,
    pub v: Seq<SpecMem>,
}

pub type SpecMemsecContentInner = (u64, Seq<SpecMem>);
impl SpecFrom<SpecMemsecContent> for SpecMemsecContentInner {
    open spec fn spec_from(m: SpecMemsecContent) -> SpecMemsecContentInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecMemsecContentInner> for SpecMemsecContent {
    open spec fn spec_from(m: SpecMemsecContentInner) -> SpecMemsecContent {
        let (l, v) = m;
        SpecMemsecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MemsecContent {
    pub l: u64,
    pub v: RepeatResult<Mem>,
}

impl View for MemsecContent {
    type V = SpecMemsecContent;

    open spec fn view(&self) -> Self::V {
        SpecMemsecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type MemsecContentInner = (u64, RepeatResult<Mem>);
impl From<MemsecContent> for MemsecContentInner {
    fn ex_from(m: MemsecContent) -> MemsecContentInner {
        (m.l, m.v)
    }
}
impl From<MemsecContentInner> for MemsecContent {
    fn ex_from(m: MemsecContentInner) -> MemsecContent {
        let (l, v) = m;
        MemsecContent { l, v }
    }
}

pub struct MemsecContentMapper;
impl MemsecContentMapper {
    pub closed spec fn spec_new() -> Self {
        MemsecContentMapper
    }
    pub fn new() -> Self {
        MemsecContentMapper
    }
}
impl View for MemsecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemsecContentMapper {
    type Src = SpecMemsecContentInner;
    type Dst = SpecMemsecContent;
}
impl SpecIsoProof for MemsecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for MemsecContentMapper {
    type Src = MemsecContentInner;
    type Dst = MemsecContent;
}

pub struct SpecMemsecContentCombinator(SpecMemsecContentCombinatorAlias);

impl SpecCombinator for SpecMemsecContentCombinator {
    type Type = SpecMemsecContent;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemsecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemsecContentCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMemsecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecMemCombinator>>, MemsecContentMapper>;

pub struct MemsecContentCombinator<'a>(MemsecContentCombinatorAlias<'a>);

impl<'a> View for MemsecContentCombinator<'a> {
    type V = SpecMemsecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemsecContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MemsecContentCombinator<'a> {
    type Type = MemsecContent;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MemsecContentCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<MemCombinator>, MemsecContentCont0<'a>>, MemsecContentMapper>;


pub closed spec fn spec_memsec_content() -> SpecMemsecContentCombinator {
    SpecMemsecContentCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_memsec_content_cont0(deps) },
        mapper: MemsecContentMapper::spec_new(),
    })
}

pub open spec fn spec_memsec_content_cont0(deps: u64) -> RepeatN<SpecMemCombinator> {
    let l = deps;
    RepeatN(spec_mem(), l.spec_into())
}
                
pub fn memsec_content<'a>() -> (o: MemsecContentCombinator<'a>)
    ensures o@ == spec_memsec_content(),
{
    MemsecContentCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: MemsecContentCont0::new(), spec_snd: Ghost(|deps| spec_memsec_content_cont0(deps)) },
        mapper: MemsecContentMapper::new(),
    })
}

pub struct MemsecContentCont0<'a>(PhantomData<&'a ()>);
impl<'a> MemsecContentCont0<'a> {
    pub fn new() -> Self {
        MemsecContentCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for MemsecContentCont0<'a> {
    type Output = RepeatN<MemCombinator>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_memsec_content_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(mem(), l.ex_into())
    }
}
                
pub type SpecMyCustomSection = SpecByteVec;
pub type MyCustomSection = ByteVec;


pub struct SpecMyCustomSectionCombinator(SpecMyCustomSectionCombinatorAlias);

impl SpecCombinator for SpecMyCustomSectionCombinator {
    type Type = SpecMyCustomSection;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMyCustomSectionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMyCustomSectionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMyCustomSectionCombinatorAlias = SpecByteVecCombinator;

pub struct MyCustomSectionCombinator<'a>(MyCustomSectionCombinatorAlias<'a>);

impl<'a> View for MyCustomSectionCombinator<'a> {
    type V = SpecMyCustomSectionCombinator;
    closed spec fn view(&self) -> Self::V { SpecMyCustomSectionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MyCustomSectionCombinator<'a> {
    type Type = MyCustomSection;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MyCustomSectionCombinatorAlias<'a> = ByteVecCombinator<'a>;


pub closed spec fn spec_my_custom_section() -> SpecMyCustomSectionCombinator {
    SpecMyCustomSectionCombinator(spec_byte_vec())
}

                
pub fn my_custom_section<'a>() -> (o: MyCustomSectionCombinator<'a>)
    ensures o@ == spec_my_custom_section(),
{
    MyCustomSectionCombinator(byte_vec())
}

                

pub struct SpecDatacountsec {
    pub size: u64,
    pub cont: u64,
}

pub type SpecDatacountsecInner = (u64, u64);
impl SpecFrom<SpecDatacountsec> for SpecDatacountsecInner {
    open spec fn spec_from(m: SpecDatacountsec) -> SpecDatacountsecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecDatacountsecInner> for SpecDatacountsec {
    open spec fn spec_from(m: SpecDatacountsecInner) -> SpecDatacountsec {
        let (size, cont) = m;
        SpecDatacountsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Datacountsec {
    pub size: u64,
    pub cont: u64,
}

impl View for Datacountsec {
    type V = SpecDatacountsec;

    open spec fn view(&self) -> Self::V {
        SpecDatacountsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type DatacountsecInner = (u64, u64);
impl From<Datacountsec> for DatacountsecInner {
    fn ex_from(m: Datacountsec) -> DatacountsecInner {
        (m.size, m.cont)
    }
}
impl From<DatacountsecInner> for Datacountsec {
    fn ex_from(m: DatacountsecInner) -> Datacountsec {
        let (size, cont) = m;
        Datacountsec { size, cont }
    }
}

pub struct DatacountsecMapper;
impl DatacountsecMapper {
    pub closed spec fn spec_new() -> Self {
        DatacountsecMapper
    }
    pub fn new() -> Self {
        DatacountsecMapper
    }
}
impl View for DatacountsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DatacountsecMapper {
    type Src = SpecDatacountsecInner;
    type Dst = SpecDatacountsec;
}
impl SpecIsoProof for DatacountsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for DatacountsecMapper {
    type Src = DatacountsecInner;
    type Dst = Datacountsec;
}

pub struct SpecDatacountsecCombinator(SpecDatacountsecCombinatorAlias);

impl SpecCombinator for SpecDatacountsecCombinator {
    type Type = SpecDatacountsec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDatacountsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDatacountsecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecDatacountsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, UnsignedLEB128>>, DatacountsecMapper>;

pub struct DatacountsecCombinator<'a>(DatacountsecCombinatorAlias<'a>);

impl<'a> View for DatacountsecCombinator<'a> {
    type V = SpecDatacountsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecDatacountsecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for DatacountsecCombinator<'a> {
    type Type = Datacountsec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type DatacountsecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, UnsignedLEB128>, DatacountsecCont0<'a>>, DatacountsecMapper>;


pub closed spec fn spec_datacountsec() -> SpecDatacountsecCombinator {
    SpecDatacountsecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_datacountsec_cont0(deps) },
        mapper: DatacountsecMapper::spec_new(),
    })
}

pub open spec fn spec_datacountsec_cont0(deps: u64) -> AndThen<bytes::Variable, UnsignedLEB128> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), UnsignedLEB128)
}
                
pub fn datacountsec<'a>() -> (o: DatacountsecCombinator<'a>)
    ensures o@ == spec_datacountsec(),
{
    DatacountsecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: DatacountsecCont0::new(), spec_snd: Ghost(|deps| spec_datacountsec_cont0(deps)) },
        mapper: DatacountsecMapper::new(),
    })
}

pub struct DatacountsecCont0<'a>(PhantomData<&'a ()>);
impl<'a> DatacountsecCont0<'a> {
    pub fn new() -> Self {
        DatacountsecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for DatacountsecCont0<'a> {
    type Output = AndThen<bytes::Variable, UnsignedLEB128>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_datacountsec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), UnsignedLEB128)
    }
}
                

pub struct SpecTypesecContent {
    pub l: u64,
    pub v: Seq<SpecFunctype>,
}

pub type SpecTypesecContentInner = (u64, Seq<SpecFunctype>);
impl SpecFrom<SpecTypesecContent> for SpecTypesecContentInner {
    open spec fn spec_from(m: SpecTypesecContent) -> SpecTypesecContentInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecTypesecContentInner> for SpecTypesecContent {
    open spec fn spec_from(m: SpecTypesecContentInner) -> SpecTypesecContent {
        let (l, v) = m;
        SpecTypesecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TypesecContent {
    pub l: u64,
    pub v: RepeatResult<Functype>,
}

impl View for TypesecContent {
    type V = SpecTypesecContent;

    open spec fn view(&self) -> Self::V {
        SpecTypesecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type TypesecContentInner = (u64, RepeatResult<Functype>);
impl From<TypesecContent> for TypesecContentInner {
    fn ex_from(m: TypesecContent) -> TypesecContentInner {
        (m.l, m.v)
    }
}
impl From<TypesecContentInner> for TypesecContent {
    fn ex_from(m: TypesecContentInner) -> TypesecContent {
        let (l, v) = m;
        TypesecContent { l, v }
    }
}

pub struct TypesecContentMapper;
impl TypesecContentMapper {
    pub closed spec fn spec_new() -> Self {
        TypesecContentMapper
    }
    pub fn new() -> Self {
        TypesecContentMapper
    }
}
impl View for TypesecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TypesecContentMapper {
    type Src = SpecTypesecContentInner;
    type Dst = SpecTypesecContent;
}
impl SpecIsoProof for TypesecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for TypesecContentMapper {
    type Src = TypesecContentInner;
    type Dst = TypesecContent;
}

pub struct SpecTypesecContentCombinator(SpecTypesecContentCombinatorAlias);

impl SpecCombinator for SpecTypesecContentCombinator {
    type Type = SpecTypesecContent;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTypesecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTypesecContentCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTypesecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecFunctypeCombinator>>, TypesecContentMapper>;

pub struct TypesecContentCombinator<'a>(TypesecContentCombinatorAlias<'a>);

impl<'a> View for TypesecContentCombinator<'a> {
    type V = SpecTypesecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecTypesecContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TypesecContentCombinator<'a> {
    type Type = TypesecContent;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TypesecContentCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<FunctypeCombinator<'a>>, TypesecContentCont0<'a>>, TypesecContentMapper>;


pub closed spec fn spec_typesec_content() -> SpecTypesecContentCombinator {
    SpecTypesecContentCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_typesec_content_cont0(deps) },
        mapper: TypesecContentMapper::spec_new(),
    })
}

pub open spec fn spec_typesec_content_cont0(deps: u64) -> RepeatN<SpecFunctypeCombinator> {
    let l = deps;
    RepeatN(spec_functype(), l.spec_into())
}
                
pub fn typesec_content<'a>() -> (o: TypesecContentCombinator<'a>)
    ensures o@ == spec_typesec_content(),
{
    TypesecContentCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: TypesecContentCont0::new(), spec_snd: Ghost(|deps| spec_typesec_content_cont0(deps)) },
        mapper: TypesecContentMapper::new(),
    })
}

pub struct TypesecContentCont0<'a>(PhantomData<&'a ()>);
impl<'a> TypesecContentCont0<'a> {
    pub fn new() -> Self {
        TypesecContentCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for TypesecContentCont0<'a> {
    type Output = RepeatN<FunctypeCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_typesec_content_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(functype(), l.ex_into())
    }
}
                

pub struct SpecMemsec {
    pub size: u64,
    pub cont: SpecMemsecContent,
}

pub type SpecMemsecInner = (u64, SpecMemsecContent);
impl SpecFrom<SpecMemsec> for SpecMemsecInner {
    open spec fn spec_from(m: SpecMemsec) -> SpecMemsecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecMemsecInner> for SpecMemsec {
    open spec fn spec_from(m: SpecMemsecInner) -> SpecMemsec {
        let (size, cont) = m;
        SpecMemsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Memsec {
    pub size: u64,
    pub cont: MemsecContent,
}

impl View for Memsec {
    type V = SpecMemsec;

    open spec fn view(&self) -> Self::V {
        SpecMemsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type MemsecInner = (u64, MemsecContent);
impl From<Memsec> for MemsecInner {
    fn ex_from(m: Memsec) -> MemsecInner {
        (m.size, m.cont)
    }
}
impl From<MemsecInner> for Memsec {
    fn ex_from(m: MemsecInner) -> Memsec {
        let (size, cont) = m;
        Memsec { size, cont }
    }
}

pub struct MemsecMapper;
impl MemsecMapper {
    pub closed spec fn spec_new() -> Self {
        MemsecMapper
    }
    pub fn new() -> Self {
        MemsecMapper
    }
}
impl View for MemsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemsecMapper {
    type Src = SpecMemsecInner;
    type Dst = SpecMemsec;
}
impl SpecIsoProof for MemsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for MemsecMapper {
    type Src = MemsecInner;
    type Dst = Memsec;
}

pub struct SpecMemsecCombinator(SpecMemsecCombinatorAlias);

impl SpecCombinator for SpecMemsecCombinator {
    type Type = SpecMemsec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemsecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMemsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecMemsecContentCombinator>>, MemsecMapper>;

pub struct MemsecCombinator<'a>(MemsecCombinatorAlias<'a>);

impl<'a> View for MemsecCombinator<'a> {
    type V = SpecMemsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemsecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MemsecCombinator<'a> {
    type Type = Memsec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MemsecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, MemsecContentCombinator<'a>>, MemsecCont0<'a>>, MemsecMapper>;


pub closed spec fn spec_memsec() -> SpecMemsecCombinator {
    SpecMemsecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_memsec_cont0(deps) },
        mapper: MemsecMapper::spec_new(),
    })
}

pub open spec fn spec_memsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecMemsecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_memsec_content())
}
                
pub fn memsec<'a>() -> (o: MemsecCombinator<'a>)
    ensures o@ == spec_memsec(),
{
    MemsecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: MemsecCont0::new(), spec_snd: Ghost(|deps| spec_memsec_cont0(deps)) },
        mapper: MemsecMapper::new(),
    })
}

pub struct MemsecCont0<'a>(PhantomData<&'a ()>);
impl<'a> MemsecCont0<'a> {
    pub fn new() -> Self {
        MemsecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for MemsecCont0<'a> {
    type Output = AndThen<bytes::Variable, MemsecContentCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_memsec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), memsec_content())
    }
}
                

pub struct SpecCustom {
    pub name: SpecName,
    pub data: SpecMyCustomSection,
}

pub type SpecCustomInner = (SpecName, SpecMyCustomSection);
impl SpecFrom<SpecCustom> for SpecCustomInner {
    open spec fn spec_from(m: SpecCustom) -> SpecCustomInner {
        (m.name, m.data)
    }
}
impl SpecFrom<SpecCustomInner> for SpecCustom {
    open spec fn spec_from(m: SpecCustomInner) -> SpecCustom {
        let (name, data) = m;
        SpecCustom { name, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Custom {
    pub name: Name,
    pub data: MyCustomSection,
}

impl View for Custom {
    type V = SpecCustom;

    open spec fn view(&self) -> Self::V {
        SpecCustom {
            name: self.name@,
            data: self.data@,
        }
    }
}
pub type CustomInner = (Name, MyCustomSection);
impl From<Custom> for CustomInner {
    fn ex_from(m: Custom) -> CustomInner {
        (m.name, m.data)
    }
}
impl From<CustomInner> for Custom {
    fn ex_from(m: CustomInner) -> Custom {
        let (name, data) = m;
        Custom { name, data }
    }
}

pub struct CustomMapper;
impl CustomMapper {
    pub closed spec fn spec_new() -> Self {
        CustomMapper
    }
    pub fn new() -> Self {
        CustomMapper
    }
}
impl View for CustomMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CustomMapper {
    type Src = SpecCustomInner;
    type Dst = SpecCustom;
}
impl SpecIsoProof for CustomMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for CustomMapper {
    type Src = CustomInner;
    type Dst = Custom;
}

pub struct SpecCustomCombinator(SpecCustomCombinatorAlias);

impl SpecCombinator for SpecCustomCombinator {
    type Type = SpecCustom;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCustomCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCustomCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecCustomCombinatorAlias = Mapped<(SpecNameCombinator, SpecMyCustomSectionCombinator), CustomMapper>;

pub struct CustomCombinator<'a>(CustomCombinatorAlias<'a>);

impl<'a> View for CustomCombinator<'a> {
    type V = SpecCustomCombinator;
    closed spec fn view(&self) -> Self::V { SpecCustomCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CustomCombinator<'a> {
    type Type = Custom;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CustomCombinatorAlias<'a> = Mapped<(NameCombinator<'a>, MyCustomSectionCombinator<'a>), CustomMapper>;


pub closed spec fn spec_custom() -> SpecCustomCombinator {
    SpecCustomCombinator(
    Mapped {
        inner: (spec_name(), spec_my_custom_section()),
        mapper: CustomMapper::spec_new(),
    })
}

                
pub fn custom<'a>() -> (o: CustomCombinator<'a>)
    ensures o@ == spec_custom(),
{
    CustomCombinator(
    Mapped {
        inner: (name(), my_custom_section()),
        mapper: CustomMapper::new(),
    })
}

                

pub struct SpecCustomsec {
    pub size: u64,
    pub cont: SpecCustom,
}

pub type SpecCustomsecInner = (u64, SpecCustom);
impl SpecFrom<SpecCustomsec> for SpecCustomsecInner {
    open spec fn spec_from(m: SpecCustomsec) -> SpecCustomsecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecCustomsecInner> for SpecCustomsec {
    open spec fn spec_from(m: SpecCustomsecInner) -> SpecCustomsec {
        let (size, cont) = m;
        SpecCustomsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Customsec {
    pub size: u64,
    pub cont: Custom,
}

impl View for Customsec {
    type V = SpecCustomsec;

    open spec fn view(&self) -> Self::V {
        SpecCustomsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type CustomsecInner = (u64, Custom);
impl From<Customsec> for CustomsecInner {
    fn ex_from(m: Customsec) -> CustomsecInner {
        (m.size, m.cont)
    }
}
impl From<CustomsecInner> for Customsec {
    fn ex_from(m: CustomsecInner) -> Customsec {
        let (size, cont) = m;
        Customsec { size, cont }
    }
}

pub struct CustomsecMapper;
impl CustomsecMapper {
    pub closed spec fn spec_new() -> Self {
        CustomsecMapper
    }
    pub fn new() -> Self {
        CustomsecMapper
    }
}
impl View for CustomsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CustomsecMapper {
    type Src = SpecCustomsecInner;
    type Dst = SpecCustomsec;
}
impl SpecIsoProof for CustomsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for CustomsecMapper {
    type Src = CustomsecInner;
    type Dst = Customsec;
}

pub struct SpecCustomsecCombinator(SpecCustomsecCombinatorAlias);

impl SpecCombinator for SpecCustomsecCombinator {
    type Type = SpecCustomsec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCustomsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCustomsecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecCustomsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecCustomCombinator>>, CustomsecMapper>;

pub struct CustomsecCombinator<'a>(CustomsecCombinatorAlias<'a>);

impl<'a> View for CustomsecCombinator<'a> {
    type V = SpecCustomsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecCustomsecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CustomsecCombinator<'a> {
    type Type = Customsec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CustomsecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, CustomCombinator<'a>>, CustomsecCont0<'a>>, CustomsecMapper>;


pub closed spec fn spec_customsec() -> SpecCustomsecCombinator {
    SpecCustomsecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_customsec_cont0(deps) },
        mapper: CustomsecMapper::spec_new(),
    })
}

pub open spec fn spec_customsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecCustomCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_custom())
}
                
pub fn customsec<'a>() -> (o: CustomsecCombinator<'a>)
    ensures o@ == spec_customsec(),
{
    CustomsecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: CustomsecCont0::new(), spec_snd: Ghost(|deps| spec_customsec_cont0(deps)) },
        mapper: CustomsecMapper::new(),
    })
}

pub struct CustomsecCont0<'a>(PhantomData<&'a ()>);
impl<'a> CustomsecCont0<'a> {
    pub fn new() -> Self {
        CustomsecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for CustomsecCont0<'a> {
    type Output = AndThen<bytes::Variable, CustomCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_customsec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), custom())
    }
}
                

pub struct SpecTypesec {
    pub size: u64,
    pub cont: SpecTypesecContent,
}

pub type SpecTypesecInner = (u64, SpecTypesecContent);
impl SpecFrom<SpecTypesec> for SpecTypesecInner {
    open spec fn spec_from(m: SpecTypesec) -> SpecTypesecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecTypesecInner> for SpecTypesec {
    open spec fn spec_from(m: SpecTypesecInner) -> SpecTypesec {
        let (size, cont) = m;
        SpecTypesec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Typesec {
    pub size: u64,
    pub cont: TypesecContent,
}

impl View for Typesec {
    type V = SpecTypesec;

    open spec fn view(&self) -> Self::V {
        SpecTypesec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type TypesecInner = (u64, TypesecContent);
impl From<Typesec> for TypesecInner {
    fn ex_from(m: Typesec) -> TypesecInner {
        (m.size, m.cont)
    }
}
impl From<TypesecInner> for Typesec {
    fn ex_from(m: TypesecInner) -> Typesec {
        let (size, cont) = m;
        Typesec { size, cont }
    }
}

pub struct TypesecMapper;
impl TypesecMapper {
    pub closed spec fn spec_new() -> Self {
        TypesecMapper
    }
    pub fn new() -> Self {
        TypesecMapper
    }
}
impl View for TypesecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TypesecMapper {
    type Src = SpecTypesecInner;
    type Dst = SpecTypesec;
}
impl SpecIsoProof for TypesecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for TypesecMapper {
    type Src = TypesecInner;
    type Dst = Typesec;
}

pub struct SpecTypesecCombinator(SpecTypesecCombinatorAlias);

impl SpecCombinator for SpecTypesecCombinator {
    type Type = SpecTypesec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTypesecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTypesecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTypesecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecTypesecContentCombinator>>, TypesecMapper>;

pub struct TypesecCombinator<'a>(TypesecCombinatorAlias<'a>);

impl<'a> View for TypesecCombinator<'a> {
    type V = SpecTypesecCombinator;
    closed spec fn view(&self) -> Self::V { SpecTypesecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TypesecCombinator<'a> {
    type Type = Typesec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TypesecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, TypesecContentCombinator<'a>>, TypesecCont0<'a>>, TypesecMapper>;


pub closed spec fn spec_typesec() -> SpecTypesecCombinator {
    SpecTypesecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_typesec_cont0(deps) },
        mapper: TypesecMapper::spec_new(),
    })
}

pub open spec fn spec_typesec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecTypesecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_typesec_content())
}
                
pub fn typesec<'a>() -> (o: TypesecCombinator<'a>)
    ensures o@ == spec_typesec(),
{
    TypesecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: TypesecCont0::new(), spec_snd: Ghost(|deps| spec_typesec_cont0(deps)) },
        mapper: TypesecMapper::new(),
    })
}

pub struct TypesecCont0<'a>(PhantomData<&'a ()>);
impl<'a> TypesecCont0<'a> {
    pub fn new() -> Self {
        TypesecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for TypesecCont0<'a> {
    type Output = AndThen<bytes::Variable, TypesecContentCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_typesec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), typesec_content())
    }
}
                

pub struct SpecImportsec {
    pub size: u64,
    pub cont: SpecImports,
}

pub type SpecImportsecInner = (u64, SpecImports);
impl SpecFrom<SpecImportsec> for SpecImportsecInner {
    open spec fn spec_from(m: SpecImportsec) -> SpecImportsecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecImportsecInner> for SpecImportsec {
    open spec fn spec_from(m: SpecImportsecInner) -> SpecImportsec {
        let (size, cont) = m;
        SpecImportsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Importsec {
    pub size: u64,
    pub cont: Imports,
}

impl View for Importsec {
    type V = SpecImportsec;

    open spec fn view(&self) -> Self::V {
        SpecImportsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type ImportsecInner = (u64, Imports);
impl From<Importsec> for ImportsecInner {
    fn ex_from(m: Importsec) -> ImportsecInner {
        (m.size, m.cont)
    }
}
impl From<ImportsecInner> for Importsec {
    fn ex_from(m: ImportsecInner) -> Importsec {
        let (size, cont) = m;
        Importsec { size, cont }
    }
}

pub struct ImportsecMapper;
impl ImportsecMapper {
    pub closed spec fn spec_new() -> Self {
        ImportsecMapper
    }
    pub fn new() -> Self {
        ImportsecMapper
    }
}
impl View for ImportsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ImportsecMapper {
    type Src = SpecImportsecInner;
    type Dst = SpecImportsec;
}
impl SpecIsoProof for ImportsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ImportsecMapper {
    type Src = ImportsecInner;
    type Dst = Importsec;
}

pub struct SpecImportsecCombinator(SpecImportsecCombinatorAlias);

impl SpecCombinator for SpecImportsecCombinator {
    type Type = SpecImportsec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecImportsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecImportsecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecImportsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecImportsCombinator>>, ImportsecMapper>;

pub struct ImportsecCombinator<'a>(ImportsecCombinatorAlias<'a>);

impl<'a> View for ImportsecCombinator<'a> {
    type V = SpecImportsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecImportsecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ImportsecCombinator<'a> {
    type Type = Importsec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ImportsecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, ImportsCombinator<'a>>, ImportsecCont0<'a>>, ImportsecMapper>;


pub closed spec fn spec_importsec() -> SpecImportsecCombinator {
    SpecImportsecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_importsec_cont0(deps) },
        mapper: ImportsecMapper::spec_new(),
    })
}

pub open spec fn spec_importsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecImportsCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_imports())
}
                
pub fn importsec<'a>() -> (o: ImportsecCombinator<'a>)
    ensures o@ == spec_importsec(),
{
    ImportsecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: ImportsecCont0::new(), spec_snd: Ghost(|deps| spec_importsec_cont0(deps)) },
        mapper: ImportsecMapper::new(),
    })
}

pub struct ImportsecCont0<'a>(PhantomData<&'a ()>);
impl<'a> ImportsecCont0<'a> {
    pub fn new() -> Self {
        ImportsecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for ImportsecCont0<'a> {
    type Output = AndThen<bytes::Variable, ImportsCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_importsec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), imports())
    }
}
                

pub struct SpecFuncsecContent {
    pub l: u64,
    pub v: Seq<SpecTypeidx>,
}

pub type SpecFuncsecContentInner = (u64, Seq<SpecTypeidx>);
impl SpecFrom<SpecFuncsecContent> for SpecFuncsecContentInner {
    open spec fn spec_from(m: SpecFuncsecContent) -> SpecFuncsecContentInner {
        (m.l, m.v)
    }
}
impl SpecFrom<SpecFuncsecContentInner> for SpecFuncsecContent {
    open spec fn spec_from(m: SpecFuncsecContentInner) -> SpecFuncsecContent {
        let (l, v) = m;
        SpecFuncsecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct FuncsecContent {
    pub l: u64,
    pub v: RepeatResult<Typeidx>,
}

impl View for FuncsecContent {
    type V = SpecFuncsecContent;

    open spec fn view(&self) -> Self::V {
        SpecFuncsecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type FuncsecContentInner = (u64, RepeatResult<Typeidx>);
impl From<FuncsecContent> for FuncsecContentInner {
    fn ex_from(m: FuncsecContent) -> FuncsecContentInner {
        (m.l, m.v)
    }
}
impl From<FuncsecContentInner> for FuncsecContent {
    fn ex_from(m: FuncsecContentInner) -> FuncsecContent {
        let (l, v) = m;
        FuncsecContent { l, v }
    }
}

pub struct FuncsecContentMapper;
impl FuncsecContentMapper {
    pub closed spec fn spec_new() -> Self {
        FuncsecContentMapper
    }
    pub fn new() -> Self {
        FuncsecContentMapper
    }
}
impl View for FuncsecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FuncsecContentMapper {
    type Src = SpecFuncsecContentInner;
    type Dst = SpecFuncsecContent;
}
impl SpecIsoProof for FuncsecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for FuncsecContentMapper {
    type Src = FuncsecContentInner;
    type Dst = FuncsecContent;
}

pub struct SpecFuncsecContentCombinator(SpecFuncsecContentCombinatorAlias);

impl SpecCombinator for SpecFuncsecContentCombinator {
    type Type = SpecFuncsecContent;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFuncsecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFuncsecContentCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecFuncsecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecTypeidxCombinator>>, FuncsecContentMapper>;

pub struct FuncsecContentCombinator<'a>(FuncsecContentCombinatorAlias<'a>);

impl<'a> View for FuncsecContentCombinator<'a> {
    type V = SpecFuncsecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecFuncsecContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for FuncsecContentCombinator<'a> {
    type Type = FuncsecContent;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type FuncsecContentCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, RepeatN<TypeidxCombinator>, FuncsecContentCont0<'a>>, FuncsecContentMapper>;


pub closed spec fn spec_funcsec_content() -> SpecFuncsecContentCombinator {
    SpecFuncsecContentCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_funcsec_content_cont0(deps) },
        mapper: FuncsecContentMapper::spec_new(),
    })
}

pub open spec fn spec_funcsec_content_cont0(deps: u64) -> RepeatN<SpecTypeidxCombinator> {
    let l = deps;
    RepeatN(spec_typeidx(), l.spec_into())
}
                
pub fn funcsec_content<'a>() -> (o: FuncsecContentCombinator<'a>)
    ensures o@ == spec_funcsec_content(),
{
    FuncsecContentCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: FuncsecContentCont0::new(), spec_snd: Ghost(|deps| spec_funcsec_content_cont0(deps)) },
        mapper: FuncsecContentMapper::new(),
    })
}

pub struct FuncsecContentCont0<'a>(PhantomData<&'a ()>);
impl<'a> FuncsecContentCont0<'a> {
    pub fn new() -> Self {
        FuncsecContentCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for FuncsecContentCont0<'a> {
    type Output = RepeatN<TypeidxCombinator>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_funcsec_content_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let l = *deps;
        RepeatN(typeidx(), l.ex_into())
    }
}
                

pub struct SpecFuncsec {
    pub size: u64,
    pub cont: SpecFuncsecContent,
}

pub type SpecFuncsecInner = (u64, SpecFuncsecContent);
impl SpecFrom<SpecFuncsec> for SpecFuncsecInner {
    open spec fn spec_from(m: SpecFuncsec) -> SpecFuncsecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecFuncsecInner> for SpecFuncsec {
    open spec fn spec_from(m: SpecFuncsecInner) -> SpecFuncsec {
        let (size, cont) = m;
        SpecFuncsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Funcsec {
    pub size: u64,
    pub cont: FuncsecContent,
}

impl View for Funcsec {
    type V = SpecFuncsec;

    open spec fn view(&self) -> Self::V {
        SpecFuncsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type FuncsecInner = (u64, FuncsecContent);
impl From<Funcsec> for FuncsecInner {
    fn ex_from(m: Funcsec) -> FuncsecInner {
        (m.size, m.cont)
    }
}
impl From<FuncsecInner> for Funcsec {
    fn ex_from(m: FuncsecInner) -> Funcsec {
        let (size, cont) = m;
        Funcsec { size, cont }
    }
}

pub struct FuncsecMapper;
impl FuncsecMapper {
    pub closed spec fn spec_new() -> Self {
        FuncsecMapper
    }
    pub fn new() -> Self {
        FuncsecMapper
    }
}
impl View for FuncsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FuncsecMapper {
    type Src = SpecFuncsecInner;
    type Dst = SpecFuncsec;
}
impl SpecIsoProof for FuncsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for FuncsecMapper {
    type Src = FuncsecInner;
    type Dst = Funcsec;
}

pub struct SpecFuncsecCombinator(SpecFuncsecCombinatorAlias);

impl SpecCombinator for SpecFuncsecCombinator {
    type Type = SpecFuncsec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFuncsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFuncsecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecFuncsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecFuncsecContentCombinator>>, FuncsecMapper>;

pub struct FuncsecCombinator<'a>(FuncsecCombinatorAlias<'a>);

impl<'a> View for FuncsecCombinator<'a> {
    type V = SpecFuncsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecFuncsecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for FuncsecCombinator<'a> {
    type Type = Funcsec;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type FuncsecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, FuncsecContentCombinator<'a>>, FuncsecCont0<'a>>, FuncsecMapper>;


pub closed spec fn spec_funcsec() -> SpecFuncsecCombinator {
    SpecFuncsecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_funcsec_cont0(deps) },
        mapper: FuncsecMapper::spec_new(),
    })
}

pub open spec fn spec_funcsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecFuncsecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_funcsec_content())
}
                
pub fn funcsec<'a>() -> (o: FuncsecCombinator<'a>)
    ensures o@ == spec_funcsec(),
{
    FuncsecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: FuncsecCont0::new(), spec_snd: Ghost(|deps| spec_funcsec_cont0(deps)) },
        mapper: FuncsecMapper::new(),
    })
}

pub struct FuncsecCont0<'a>(PhantomData<&'a ()>);
impl<'a> FuncsecCont0<'a> {
    pub fn new() -> Self {
        FuncsecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for FuncsecCont0<'a> {
    type Output = AndThen<bytes::Variable, FuncsecContentCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_funcsec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), funcsec_content())
    }
}
                

pub struct SpecElemsec {
    pub size: u64,
    pub cont: SpecElemsecContent,
}

pub type SpecElemsecInner = (u64, SpecElemsecContent);
impl SpecFrom<SpecElemsec> for SpecElemsecInner {
    open spec fn spec_from(m: SpecElemsec) -> SpecElemsecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecElemsecInner> for SpecElemsec {
    open spec fn spec_from(m: SpecElemsecInner) -> SpecElemsec {
        let (size, cont) = m;
        SpecElemsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Elemsec<'a> {
    pub size: u64,
    pub cont: ElemsecContent<'a>,
}

impl View for Elemsec<'_> {
    type V = SpecElemsec;

    open spec fn view(&self) -> Self::V {
        SpecElemsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type ElemsecInner<'a> = (u64, ElemsecContent<'a>);
impl<'a> From<Elemsec<'a>> for ElemsecInner<'a> {
    fn ex_from(m: Elemsec) -> ElemsecInner {
        (m.size, m.cont)
    }
}
impl<'a> From<ElemsecInner<'a>> for Elemsec<'a> {
    fn ex_from(m: ElemsecInner) -> Elemsec {
        let (size, cont) = m;
        Elemsec { size, cont }
    }
}

pub struct ElemsecMapper<'a>(PhantomData<&'a ()>);
impl<'a> ElemsecMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ElemsecMapper(PhantomData)
    }
    pub fn new() -> Self {
        ElemsecMapper(PhantomData)
    }
}
impl View for ElemsecMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ElemsecMapper<'_> {
    type Src = SpecElemsecInner;
    type Dst = SpecElemsec;
}
impl SpecIsoProof for ElemsecMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ElemsecMapper<'a> {
    type Src = ElemsecInner<'a>;
    type Dst = Elemsec<'a>;
}

pub struct SpecElemsecCombinator(SpecElemsecCombinatorAlias);

impl SpecCombinator for SpecElemsecCombinator {
    type Type = SpecElemsec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemsecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecElemsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecElemsecContentCombinator>>, ElemsecMapper<'static>>;

pub struct ElemsecCombinator<'a>(ElemsecCombinatorAlias<'a>);

impl<'a> View for ElemsecCombinator<'a> {
    type V = SpecElemsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemsecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ElemsecCombinator<'a> {
    type Type = Elemsec<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ElemsecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, ElemsecContentCombinator<'a>>, ElemsecCont0<'a>>, ElemsecMapper<'a>>;


pub closed spec fn spec_elemsec() -> SpecElemsecCombinator {
    SpecElemsecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_elemsec_cont0(deps) },
        mapper: ElemsecMapper::spec_new(),
    })
}

pub open spec fn spec_elemsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecElemsecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_elemsec_content())
}
                
pub fn elemsec<'a>() -> (o: ElemsecCombinator<'a>)
    ensures o@ == spec_elemsec(),
{
    ElemsecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: ElemsecCont0::new(), spec_snd: Ghost(|deps| spec_elemsec_cont0(deps)) },
        mapper: ElemsecMapper::new(),
    })
}

pub struct ElemsecCont0<'a>(PhantomData<&'a ()>);
impl<'a> ElemsecCont0<'a> {
    pub fn new() -> Self {
        ElemsecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for ElemsecCont0<'a> {
    type Output = AndThen<bytes::Variable, ElemsecContentCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_elemsec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), elemsec_content())
    }
}
                

pub struct SpecDatasec {
    pub size: u64,
    pub cont: SpecDatasecContent,
}

pub type SpecDatasecInner = (u64, SpecDatasecContent);
impl SpecFrom<SpecDatasec> for SpecDatasecInner {
    open spec fn spec_from(m: SpecDatasec) -> SpecDatasecInner {
        (m.size, m.cont)
    }
}
impl SpecFrom<SpecDatasecInner> for SpecDatasec {
    open spec fn spec_from(m: SpecDatasecInner) -> SpecDatasec {
        let (size, cont) = m;
        SpecDatasec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Datasec<'a> {
    pub size: u64,
    pub cont: DatasecContent<'a>,
}

impl View for Datasec<'_> {
    type V = SpecDatasec;

    open spec fn view(&self) -> Self::V {
        SpecDatasec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type DatasecInner<'a> = (u64, DatasecContent<'a>);
impl<'a> From<Datasec<'a>> for DatasecInner<'a> {
    fn ex_from(m: Datasec) -> DatasecInner {
        (m.size, m.cont)
    }
}
impl<'a> From<DatasecInner<'a>> for Datasec<'a> {
    fn ex_from(m: DatasecInner) -> Datasec {
        let (size, cont) = m;
        Datasec { size, cont }
    }
}

pub struct DatasecMapper<'a>(PhantomData<&'a ()>);
impl<'a> DatasecMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        DatasecMapper(PhantomData)
    }
    pub fn new() -> Self {
        DatasecMapper(PhantomData)
    }
}
impl View for DatasecMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DatasecMapper<'_> {
    type Src = SpecDatasecInner;
    type Dst = SpecDatasec;
}
impl SpecIsoProof for DatasecMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for DatasecMapper<'a> {
    type Src = DatasecInner<'a>;
    type Dst = Datasec<'a>;
}

pub struct SpecDatasecCombinator(SpecDatasecCombinatorAlias);

impl SpecCombinator for SpecDatasecCombinator {
    type Type = SpecDatasec;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDatasecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDatasecCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecDatasecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecDatasecContentCombinator>>, DatasecMapper<'static>>;

pub struct DatasecCombinator<'a>(DatasecCombinatorAlias<'a>);

impl<'a> View for DatasecCombinator<'a> {
    type V = SpecDatasecCombinator;
    closed spec fn view(&self) -> Self::V { SpecDatasecCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for DatasecCombinator<'a> {
    type Type = Datasec<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type DatasecCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, UnsignedLEB128, AndThen<bytes::Variable, DatasecContentCombinator<'a>>, DatasecCont0<'a>>, DatasecMapper<'a>>;


pub closed spec fn spec_datasec() -> SpecDatasecCombinator {
    SpecDatasecCombinator(
    Mapped {
        inner: SpecPair { fst: UnsignedLEB128, snd: |deps| spec_datasec_cont0(deps) },
        mapper: DatasecMapper::spec_new(),
    })
}

pub open spec fn spec_datasec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecDatasecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_datasec_content())
}
                
pub fn datasec<'a>() -> (o: DatasecCombinator<'a>)
    ensures o@ == spec_datasec(),
{
    DatasecCombinator(
    Mapped {
        inner: Pair { fst: UnsignedLEB128, snd: DatasecCont0::new(), spec_snd: Ghost(|deps| spec_datasec_cont0(deps)) },
        mapper: DatasecMapper::new(),
    })
}

pub struct DatasecCont0<'a>(PhantomData<&'a ()>);
impl<'a> DatasecCont0<'a> {
    pub fn new() -> Self {
        DatasecCont0(PhantomData)
    }
}
impl<'a> Continuation<&u64> for DatasecCont0<'a> {
    type Output = AndThen<bytes::Variable, DatasecContentCombinator<'a>>;

    open spec fn requires(&self, deps: &u64) -> bool { true }

    open spec fn ensures(&self, deps: &u64, o: Self::Output) -> bool {
        o@ == spec_datasec_cont0(deps@)
    }

    fn apply(&self, deps: &u64) -> Self::Output {
        let size = *deps;
        AndThen(bytes::Variable(size.ex_into()), datasec_content())
    }
}
                

pub struct SpecModule {
    pub magic: Seq<u8>,
    pub version: Seq<u8>,
    pub custom1: Option<SpecCustomsec>,
    pub types: Option<SpecTypesec>,
    pub custom2: Option<SpecCustomsec>,
    pub imports: Option<SpecImportsec>,
    pub custom3: Option<SpecCustomsec>,
    pub typeidxs: Option<SpecFuncsec>,
    pub custom4: Option<SpecCustomsec>,
    pub tables: Option<SpecTablesec>,
    pub custom5: Option<SpecCustomsec>,
    pub mems: Option<SpecMemsec>,
    pub custom6: Option<SpecCustomsec>,
    pub globals: Option<SpecGlobalsec>,
    pub custom7: Option<SpecCustomsec>,
    pub exports: Option<SpecExportsec>,
    pub custom8: Option<SpecCustomsec>,
    pub start: Option<SpecStartsec>,
    pub custom9: Option<SpecCustomsec>,
    pub elems: Option<SpecElemsec>,
    pub custom10: Option<SpecCustomsec>,
    pub datacount: Option<SpecDatacountsec>,
    pub custom11: Option<SpecCustomsec>,
    pub codes: Option<SpecCodesec>,
    pub custom12: Option<SpecCustomsec>,
    pub datas: Option<SpecDatasec>,
    pub custom13: Option<SpecCustomsec>,
}

pub type SpecModuleInner = (Seq<u8>, (Seq<u8>, (Option<SpecCustomsec>, (Option<SpecTypesec>, (Option<SpecCustomsec>, (Option<SpecImportsec>, (Option<SpecCustomsec>, (Option<SpecFuncsec>, (Option<SpecCustomsec>, (Option<SpecTablesec>, (Option<SpecCustomsec>, (Option<SpecMemsec>, (Option<SpecCustomsec>, (Option<SpecGlobalsec>, (Option<SpecCustomsec>, (Option<SpecExportsec>, (Option<SpecCustomsec>, (Option<SpecStartsec>, (Option<SpecCustomsec>, (Option<SpecElemsec>, (Option<SpecCustomsec>, (Option<SpecDatacountsec>, (Option<SpecCustomsec>, (Option<SpecCodesec>, (Option<SpecCustomsec>, (Option<SpecDatasec>, Option<SpecCustomsec>))))))))))))))))))))))))));
impl SpecFrom<SpecModule> for SpecModuleInner {
    open spec fn spec_from(m: SpecModule) -> SpecModuleInner {
        (m.magic, (m.version, (m.custom1, (m.types, (m.custom2, (m.imports, (m.custom3, (m.typeidxs, (m.custom4, (m.tables, (m.custom5, (m.mems, (m.custom6, (m.globals, (m.custom7, (m.exports, (m.custom8, (m.start, (m.custom9, (m.elems, (m.custom10, (m.datacount, (m.custom11, (m.codes, (m.custom12, (m.datas, m.custom13))))))))))))))))))))))))))
    }
}
impl SpecFrom<SpecModuleInner> for SpecModule {
    open spec fn spec_from(m: SpecModuleInner) -> SpecModule {
        let (magic, (version, (custom1, (types, (custom2, (imports, (custom3, (typeidxs, (custom4, (tables, (custom5, (mems, (custom6, (globals, (custom7, (exports, (custom8, (start, (custom9, (elems, (custom10, (datacount, (custom11, (codes, (custom12, (datas, custom13)))))))))))))))))))))))))) = m;
        SpecModule { magic, version, custom1, types, custom2, imports, custom3, typeidxs, custom4, tables, custom5, mems, custom6, globals, custom7, exports, custom8, start, custom9, elems, custom10, datacount, custom11, codes, custom12, datas, custom13 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Module<'a> {
    pub magic: &'a [u8],
    pub version: &'a [u8],
    pub custom1: Optional<Customsec>,
    pub types: Optional<Typesec>,
    pub custom2: Optional<Customsec>,
    pub imports: Optional<Importsec>,
    pub custom3: Optional<Customsec>,
    pub typeidxs: Optional<Funcsec>,
    pub custom4: Optional<Customsec>,
    pub tables: Optional<Tablesec>,
    pub custom5: Optional<Customsec>,
    pub mems: Optional<Memsec>,
    pub custom6: Optional<Customsec>,
    pub globals: Optional<Globalsec<'a>>,
    pub custom7: Optional<Customsec>,
    pub exports: Optional<Exportsec>,
    pub custom8: Optional<Customsec>,
    pub start: Optional<Startsec>,
    pub custom9: Optional<Customsec>,
    pub elems: Optional<Elemsec<'a>>,
    pub custom10: Optional<Customsec>,
    pub datacount: Optional<Datacountsec>,
    pub custom11: Optional<Customsec>,
    pub codes: Optional<Codesec<'a>>,
    pub custom12: Optional<Customsec>,
    pub datas: Optional<Datasec<'a>>,
    pub custom13: Optional<Customsec>,
}

impl View for Module<'_> {
    type V = SpecModule;

    open spec fn view(&self) -> Self::V {
        SpecModule {
            magic: self.magic@,
            version: self.version@,
            custom1: self.custom1@,
            types: self.types@,
            custom2: self.custom2@,
            imports: self.imports@,
            custom3: self.custom3@,
            typeidxs: self.typeidxs@,
            custom4: self.custom4@,
            tables: self.tables@,
            custom5: self.custom5@,
            mems: self.mems@,
            custom6: self.custom6@,
            globals: self.globals@,
            custom7: self.custom7@,
            exports: self.exports@,
            custom8: self.custom8@,
            start: self.start@,
            custom9: self.custom9@,
            elems: self.elems@,
            custom10: self.custom10@,
            datacount: self.datacount@,
            custom11: self.custom11@,
            codes: self.codes@,
            custom12: self.custom12@,
            datas: self.datas@,
            custom13: self.custom13@,
        }
    }
}
pub type ModuleInner<'a> = (&'a [u8], (&'a [u8], (Optional<Customsec>, (Optional<Typesec>, (Optional<Customsec>, (Optional<Importsec>, (Optional<Customsec>, (Optional<Funcsec>, (Optional<Customsec>, (Optional<Tablesec>, (Optional<Customsec>, (Optional<Memsec>, (Optional<Customsec>, (Optional<Globalsec<'a>>, (Optional<Customsec>, (Optional<Exportsec>, (Optional<Customsec>, (Optional<Startsec>, (Optional<Customsec>, (Optional<Elemsec<'a>>, (Optional<Customsec>, (Optional<Datacountsec>, (Optional<Customsec>, (Optional<Codesec<'a>>, (Optional<Customsec>, (Optional<Datasec<'a>>, Optional<Customsec>))))))))))))))))))))))))));
impl<'a> From<Module<'a>> for ModuleInner<'a> {
    fn ex_from(m: Module) -> ModuleInner {
        (m.magic, (m.version, (m.custom1, (m.types, (m.custom2, (m.imports, (m.custom3, (m.typeidxs, (m.custom4, (m.tables, (m.custom5, (m.mems, (m.custom6, (m.globals, (m.custom7, (m.exports, (m.custom8, (m.start, (m.custom9, (m.elems, (m.custom10, (m.datacount, (m.custom11, (m.codes, (m.custom12, (m.datas, m.custom13))))))))))))))))))))))))))
    }
}
impl<'a> From<ModuleInner<'a>> for Module<'a> {
    fn ex_from(m: ModuleInner) -> Module {
        let (magic, (version, (custom1, (types, (custom2, (imports, (custom3, (typeidxs, (custom4, (tables, (custom5, (mems, (custom6, (globals, (custom7, (exports, (custom8, (start, (custom9, (elems, (custom10, (datacount, (custom11, (codes, (custom12, (datas, custom13)))))))))))))))))))))))))) = m;
        Module { magic, version, custom1, types, custom2, imports, custom3, typeidxs, custom4, tables, custom5, mems, custom6, globals, custom7, exports, custom8, start, custom9, elems, custom10, datacount, custom11, codes, custom12, datas, custom13 }
    }
}

pub struct ModuleMapper<'a>(PhantomData<&'a ()>);
impl<'a> ModuleMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ModuleMapper(PhantomData)
    }
    pub fn new() -> Self {
        ModuleMapper(PhantomData)
    }
}
impl View for ModuleMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ModuleMapper<'_> {
    type Src = SpecModuleInner;
    type Dst = SpecModule;
}
impl SpecIsoProof for ModuleMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ModuleMapper<'a> {
    type Src = ModuleInner<'a>;
    type Dst = Module<'a>;
}
pub spec const SPEC_MODULEMAGIC_CONST: Seq<u8> = seq![0, 97, 115, 109];pub spec const SPEC_MODULEVERSION_CONST: Seq<u8> = seq![1, 0, 0, 0];pub const MODULECUSTOM1_0_FRONT_CONST: u8 = 0;

pub const MODULETYPES_0_FRONT_CONST: u8 = 1;

pub const MODULECUSTOM2_0_FRONT_CONST: u8 = 0;

pub const MODULEIMPORTS_0_FRONT_CONST: u8 = 2;

pub const MODULECUSTOM3_0_FRONT_CONST: u8 = 0;

pub const MODULETYPEIDXS_0_FRONT_CONST: u8 = 3;

pub const MODULECUSTOM4_0_FRONT_CONST: u8 = 0;

pub const MODULETABLES_0_FRONT_CONST: u8 = 4;

pub const MODULECUSTOM5_0_FRONT_CONST: u8 = 0;

pub const MODULEMEMS_0_FRONT_CONST: u8 = 5;

pub const MODULECUSTOM6_0_FRONT_CONST: u8 = 0;

pub const MODULEGLOBALS_0_FRONT_CONST: u8 = 6;

pub const MODULECUSTOM7_0_FRONT_CONST: u8 = 0;

pub const MODULEEXPORTS_0_FRONT_CONST: u8 = 7;

pub const MODULECUSTOM8_0_FRONT_CONST: u8 = 0;

pub const MODULESTART_0_FRONT_CONST: u8 = 8;

pub const MODULECUSTOM9_0_FRONT_CONST: u8 = 0;

pub const MODULEELEMS_0_FRONT_CONST: u8 = 9;

pub const MODULECUSTOM10_0_FRONT_CONST: u8 = 0;

pub const MODULEDATACOUNT_0_FRONT_CONST: u8 = 12;

pub const MODULECUSTOM11_0_FRONT_CONST: u8 = 0;

pub const MODULECODES_0_FRONT_CONST: u8 = 10;

pub const MODULECUSTOM12_0_FRONT_CONST: u8 = 0;

pub const MODULEDATAS_0_FRONT_CONST: u8 = 11;

pub const MODULECUSTOM13_0_FRONT_CONST: u8 = 0;


pub struct SpecModuleCombinator(SpecModuleCombinatorAlias);

impl SpecCombinator for SpecModuleCombinator {
    type Type = SpecModule;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecModuleCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecModuleCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecModuleCombinatorAlias = Mapped<(Refined<bytes::Fixed<4>, TagPred<Seq<u8>>>, (Refined<bytes::Fixed<4>, TagPred<Seq<u8>>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecTypesecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecImportsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecFuncsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecTablesecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecMemsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecGlobalsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecExportsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecStartsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecElemsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecDatacountsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCodesecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecDatasecCombinator>>, Opt<Preceded<Tag<U8, u8>, SpecCustomsecCombinator>>)))))))))))))))))))))))))), ModuleMapper<'static>>;
pub exec static MODULEMAGIC_CONST: [u8; 4]
    ensures MODULEMAGIC_CONST@ == SPEC_MODULEMAGIC_CONST,
{
    let arr: [u8; 4] = [0, 97, 115, 109];
    assert(arr@ == SPEC_MODULEMAGIC_CONST);
    arr
}
pub exec static MODULEVERSION_CONST: [u8; 4]
    ensures MODULEVERSION_CONST@ == SPEC_MODULEVERSION_CONST,
{
    let arr: [u8; 4] = [1, 0, 0, 0];
    assert(arr@ == SPEC_MODULEVERSION_CONST);
    arr
}


























pub struct ModuleCombinator<'a>(ModuleCombinatorAlias<'a>);

impl<'a> View for ModuleCombinator<'a> {
    type V = SpecModuleCombinator;
    closed spec fn view(&self) -> Self::V { SpecModuleCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ModuleCombinator<'a> {
    type Type = Module<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ModuleCombinatorAlias<'a> = Mapped<(Refined<bytes::Fixed<4>, TagPred<&'a [u8]>>, (Refined<bytes::Fixed<4>, TagPred<&'a [u8]>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, TypesecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, ImportsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, FuncsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, TablesecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, MemsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, GlobalsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, ExportsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, StartsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, ElemsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, DatacountsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CodesecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>, (Opt<Preceded<Tag<U8, u8>, DatasecCombinator<'a>>>, Opt<Preceded<Tag<U8, u8>, CustomsecCombinator<'a>>>)))))))))))))))))))))))))), ModuleMapper<'a>>;


pub closed spec fn spec_module() -> SpecModuleCombinator {
    SpecModuleCombinator(
    Mapped {
        inner: (Refined { inner: bytes::Fixed::<4>, predicate: TagPred(SPEC_MODULEMAGIC_CONST) }, (Refined { inner: bytes::Fixed::<4>, predicate: TagPred(SPEC_MODULEVERSION_CONST) }, (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM1_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULETYPES_0_FRONT_CONST), spec_typesec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM2_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULEIMPORTS_0_FRONT_CONST), spec_importsec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM3_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULETYPEIDXS_0_FRONT_CONST), spec_funcsec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM4_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULETABLES_0_FRONT_CONST), spec_tablesec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM5_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULEMEMS_0_FRONT_CONST), spec_memsec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM6_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULEGLOBALS_0_FRONT_CONST), spec_globalsec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM7_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULEEXPORTS_0_FRONT_CONST), spec_exportsec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM8_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULESTART_0_FRONT_CONST), spec_startsec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM9_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULEELEMS_0_FRONT_CONST), spec_elemsec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM10_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULEDATACOUNT_0_FRONT_CONST), spec_datacountsec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM11_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULECODES_0_FRONT_CONST), spec_codesec())), (Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM12_0_FRONT_CONST), spec_customsec())), (Opt(Preceded(Tag::spec_new(U8, MODULEDATAS_0_FRONT_CONST), spec_datasec())), Opt(Preceded(Tag::spec_new(U8, MODULECUSTOM13_0_FRONT_CONST), spec_customsec())))))))))))))))))))))))))))),
        mapper: ModuleMapper::spec_new(),
    })
}

                
pub fn module<'a>() -> (o: ModuleCombinator<'a>)
    ensures o@ == spec_module(),
{
    ModuleCombinator(
    Mapped {
        inner: (Refined { inner: bytes::Fixed::<4>, predicate: TagPred(MODULEMAGIC_CONST.as_slice()) }, (Refined { inner: bytes::Fixed::<4>, predicate: TagPred(MODULEVERSION_CONST.as_slice()) }, (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM1_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULETYPES_0_FRONT_CONST), typesec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM2_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULEIMPORTS_0_FRONT_CONST), importsec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM3_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULETYPEIDXS_0_FRONT_CONST), funcsec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM4_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULETABLES_0_FRONT_CONST), tablesec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM5_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULEMEMS_0_FRONT_CONST), memsec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM6_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULEGLOBALS_0_FRONT_CONST), globalsec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM7_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULEEXPORTS_0_FRONT_CONST), exportsec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM8_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULESTART_0_FRONT_CONST), startsec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM9_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULEELEMS_0_FRONT_CONST), elemsec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM10_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULEDATACOUNT_0_FRONT_CONST), datacountsec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM11_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULECODES_0_FRONT_CONST), codesec())), (Opt::new(Preceded(Tag::new(U8, MODULECUSTOM12_0_FRONT_CONST), customsec())), (Opt::new(Preceded(Tag::new(U8, MODULEDATAS_0_FRONT_CONST), datasec())), Opt::new(Preceded(Tag::new(U8, MODULECUSTOM13_0_FRONT_CONST), customsec())))))))))))))))))))))))))))),
        mapper: ModuleMapper::new(),
    })
}

                

}
