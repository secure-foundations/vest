
#![allow(warnings)]
#![allow(unused)]
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

macro_rules! impl_wrapper_combinator {
    ($combinator:ty, $combinator_alias:ty) => {
        ::vstd::prelude::verus! {
            impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for $combinator {
                type Type = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
                type SType = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
                fn length(&self, v: Self::SType) -> usize
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
                closed spec fn ex_requires(&self) -> bool
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
                fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
                fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
            }
        } // verus!
    };
}
verus!{

pub struct SpecMsg1 {
    pub a: u8,
    pub b: u16,
    pub c: Seq<u8>,
}

pub type SpecMsg1Inner = (u8, (u16, Seq<u8>));


impl SpecFrom<SpecMsg1> for SpecMsg1Inner {
    open spec fn spec_from(m: SpecMsg1) -> SpecMsg1Inner {
        (m.a, (m.b, m.c))
    }
}

impl SpecFrom<SpecMsg1Inner> for SpecMsg1 {
    open spec fn spec_from(m: SpecMsg1Inner) -> SpecMsg1 {
        let (a, (b, c)) = m;
        SpecMsg1 { a, b, c }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg1<'a> {
    pub a: u8,
    pub b: u16,
    pub c: &'a [u8],
}

impl View for Msg1<'_> {
    type V = SpecMsg1;

    open spec fn view(&self) -> Self::V {
        SpecMsg1 {
            a: self.a@,
            b: self.b@,
            c: self.c@,
        }
    }
}
pub type Msg1Inner<'a> = (u8, (u16, &'a [u8]));

pub type Msg1InnerRef<'a> = (&'a u8, (&'a u16, &'a &'a [u8]));
impl<'a> From<&'a Msg1<'a>> for Msg1InnerRef<'a> {
    fn ex_from(m: &'a Msg1) -> Msg1InnerRef<'a> {
        (&m.a, (&m.b, &m.c))
    }
}

impl<'a> From<Msg1Inner<'a>> for Msg1<'a> {
    fn ex_from(m: Msg1Inner) -> Msg1 {
        let (a, (b, c)) = m;
        Msg1 { a, b, c }
    }
}

pub struct Msg1Mapper;
impl View for Msg1Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg1Mapper {
    type Src = SpecMsg1Inner;
    type Dst = SpecMsg1;
}
impl SpecIsoProof for Msg1Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg1Mapper {
    type Src = Msg1Inner<'a>;
    type Dst = Msg1<'a>;
    type RefSrc = Msg1InnerRef<'a>;
}
type SpecMsg1CombinatorAlias1 = (U16Le, bytes::Fixed<3>);
type SpecMsg1CombinatorAlias2 = (Refined<U8, Predicate15164968237706789291>, SpecMsg1CombinatorAlias1);
pub struct SpecMsg1Combinator(SpecMsg1CombinatorAlias);

impl SpecCombinator for SpecMsg1Combinator {
    type Type = SpecMsg1;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg1Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg1CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg1CombinatorAlias = Mapped<SpecMsg1CombinatorAlias2, Msg1Mapper>;
pub struct Predicate15164968237706789291;
impl View for Predicate15164968237706789291 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate15164968237706789291 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 0 && i <= 10) || (i == 32) || (i >= 100)
    }
}
impl SpecPred<u8> for Predicate15164968237706789291 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 0 && i <= 10) || (i == 32) || (i >= 100)
    }
}
type Msg1CombinatorAlias1 = (U16Le, bytes::Fixed<3>);
type Msg1CombinatorAlias2 = (Refined<U8, Predicate15164968237706789291>, Msg1Combinator1);
struct Msg1Combinator1(Msg1CombinatorAlias1);
impl View for Msg1Combinator1 {
    type V = SpecMsg1CombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg1Combinator1, Msg1CombinatorAlias1);

struct Msg1Combinator2(Msg1CombinatorAlias2);
impl View for Msg1Combinator2 {
    type V = SpecMsg1CombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg1Combinator2, Msg1CombinatorAlias2);

pub struct Msg1Combinator(Msg1CombinatorAlias);

impl View for Msg1Combinator {
    type V = SpecMsg1Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg1Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg1Combinator {
    type Type = Msg1<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Msg1CombinatorAlias = Mapped<Msg1Combinator2, Msg1Mapper>;


pub closed spec fn spec_msg1() -> SpecMsg1Combinator {
    SpecMsg1Combinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate15164968237706789291 }, (U16Le, bytes::Fixed::<3>)),
        mapper: Msg1Mapper,
    })
}

                
pub fn msg1<'a>() -> (o: Msg1Combinator)
    ensures o@ == spec_msg1(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg1Combinator(
    Mapped {
        inner: Msg1Combinator2((Refined { inner: U8, predicate: Predicate15164968237706789291 }, Msg1Combinator1((U16Le, bytes::Fixed::<3>)))),
        mapper: Msg1Mapper,
    });
    assert({
        &&& combinator@ == spec_msg1()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_msg1<'a>(input: &'a [u8]) -> (res: PResult<<Msg1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_msg1().spec_parse(input@) == Some((n as int, v@)),
        spec_msg1().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg1().spec_parse(input@) is None,
        spec_msg1().spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg1<'a>(v: <Msg1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg1().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg1().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg1().spec_serialize(v@))
        },
{
    let combinator = msg1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn msg1_len<'a>(v: <Msg1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (len: usize)
    requires
        spec_msg1().wf(v@),
        spec_msg1().spec_serialize(v@).len() <= usize::MAX,
    ensures
        len == spec_msg1().spec_serialize(v@).len(),
{
    let combinator = msg1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecMsg3 = Seq<u8>;
pub type Msg3<'a> = &'a [u8];
pub type Msg3Ref<'a> = &'a &'a [u8];


pub struct SpecMsg3Combinator(SpecMsg3CombinatorAlias);

impl SpecCombinator for SpecMsg3Combinator {
    type Type = SpecMsg3;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg3Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg3CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg3CombinatorAlias = bytes::Fixed<6>;

pub struct Msg3Combinator(Msg3CombinatorAlias);

impl View for Msg3Combinator {
    type V = SpecMsg3Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg3Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg3Combinator {
    type Type = Msg3<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Msg3CombinatorAlias = bytes::Fixed<6>;


pub closed spec fn spec_msg3() -> SpecMsg3Combinator {
    SpecMsg3Combinator(bytes::Fixed::<6>)
}

                
pub fn msg3<'a>() -> (o: Msg3Combinator)
    ensures o@ == spec_msg3(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg3Combinator(bytes::Fixed::<6>);
    assert({
        &&& combinator@ == spec_msg3()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_msg3<'a>(input: &'a [u8]) -> (res: PResult<<Msg3Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_msg3().spec_parse(input@) == Some((n as int, v@)),
        spec_msg3().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg3().spec_parse(input@) is None,
        spec_msg3().spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg3();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg3<'a>(v: <Msg3Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg3().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg3().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg3().spec_serialize(v@))
        },
{
    let combinator = msg3();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn msg3_len<'a>(v: <Msg3Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (len: usize)
    requires
        spec_msg3().wf(v@),
        spec_msg3().spec_serialize(v@).len() <= usize::MAX,
    ensures
        len == spec_msg3().spec_serialize(v@).len(),
{
    let combinator = msg3();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecMsg2 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

pub type SpecMsg2Inner = (u8, (u16, u32));


impl SpecFrom<SpecMsg2> for SpecMsg2Inner {
    open spec fn spec_from(m: SpecMsg2) -> SpecMsg2Inner {
        (m.a, (m.b, m.c))
    }
}

impl SpecFrom<SpecMsg2Inner> for SpecMsg2 {
    open spec fn spec_from(m: SpecMsg2Inner) -> SpecMsg2 {
        let (a, (b, c)) = m;
        SpecMsg2 { a, b, c }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg2 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

impl View for Msg2 {
    type V = SpecMsg2;

    open spec fn view(&self) -> Self::V {
        SpecMsg2 {
            a: self.a@,
            b: self.b@,
            c: self.c@,
        }
    }
}
pub type Msg2Inner = (u8, (u16, u32));

pub type Msg2InnerRef<'a> = (&'a u8, (&'a u16, &'a u32));
impl<'a> From<&'a Msg2> for Msg2InnerRef<'a> {
    fn ex_from(m: &'a Msg2) -> Msg2InnerRef<'a> {
        (&m.a, (&m.b, &m.c))
    }
}

impl From<Msg2Inner> for Msg2 {
    fn ex_from(m: Msg2Inner) -> Msg2 {
        let (a, (b, c)) = m;
        Msg2 { a, b, c }
    }
}

pub struct Msg2Mapper;
impl View for Msg2Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg2Mapper {
    type Src = SpecMsg2Inner;
    type Dst = SpecMsg2;
}
impl SpecIsoProof for Msg2Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg2Mapper {
    type Src = Msg2Inner;
    type Dst = Msg2;
    type RefSrc = Msg2InnerRef<'a>;
}
type SpecMsg2CombinatorAlias1 = (U16Le, U32Le);
type SpecMsg2CombinatorAlias2 = (U8, SpecMsg2CombinatorAlias1);
pub struct SpecMsg2Combinator(SpecMsg2CombinatorAlias);

impl SpecCombinator for SpecMsg2Combinator {
    type Type = SpecMsg2;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg2Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg2CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg2CombinatorAlias = Mapped<SpecMsg2CombinatorAlias2, Msg2Mapper>;
type Msg2CombinatorAlias1 = (U16Le, U32Le);
type Msg2CombinatorAlias2 = (U8, Msg2Combinator1);
struct Msg2Combinator1(Msg2CombinatorAlias1);
impl View for Msg2Combinator1 {
    type V = SpecMsg2CombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg2Combinator1, Msg2CombinatorAlias1);

struct Msg2Combinator2(Msg2CombinatorAlias2);
impl View for Msg2Combinator2 {
    type V = SpecMsg2CombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg2Combinator2, Msg2CombinatorAlias2);

pub struct Msg2Combinator(Msg2CombinatorAlias);

impl View for Msg2Combinator {
    type V = SpecMsg2Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg2Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg2Combinator {
    type Type = Msg2;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Msg2CombinatorAlias = Mapped<Msg2Combinator2, Msg2Mapper>;


pub closed spec fn spec_msg2() -> SpecMsg2Combinator {
    SpecMsg2Combinator(
    Mapped {
        inner: (U8, (U16Le, U32Le)),
        mapper: Msg2Mapper,
    })
}

                
pub fn msg2<'a>() -> (o: Msg2Combinator)
    ensures o@ == spec_msg2(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg2Combinator(
    Mapped {
        inner: Msg2Combinator2((U8, Msg2Combinator1((U16Le, U32Le)))),
        mapper: Msg2Mapper,
    });
    assert({
        &&& combinator@ == spec_msg2()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_msg2<'a>(input: &'a [u8]) -> (res: PResult<<Msg2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_msg2().spec_parse(input@) == Some((n as int, v@)),
        spec_msg2().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg2().spec_parse(input@) is None,
        spec_msg2().spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg2<'a>(v: <Msg2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg2().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg2().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg2().spec_serialize(v@))
        },
{
    let combinator = msg2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn msg2_len<'a>(v: <Msg2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (len: usize)
    requires
        spec_msg2().wf(v@),
        spec_msg2().spec_serialize(v@).len() <= usize::MAX,
    ensures
        len == spec_msg2().spec_serialize(v@).len(),
{
    let combinator = msg2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecMsg4V {
    A(SpecMsg1),
    B(SpecMsg2),
    C(SpecMsg3),
}

pub type SpecMsg4VInner = Either<SpecMsg1, Either<SpecMsg2, SpecMsg3>>;

impl SpecFrom<SpecMsg4V> for SpecMsg4VInner {
    open spec fn spec_from(m: SpecMsg4V) -> SpecMsg4VInner {
        match m {
            SpecMsg4V::A(m) => Either::Left(m),
            SpecMsg4V::B(m) => Either::Right(Either::Left(m)),
            SpecMsg4V::C(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecMsg4VInner> for SpecMsg4V {
    open spec fn spec_from(m: SpecMsg4VInner) -> SpecMsg4V {
        match m {
            Either::Left(m) => SpecMsg4V::A(m),
            Either::Right(Either::Left(m)) => SpecMsg4V::B(m),
            Either::Right(Either::Right(m)) => SpecMsg4V::C(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg4V<'a> {
    A(Msg1<'a>),
    B(Msg2),
    C(Msg3<'a>),
}

pub type Msg4VInner<'a> = Either<Msg1<'a>, Either<Msg2, Msg3<'a>>>;

pub type Msg4VInnerRef<'a> = Either<&'a Msg1<'a>, Either<&'a Msg2, &'a Msg3<'a>>>;


impl<'a> View for Msg4V<'a> {
    type V = SpecMsg4V;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg4V::A(m) => SpecMsg4V::A(m@),
            Msg4V::B(m) => SpecMsg4V::B(m@),
            Msg4V::C(m) => SpecMsg4V::C(m@),
        }
    }
}


impl<'a> From<&'a Msg4V<'a>> for Msg4VInnerRef<'a> {
    fn ex_from(m: &'a Msg4V<'a>) -> Msg4VInnerRef<'a> {
        match m {
            Msg4V::A(m) => Either::Left(m),
            Msg4V::B(m) => Either::Right(Either::Left(m)),
            Msg4V::C(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<Msg4VInner<'a>> for Msg4V<'a> {
    fn ex_from(m: Msg4VInner<'a>) -> Msg4V<'a> {
        match m {
            Either::Left(m) => Msg4V::A(m),
            Either::Right(Either::Left(m)) => Msg4V::B(m),
            Either::Right(Either::Right(m)) => Msg4V::C(m),
        }
    }
    
}


pub struct Msg4VMapper;
impl View for Msg4VMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg4VMapper {
    type Src = SpecMsg4VInner;
    type Dst = SpecMsg4V;
}
impl SpecIsoProof for Msg4VMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg4VMapper {
    type Src = Msg4VInner<'a>;
    type Dst = Msg4V<'a>;
    type RefSrc = Msg4VInnerRef<'a>;
}

type SpecMsg4VCombinatorAlias1 = Choice<Cond<SpecMsg2Combinator>, Cond<SpecMsg3Combinator>>;
type SpecMsg4VCombinatorAlias2 = Choice<Cond<SpecMsg1Combinator>, SpecMsg4VCombinatorAlias1>;
pub struct SpecMsg4VCombinator(SpecMsg4VCombinatorAlias);

impl SpecCombinator for SpecMsg4VCombinator {
    type Type = SpecMsg4V;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg4VCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg4VCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg4VCombinatorAlias = Mapped<SpecMsg4VCombinatorAlias2, Msg4VMapper>;
type Msg4VCombinatorAlias1 = Choice<Cond<Msg2Combinator>, Cond<Msg3Combinator>>;
type Msg4VCombinatorAlias2 = Choice<Cond<Msg1Combinator>, Msg4VCombinator1>;
struct Msg4VCombinator1(Msg4VCombinatorAlias1);
impl View for Msg4VCombinator1 {
    type V = SpecMsg4VCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg4VCombinator1, Msg4VCombinatorAlias1);

struct Msg4VCombinator2(Msg4VCombinatorAlias2);
impl View for Msg4VCombinator2 {
    type V = SpecMsg4VCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg4VCombinator2, Msg4VCombinatorAlias2);

pub struct Msg4VCombinator(Msg4VCombinatorAlias);

impl View for Msg4VCombinator {
    type V = SpecMsg4VCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg4VCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg4VCombinator {
    type Type = Msg4V<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Msg4VCombinatorAlias = Mapped<Msg4VCombinator2, Msg4VMapper>;


pub closed spec fn spec_msg4_v(t: SpecAType) -> SpecMsg4VCombinator {
    SpecMsg4VCombinator(Mapped { inner: Choice(Cond { cond: t == AType::A, inner: spec_msg1() }, Choice(Cond { cond: t == AType::B, inner: spec_msg2() }, Cond { cond: t == AType::C, inner: spec_msg3() })), mapper: Msg4VMapper })
}

pub fn msg4_v<'a>(t: AType) -> (o: Msg4VCombinator)
    ensures o@ == spec_msg4_v(t@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg4VCombinator(Mapped { inner: Msg4VCombinator2(Choice::new(Cond { cond: t == AType::A, inner: msg1() }, Msg4VCombinator1(Choice::new(Cond { cond: t == AType::B, inner: msg2() }, Cond { cond: t == AType::C, inner: msg3() })))), mapper: Msg4VMapper });
    assert({
        &&& combinator@ == spec_msg4_v(t@)
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_msg4_v<'a>(input: &'a [u8], t: AType) -> (res: PResult<<Msg4VCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_msg4_v(t@).spec_parse(input@) == Some((n as int, v@)),
        spec_msg4_v(t@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg4_v(t@).spec_parse(input@) is None,
        spec_msg4_v(t@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg4_v( t );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg4_v<'a>(v: <Msg4VCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, t: AType) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg4_v(t@).wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg4_v(t@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg4_v(t@).spec_serialize(v@))
        },
{
    let combinator = msg4_v( t );
    combinator.serialize(v, data, pos)
}

pub fn msg4_v_len<'a>(v: <Msg4VCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, t: AType) -> (len: usize)
    requires
        spec_msg4_v(t@).wf(v@),
        spec_msg4_v(t@).spec_serialize(v@).len() <= usize::MAX,
    ensures
        len == spec_msg4_v(t@).spec_serialize(v@).len(),
{
    let combinator = msg4_v( t );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub spec const SPEC_AType_A: u8 = 0;
pub spec const SPEC_AType_B: u8 = 1;
pub spec const SPEC_AType_C: u8 = 2;
pub exec static EXEC_AType_A: u8 ensures EXEC_AType_A == SPEC_AType_A { 0 }
pub exec static EXEC_AType_B: u8 ensures EXEC_AType_B == SPEC_AType_B { 1 }
pub exec static EXEC_AType_C: u8 ensures EXEC_AType_C == SPEC_AType_C { 2 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AType {
    A = 0,
B = 1,
C = 2
}
pub type SpecAType = AType;

pub type ATypeInner = u8;

pub type ATypeInnerRef<'a> = &'a u8;

impl View for AType {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<ATypeInner> for AType {
    type Error = ();

    open spec fn spec_try_from(v: ATypeInner) -> Result<AType, ()> {
        match v {
            0u8 => Ok(AType::A),
            1u8 => Ok(AType::B),
            2u8 => Ok(AType::C),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AType> for ATypeInner {
    type Error = ();

    open spec fn spec_try_from(v: AType) -> Result<ATypeInner, ()> {
        match v {
            AType::A => Ok(SPEC_AType_A),
            AType::B => Ok(SPEC_AType_B),
            AType::C => Ok(SPEC_AType_C),
        }
    }
}

impl TryFrom<ATypeInner> for AType {
    type Error = ();

    fn ex_try_from(v: ATypeInner) -> Result<AType, ()> {
        match v {
            0u8 => Ok(AType::A),
            1u8 => Ok(AType::B),
            2u8 => Ok(AType::C),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a AType> for ATypeInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a AType) -> Result<ATypeInnerRef<'a>, ()> {
        match v {
            AType::A => Ok(&EXEC_AType_A),
            AType::B => Ok(&EXEC_AType_B),
            AType::C => Ok(&EXEC_AType_C),
        }
    }
}

pub struct ATypeMapper;

impl View for ATypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for ATypeMapper {
    type Src = ATypeInner;
    type Dst = AType;
}

impl SpecPartialIsoProof for ATypeMapper {
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

impl<'a> PartialIso<'a> for ATypeMapper {
    type Src = ATypeInner;
    type Dst = AType;
    type RefSrc = ATypeInnerRef<'a>;
}


pub struct SpecATypeCombinator(SpecATypeCombinatorAlias);

impl SpecCombinator for SpecATypeCombinator {
    type Type = SpecAType;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecATypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecATypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecATypeCombinatorAlias = TryMap<U8, ATypeMapper>;

pub struct ATypeCombinator(ATypeCombinatorAlias);

impl View for ATypeCombinator {
    type V = SpecATypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecATypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ATypeCombinator {
    type Type = AType;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ATypeCombinatorAlias = TryMap<U8, ATypeMapper>;


pub closed spec fn spec_a_type() -> SpecATypeCombinator {
    SpecATypeCombinator(TryMap { inner: U8, mapper: ATypeMapper })
}

                
pub fn a_type<'a>() -> (o: ATypeCombinator)
    ensures o@ == spec_a_type(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ATypeCombinator(TryMap { inner: U8, mapper: ATypeMapper });
    assert({
        &&& combinator@ == spec_a_type()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_a_type<'a>(input: &'a [u8]) -> (res: PResult<<ATypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_type().spec_parse(input@) == Some((n as int, v@)),
        spec_a_type().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_type().spec_parse(input@) is None,
        spec_a_type().spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_type<'a>(v: <ATypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_type().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_type().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_type().spec_serialize(v@))
        },
{
    let combinator = a_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn a_type_len<'a>(v: <ATypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (len: usize)
    requires
        spec_a_type().wf(v@),
        spec_a_type().spec_serialize(v@).len() <= usize::MAX,
    ensures
        len == spec_a_type().spec_serialize(v@).len(),
{
    let combinator = a_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecMsg4 {
    pub t: SpecAType,
    pub v: SpecMsg4V,
    pub tail: Seq<u8>,
}

pub type SpecMsg4Inner = (SpecAType, (SpecMsg4V, Seq<u8>));


impl SpecFrom<SpecMsg4> for SpecMsg4Inner {
    open spec fn spec_from(m: SpecMsg4) -> SpecMsg4Inner {
        (m.t, (m.v, m.tail))
    }
}

impl SpecFrom<SpecMsg4Inner> for SpecMsg4 {
    open spec fn spec_from(m: SpecMsg4Inner) -> SpecMsg4 {
        let (t, (v, tail)) = m;
        SpecMsg4 { t, v, tail }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg4<'a> {
    pub t: AType,
    pub v: Msg4V<'a>,
    pub tail: &'a [u8],
}

impl View for Msg4<'_> {
    type V = SpecMsg4;

    open spec fn view(&self) -> Self::V {
        SpecMsg4 {
            t: self.t@,
            v: self.v@,
            tail: self.tail@,
        }
    }
}
pub type Msg4Inner<'a> = (AType, (Msg4V<'a>, &'a [u8]));

pub type Msg4InnerRef<'a> = (&'a AType, (&'a Msg4V<'a>, &'a &'a [u8]));
impl<'a> From<&'a Msg4<'a>> for Msg4InnerRef<'a> {
    fn ex_from(m: &'a Msg4) -> Msg4InnerRef<'a> {
        (&m.t, (&m.v, &m.tail))
    }
}

impl<'a> From<Msg4Inner<'a>> for Msg4<'a> {
    fn ex_from(m: Msg4Inner) -> Msg4 {
        let (t, (v, tail)) = m;
        Msg4 { t, v, tail }
    }
}

pub struct Msg4Mapper;
impl View for Msg4Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg4Mapper {
    type Src = SpecMsg4Inner;
    type Dst = SpecMsg4;
}
impl SpecIsoProof for Msg4Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg4Mapper {
    type Src = Msg4Inner<'a>;
    type Dst = Msg4<'a>;
    type RefSrc = Msg4InnerRef<'a>;
}

pub struct SpecMsg4Combinator(SpecMsg4CombinatorAlias);

impl SpecCombinator for SpecMsg4Combinator {
    type Type = SpecMsg4;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg4Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg4CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg4CombinatorAlias = Mapped<SpecPair<SpecATypeCombinator, (SpecMsg4VCombinator, bytes::Tail)>, Msg4Mapper>;

pub struct Msg4Combinator(Msg4CombinatorAlias);

impl View for Msg4Combinator {
    type V = SpecMsg4Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg4Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg4Combinator {
    type Type = Msg4<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Msg4CombinatorAlias = Mapped<Pair<ATypeCombinator, (Msg4VCombinator, bytes::Tail), Msg4Cont0>, Msg4Mapper>;


pub closed spec fn spec_msg4() -> SpecMsg4Combinator {
    SpecMsg4Combinator(
    Mapped {
        inner: Pair::spec_new(spec_a_type(), |deps| spec_msg4_cont0(deps)),
        mapper: Msg4Mapper,
    })
}

pub open spec fn spec_msg4_cont0(deps: SpecAType) -> (SpecMsg4VCombinator, bytes::Tail) {
    let t = deps;
    (spec_msg4_v(t), bytes::Tail)
}

impl View for Msg4Cont0 {
    type V = spec_fn(SpecAType) -> (SpecMsg4VCombinator, bytes::Tail);

    open spec fn view(&self) -> Self::V {
        |deps: SpecAType| {
            spec_msg4_cont0(deps)
        }
    }
}

                
pub fn msg4<'a>() -> (o: Msg4Combinator)
    ensures o@ == spec_msg4(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg4Combinator(
    Mapped {
        inner: Pair::new(a_type(), Msg4Cont0),
        mapper: Msg4Mapper,
    });
    assert({
        &&& combinator@ == spec_msg4()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_msg4<'a>(input: &'a [u8]) -> (res: PResult<<Msg4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_msg4().spec_parse(input@) == Some((n as int, v@)),
        spec_msg4().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg4().spec_parse(input@) is None,
        spec_msg4().spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg4<'a>(v: <Msg4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg4().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg4().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg4().spec_serialize(v@))
        },
{
    let combinator = msg4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn msg4_len<'a>(v: <Msg4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (len: usize)
    requires
        spec_msg4().wf(v@),
        spec_msg4().spec_serialize(v@).len() <= usize::MAX,
    ensures
        len == spec_msg4().spec_serialize(v@).len(),
{
    let combinator = msg4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct Msg4Cont0;
type Msg4Cont0Type<'a, 'b> = &'b AType;
type Msg4Cont0SType<'a, 'x> = &'x AType;
type Msg4Cont0Input<'a, 'b, 'x> = POrSType<Msg4Cont0Type<'a, 'b>, Msg4Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg4Cont0Input<'a, 'b, 'x>> for Msg4Cont0 {
    type Output = (Msg4VCombinator, bytes::Tail);

    open spec fn requires(&self, deps: Msg4Cont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Msg4Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_msg4_cont0(deps@)
    }

    fn apply(&self, deps: Msg4Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let t = *deps;
                (msg4_v(t), bytes::Tail)
            }
            POrSType::S(deps) => {
                let t = deps;
                let t = *t;
                (msg4_v(t), bytes::Tail)
            }
        }
    }
}
                

}
