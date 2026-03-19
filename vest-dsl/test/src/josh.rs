
#![allow(warnings)]
#![allow(unused)]
use vstd::prelude::*;
use vest_lib::regular::modifier::*;
use vest_lib::regular::bytes;
use vest_lib::regular::variant::*;
use vest_lib::regular::sequence::*;
use vest_lib::regular::repetition::*;
use vest_lib::regular::disjoint::DisjointFrom;
use vest_lib::regular::tag::*;
use vest_lib::regular::uints::*;
use vest_lib::utils::*;
use vest_lib::properties::*;
use vest_lib::bitcoin::varint::{BtcVarint, VarInt};
use vest_lib::regular::leb128::*;

macro_rules! impl_wrapper_combinator {
    ($combinator:ty, $combinator_alias:ty) => {
        ::vstd::prelude::verus! {
            impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for $combinator {
                type Type = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
                type SType = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
                fn length(&self, v: Self::SType) -> usize
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
                open spec fn ex_requires(&self) -> bool
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
pub mod TstTag {
    use super::*;
    pub spec const SPEC_C0: u8 = 0;
    pub spec const SPEC_C1: u8 = 1;
    pub spec const SPEC_C2: u8 = 2;
    pub spec const SPEC_C3: u8 = 3;
    pub spec const SPEC_C4: u8 = 4;
    pub spec const SPEC_C5: u8 = 5;
    pub spec const SPEC_C6: u8 = 6;
    pub spec const SPEC_C7: u8 = 7;
    pub spec const SPEC_C8: u8 = 8;
    pub spec const SPEC_C9: u8 = 9;
    pub spec const SPEC_C10: u8 = 10;
    pub spec const SPEC_C11: u8 = 11;
    pub spec const SPEC_C12: u8 = 12;
    pub spec const SPEC_C13: u8 = 13;
    pub spec const SPEC_C14: u8 = 14;
    pub spec const SPEC_C15: u8 = 15;
    pub spec const SPEC_C16: u8 = 16;
    pub spec const SPEC_C17: u8 = 17;
    pub spec const SPEC_C18: u8 = 18;
    pub spec const SPEC_C19: u8 = 19;
    pub spec const SPEC_C20: u8 = 20;
    pub spec const SPEC_C21: u8 = 21;
    pub spec const SPEC_C22: u8 = 22;
    pub spec const SPEC_C23: u8 = 23;
    pub spec const SPEC_C24: u8 = 24;
    pub spec const SPEC_C25: u8 = 25;
    pub spec const SPEC_C26: u8 = 26;
    pub spec const SPEC_C27: u8 = 27;
    pub spec const SPEC_C28: u8 = 28;
    pub spec const SPEC_C29: u8 = 29;
    pub spec const SPEC_C30: u8 = 30;
    pub exec const C0: u8 ensures C0 == SPEC_C0 { 0 }
    pub exec const C1: u8 ensures C1 == SPEC_C1 { 1 }
    pub exec const C2: u8 ensures C2 == SPEC_C2 { 2 }
    pub exec const C3: u8 ensures C3 == SPEC_C3 { 3 }
    pub exec const C4: u8 ensures C4 == SPEC_C4 { 4 }
    pub exec const C5: u8 ensures C5 == SPEC_C5 { 5 }
    pub exec const C6: u8 ensures C6 == SPEC_C6 { 6 }
    pub exec const C7: u8 ensures C7 == SPEC_C7 { 7 }
    pub exec const C8: u8 ensures C8 == SPEC_C8 { 8 }
    pub exec const C9: u8 ensures C9 == SPEC_C9 { 9 }
    pub exec const C10: u8 ensures C10 == SPEC_C10 { 10 }
    pub exec const C11: u8 ensures C11 == SPEC_C11 { 11 }
    pub exec const C12: u8 ensures C12 == SPEC_C12 { 12 }
    pub exec const C13: u8 ensures C13 == SPEC_C13 { 13 }
    pub exec const C14: u8 ensures C14 == SPEC_C14 { 14 }
    pub exec const C15: u8 ensures C15 == SPEC_C15 { 15 }
    pub exec const C16: u8 ensures C16 == SPEC_C16 { 16 }
    pub exec const C17: u8 ensures C17 == SPEC_C17 { 17 }
    pub exec const C18: u8 ensures C18 == SPEC_C18 { 18 }
    pub exec const C19: u8 ensures C19 == SPEC_C19 { 19 }
    pub exec const C20: u8 ensures C20 == SPEC_C20 { 20 }
    pub exec const C21: u8 ensures C21 == SPEC_C21 { 21 }
    pub exec const C22: u8 ensures C22 == SPEC_C22 { 22 }
    pub exec const C23: u8 ensures C23 == SPEC_C23 { 23 }
    pub exec const C24: u8 ensures C24 == SPEC_C24 { 24 }
    pub exec const C25: u8 ensures C25 == SPEC_C25 { 25 }
    pub exec const C26: u8 ensures C26 == SPEC_C26 { 26 }
    pub exec const C27: u8 ensures C27 == SPEC_C27 { 27 }
    pub exec const C28: u8 ensures C28 == SPEC_C28 { 28 }
    pub exec const C29: u8 ensures C29 == SPEC_C29 { 29 }
    pub exec const C30: u8 ensures C30 == SPEC_C30 { 30 }
}


pub struct SpecTstTagCombinator(pub SpecTstTagCombinatorAlias);

impl SpecCombinator for SpecTstTagCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTstTagCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTstTagCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTstTagCombinatorAlias = U8;

pub struct TstTagCombinator(pub TstTagCombinatorAlias);

impl View for TstTagCombinator {
    type V = SpecTstTagCombinator;
    open spec fn view(&self) -> Self::V { SpecTstTagCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TstTagCombinator {
    type Type = u8;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type TstTagCombinatorAlias = U8;


pub open spec fn spec_tst_tag() -> SpecTstTagCombinator {
    SpecTstTagCombinator(U8)
}

                
pub fn tst_tag<'a>() -> (o: TstTagCombinator)
    ensures o@ == spec_tst_tag(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TstTagCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_tst_tag()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_tst_tag<'a>(input: &'a [u8]) -> (res: PResult<<TstTagCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_tst_tag().spec_parse(input@) == Some((n as int, v@)),
        spec_tst_tag().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_tst_tag().spec_parse(input@) is None,
        spec_tst_tag().spec_parse(input@) is None ==> res is Err,
{
    let combinator = tst_tag();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_tst_tag<'a>(v: <TstTagCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_tst_tag().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_tst_tag().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_tst_tag().spec_serialize(v@))
        },
{
    let combinator = tst_tag();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn tst_tag_len<'a>(v: <TstTagCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_tst_tag().wf(v@),
        spec_tst_tag().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_tst_tag().spec_serialize(v@).len(),
{
    let combinator = tst_tag();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecMydata {
    pub foo: Seq<u8>,
    pub bar: Seq<u8>,
}

pub type SpecMydataInner = (Seq<u8>, Seq<u8>);


impl SpecFrom<SpecMydata> for SpecMydataInner {
    open spec fn spec_from(m: SpecMydata) -> SpecMydataInner {
        (m.foo, m.bar)
    }
}

impl SpecFrom<SpecMydataInner> for SpecMydata {
    open spec fn spec_from(m: SpecMydataInner) -> SpecMydata {
        let (foo, bar) = m;
        SpecMydata { foo, bar }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Mydata<'a> {
    pub foo: &'a [u8],
    pub bar: &'a [u8],
}

impl View for Mydata<'_> {
    type V = SpecMydata;

    open spec fn view(&self) -> Self::V {
        SpecMydata {
            foo: self.foo@,
            bar: self.bar@,
        }
    }
}
pub type MydataInner<'a> = (&'a [u8], &'a [u8]);

pub type MydataInnerRef<'a> = (&'a &'a [u8], &'a &'a [u8]);
impl<'a> From<&'a Mydata<'a>> for MydataInnerRef<'a> {
    fn ex_from(m: &'a Mydata) -> MydataInnerRef<'a> {
        (&m.foo, &m.bar)
    }
}

impl<'a> From<MydataInner<'a>> for Mydata<'a> {
    fn ex_from(m: MydataInner) -> Mydata {
        let (foo, bar) = m;
        Mydata { foo, bar }
    }
}

pub struct MydataMapper;
impl View for MydataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MydataMapper {
    type Src = SpecMydataInner;
    type Dst = SpecMydata;
}
impl SpecIsoProof for MydataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MydataMapper {
    type Src = MydataInner<'a>;
    type Dst = Mydata<'a>;
    type RefSrc = MydataInnerRef<'a>;
}
type SpecMydataCombinatorAlias1 = (bytes::Fixed<2>, bytes::Fixed<2>);
pub struct SpecMydataCombinator(pub SpecMydataCombinatorAlias);

impl SpecCombinator for SpecMydataCombinator {
    type Type = SpecMydata;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMydataCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMydataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMydataCombinatorAlias = Mapped<SpecMydataCombinatorAlias1, MydataMapper>;
type MydataCombinatorAlias1 = (bytes::Fixed<2>, bytes::Fixed<2>);
pub struct MydataCombinator1(pub MydataCombinatorAlias1);
impl View for MydataCombinator1 {
    type V = SpecMydataCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MydataCombinator1, MydataCombinatorAlias1);

pub struct MydataCombinator(pub MydataCombinatorAlias);

impl View for MydataCombinator {
    type V = SpecMydataCombinator;
    open spec fn view(&self) -> Self::V { SpecMydataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MydataCombinator {
    type Type = Mydata<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type MydataCombinatorAlias = Mapped<MydataCombinator1, MydataMapper>;


pub open spec fn spec_mydata() -> SpecMydataCombinator {
    SpecMydataCombinator(
    Mapped {
        inner: (bytes::Fixed::<2>, bytes::Fixed::<2>),
        mapper: MydataMapper,
    })
}

                
pub fn mydata<'a>() -> (o: MydataCombinator)
    ensures o@ == spec_mydata(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MydataCombinator(
    Mapped {
        inner: MydataCombinator1((bytes::Fixed::<2>, bytes::Fixed::<2>)),
        mapper: MydataMapper,
    });
    // assert({
    //     &&& combinator@ == spec_mydata()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_mydata<'a>(input: &'a [u8]) -> (res: PResult<<MydataCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_mydata().spec_parse(input@) == Some((n as int, v@)),
        spec_mydata().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mydata().spec_parse(input@) is None,
        spec_mydata().spec_parse(input@) is None ==> res is Err,
{
    let combinator = mydata();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mydata<'a>(v: <MydataCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mydata().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mydata().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mydata().spec_serialize(v@))
        },
{
    let combinator = mydata();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn mydata_len<'a>(v: <MydataCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_mydata().wf(v@),
        spec_mydata().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_mydata().spec_serialize(v@).len(),
{
    let combinator = mydata();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecTstAnonMydata {
    C0(SpecMydata),
    C1(SpecMydata),
    C2(SpecMydata),
    C3(SpecMydata),
    C4(SpecMydata),
    C5(SpecMydata),
    C6(SpecMydata),
    C7(SpecMydata),
    C8(SpecMydata),
    C9(SpecMydata),
    C10(SpecMydata),
    C11(SpecMydata),
    C12(SpecMydata),
    C13(SpecMydata),
    C14(SpecMydata),
    C15(SpecMydata),
    C16(SpecMydata),
    C17(SpecMydata),
    C18(SpecMydata),
    C19(SpecMydata),
    C20(SpecMydata),
    C21(SpecMydata),
    C22(SpecMydata),
    C23(SpecMydata),
    C24(SpecMydata),
    C25(SpecMydata),
    C26(SpecMydata),
    C27(SpecMydata),
    C28(SpecMydata),
    C29(SpecMydata),
    C30(SpecMydata),
}

pub type SpecTstAnonMydataInner = Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, SpecMydata>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;

impl SpecFrom<SpecTstAnonMydata> for SpecTstAnonMydataInner {
    open spec fn spec_from(m: SpecTstAnonMydata) -> SpecTstAnonMydataInner {
        match m {
            SpecTstAnonMydata::C0(m) => Either::Left(m),
            SpecTstAnonMydata::C1(m) => Either::Right(Either::Left(m)),
            SpecTstAnonMydata::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecTstAnonMydata::C3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecTstAnonMydata::C4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecTstAnonMydata::C5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecTstAnonMydata::C6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecTstAnonMydata::C7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecTstAnonMydata::C8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecTstAnonMydata::C9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecTstAnonMydata::C10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecTstAnonMydata::C11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecTstAnonMydata::C12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecTstAnonMydata::C13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecTstAnonMydata::C14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecTstAnonMydata::C15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecTstAnonMydata::C16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SpecTstAnonMydata::C17(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SpecTstAnonMydata::C18(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SpecTstAnonMydata::C19(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SpecTstAnonMydata::C20(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SpecTstAnonMydata::C21(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SpecTstAnonMydata::C22(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SpecTstAnonMydata::C23(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SpecTstAnonMydata::C24(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SpecTstAnonMydata::C25(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SpecTstAnonMydata::C26(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            SpecTstAnonMydata::C27(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            SpecTstAnonMydata::C28(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            SpecTstAnonMydata::C29(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            SpecTstAnonMydata::C30(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))))))),
        }
    }

}

                
impl SpecFrom<SpecTstAnonMydataInner> for SpecTstAnonMydata {
    open spec fn spec_from(m: SpecTstAnonMydataInner) -> SpecTstAnonMydata {
        match m {
            Either::Left(m) => SpecTstAnonMydata::C0(m),
            Either::Right(Either::Left(m)) => SpecTstAnonMydata::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecTstAnonMydata::C2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecTstAnonMydata::C3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecTstAnonMydata::C4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecTstAnonMydata::C5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecTstAnonMydata::C6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecTstAnonMydata::C7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecTstAnonMydata::C8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecTstAnonMydata::C9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecTstAnonMydata::C10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecTstAnonMydata::C11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecTstAnonMydata::C12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecTstAnonMydata::C13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecTstAnonMydata::C14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecTstAnonMydata::C15(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SpecTstAnonMydata::C16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SpecTstAnonMydata::C17(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SpecTstAnonMydata::C18(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SpecTstAnonMydata::C19(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SpecTstAnonMydata::C20(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SpecTstAnonMydata::C21(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SpecTstAnonMydata::C22(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SpecTstAnonMydata::C23(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SpecTstAnonMydata::C24(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SpecTstAnonMydata::C25(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => SpecTstAnonMydata::C26(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => SpecTstAnonMydata::C27(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => SpecTstAnonMydata::C28(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => SpecTstAnonMydata::C29(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))))))) => SpecTstAnonMydata::C30(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TstAnonMydata<'a> {
    C0(Mydata<'a>),
    C1(Mydata<'a>),
    C2(Mydata<'a>),
    C3(Mydata<'a>),
    C4(Mydata<'a>),
    C5(Mydata<'a>),
    C6(Mydata<'a>),
    C7(Mydata<'a>),
    C8(Mydata<'a>),
    C9(Mydata<'a>),
    C10(Mydata<'a>),
    C11(Mydata<'a>),
    C12(Mydata<'a>),
    C13(Mydata<'a>),
    C14(Mydata<'a>),
    C15(Mydata<'a>),
    C16(Mydata<'a>),
    C17(Mydata<'a>),
    C18(Mydata<'a>),
    C19(Mydata<'a>),
    C20(Mydata<'a>),
    C21(Mydata<'a>),
    C22(Mydata<'a>),
    C23(Mydata<'a>),
    C24(Mydata<'a>),
    C25(Mydata<'a>),
    C26(Mydata<'a>),
    C27(Mydata<'a>),
    C28(Mydata<'a>),
    C29(Mydata<'a>),
    C30(Mydata<'a>),
}

pub type TstAnonMydataInner<'a> = Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Mydata<'a>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;

pub type TstAnonMydataInnerRef<'a> = Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, &'a Mydata<'a>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;


impl<'a> View for TstAnonMydata<'a> {
    type V = SpecTstAnonMydata;
    open spec fn view(&self) -> Self::V {
        match self {
            TstAnonMydata::C0(m) => SpecTstAnonMydata::C0(m@),
            TstAnonMydata::C1(m) => SpecTstAnonMydata::C1(m@),
            TstAnonMydata::C2(m) => SpecTstAnonMydata::C2(m@),
            TstAnonMydata::C3(m) => SpecTstAnonMydata::C3(m@),
            TstAnonMydata::C4(m) => SpecTstAnonMydata::C4(m@),
            TstAnonMydata::C5(m) => SpecTstAnonMydata::C5(m@),
            TstAnonMydata::C6(m) => SpecTstAnonMydata::C6(m@),
            TstAnonMydata::C7(m) => SpecTstAnonMydata::C7(m@),
            TstAnonMydata::C8(m) => SpecTstAnonMydata::C8(m@),
            TstAnonMydata::C9(m) => SpecTstAnonMydata::C9(m@),
            TstAnonMydata::C10(m) => SpecTstAnonMydata::C10(m@),
            TstAnonMydata::C11(m) => SpecTstAnonMydata::C11(m@),
            TstAnonMydata::C12(m) => SpecTstAnonMydata::C12(m@),
            TstAnonMydata::C13(m) => SpecTstAnonMydata::C13(m@),
            TstAnonMydata::C14(m) => SpecTstAnonMydata::C14(m@),
            TstAnonMydata::C15(m) => SpecTstAnonMydata::C15(m@),
            TstAnonMydata::C16(m) => SpecTstAnonMydata::C16(m@),
            TstAnonMydata::C17(m) => SpecTstAnonMydata::C17(m@),
            TstAnonMydata::C18(m) => SpecTstAnonMydata::C18(m@),
            TstAnonMydata::C19(m) => SpecTstAnonMydata::C19(m@),
            TstAnonMydata::C20(m) => SpecTstAnonMydata::C20(m@),
            TstAnonMydata::C21(m) => SpecTstAnonMydata::C21(m@),
            TstAnonMydata::C22(m) => SpecTstAnonMydata::C22(m@),
            TstAnonMydata::C23(m) => SpecTstAnonMydata::C23(m@),
            TstAnonMydata::C24(m) => SpecTstAnonMydata::C24(m@),
            TstAnonMydata::C25(m) => SpecTstAnonMydata::C25(m@),
            TstAnonMydata::C26(m) => SpecTstAnonMydata::C26(m@),
            TstAnonMydata::C27(m) => SpecTstAnonMydata::C27(m@),
            TstAnonMydata::C28(m) => SpecTstAnonMydata::C28(m@),
            TstAnonMydata::C29(m) => SpecTstAnonMydata::C29(m@),
            TstAnonMydata::C30(m) => SpecTstAnonMydata::C30(m@),
        }
    }
}


impl<'a> From<&'a TstAnonMydata<'a>> for TstAnonMydataInnerRef<'a> {
    fn ex_from(m: &'a TstAnonMydata<'a>) -> TstAnonMydataInnerRef<'a> {
        match m {
            TstAnonMydata::C0(m) => Either::Left(m),
            TstAnonMydata::C1(m) => Either::Right(Either::Left(m)),
            TstAnonMydata::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            TstAnonMydata::C3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            TstAnonMydata::C4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            TstAnonMydata::C5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            TstAnonMydata::C6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            TstAnonMydata::C7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            TstAnonMydata::C8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            TstAnonMydata::C9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            TstAnonMydata::C10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            TstAnonMydata::C11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            TstAnonMydata::C12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            TstAnonMydata::C13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            TstAnonMydata::C14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            TstAnonMydata::C15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            TstAnonMydata::C16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            TstAnonMydata::C17(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            TstAnonMydata::C18(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            TstAnonMydata::C19(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            TstAnonMydata::C20(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            TstAnonMydata::C21(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            TstAnonMydata::C22(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            TstAnonMydata::C23(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            TstAnonMydata::C24(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            TstAnonMydata::C25(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            TstAnonMydata::C26(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            TstAnonMydata::C27(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            TstAnonMydata::C28(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            TstAnonMydata::C29(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            TstAnonMydata::C30(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))))))),
        }
    }

}

impl<'a> From<TstAnonMydataInner<'a>> for TstAnonMydata<'a> {
    fn ex_from(m: TstAnonMydataInner<'a>) -> TstAnonMydata<'a> {
        match m {
            Either::Left(m) => TstAnonMydata::C0(m),
            Either::Right(Either::Left(m)) => TstAnonMydata::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => TstAnonMydata::C2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => TstAnonMydata::C3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => TstAnonMydata::C4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => TstAnonMydata::C5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => TstAnonMydata::C6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => TstAnonMydata::C7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => TstAnonMydata::C8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => TstAnonMydata::C9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => TstAnonMydata::C10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => TstAnonMydata::C11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => TstAnonMydata::C12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => TstAnonMydata::C13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => TstAnonMydata::C14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => TstAnonMydata::C15(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => TstAnonMydata::C16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => TstAnonMydata::C17(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => TstAnonMydata::C18(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => TstAnonMydata::C19(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => TstAnonMydata::C20(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => TstAnonMydata::C21(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => TstAnonMydata::C22(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => TstAnonMydata::C23(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => TstAnonMydata::C24(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => TstAnonMydata::C25(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => TstAnonMydata::C26(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => TstAnonMydata::C27(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => TstAnonMydata::C28(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => TstAnonMydata::C29(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))))))) => TstAnonMydata::C30(m),
        }
    }
    
}


pub struct TstAnonMydataMapper;
impl View for TstAnonMydataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TstAnonMydataMapper {
    type Src = SpecTstAnonMydataInner;
    type Dst = SpecTstAnonMydata;
}
impl SpecIsoProof for TstAnonMydataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TstAnonMydataMapper {
    type Src = TstAnonMydataInner<'a>;
    type Dst = TstAnonMydata<'a>;
    type RefSrc = TstAnonMydataInnerRef<'a>;
}

type SpecTstAnonMydataCombinatorAlias1 = Choice<Cond<SpecMydataCombinator>, Cond<SpecMydataCombinator>>;
type SpecTstAnonMydataCombinatorAlias2 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias1>;
type SpecTstAnonMydataCombinatorAlias3 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias2>;
type SpecTstAnonMydataCombinatorAlias4 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias3>;
type SpecTstAnonMydataCombinatorAlias5 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias4>;
type SpecTstAnonMydataCombinatorAlias6 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias5>;
type SpecTstAnonMydataCombinatorAlias7 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias6>;
type SpecTstAnonMydataCombinatorAlias8 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias7>;
type SpecTstAnonMydataCombinatorAlias9 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias8>;
type SpecTstAnonMydataCombinatorAlias10 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias9>;
type SpecTstAnonMydataCombinatorAlias11 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias10>;
type SpecTstAnonMydataCombinatorAlias12 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias11>;
type SpecTstAnonMydataCombinatorAlias13 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias12>;
type SpecTstAnonMydataCombinatorAlias14 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias13>;
type SpecTstAnonMydataCombinatorAlias15 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias14>;
type SpecTstAnonMydataCombinatorAlias16 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias15>;
type SpecTstAnonMydataCombinatorAlias17 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias16>;
type SpecTstAnonMydataCombinatorAlias18 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias17>;
type SpecTstAnonMydataCombinatorAlias19 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias18>;
type SpecTstAnonMydataCombinatorAlias20 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias19>;
type SpecTstAnonMydataCombinatorAlias21 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias20>;
type SpecTstAnonMydataCombinatorAlias22 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias21>;
type SpecTstAnonMydataCombinatorAlias23 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias22>;
type SpecTstAnonMydataCombinatorAlias24 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias23>;
type SpecTstAnonMydataCombinatorAlias25 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias24>;
type SpecTstAnonMydataCombinatorAlias26 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias25>;
type SpecTstAnonMydataCombinatorAlias27 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias26>;
type SpecTstAnonMydataCombinatorAlias28 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias27>;
type SpecTstAnonMydataCombinatorAlias29 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias28>;
type SpecTstAnonMydataCombinatorAlias30 = Choice<Cond<SpecMydataCombinator>, SpecTstAnonMydataCombinatorAlias29>;
pub struct SpecTstAnonMydataCombinator(pub SpecTstAnonMydataCombinatorAlias);

impl SpecCombinator for SpecTstAnonMydataCombinator {
    type Type = SpecTstAnonMydata;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTstAnonMydataCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTstAnonMydataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTstAnonMydataCombinatorAlias = Mapped<SpecTstAnonMydataCombinatorAlias30, TstAnonMydataMapper>;
type TstAnonMydataCombinatorAlias1 = Choice<Cond<MydataCombinator>, Cond<MydataCombinator>>;
type TstAnonMydataCombinatorAlias2 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator1>;
type TstAnonMydataCombinatorAlias3 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator2>;
type TstAnonMydataCombinatorAlias4 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator3>;
type TstAnonMydataCombinatorAlias5 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator4>;
type TstAnonMydataCombinatorAlias6 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator5>;
type TstAnonMydataCombinatorAlias7 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator6>;
type TstAnonMydataCombinatorAlias8 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator7>;
type TstAnonMydataCombinatorAlias9 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator8>;
type TstAnonMydataCombinatorAlias10 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator9>;
type TstAnonMydataCombinatorAlias11 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator10>;
type TstAnonMydataCombinatorAlias12 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator11>;
type TstAnonMydataCombinatorAlias13 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator12>;
type TstAnonMydataCombinatorAlias14 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator13>;
type TstAnonMydataCombinatorAlias15 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator14>;
type TstAnonMydataCombinatorAlias16 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator15>;
type TstAnonMydataCombinatorAlias17 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator16>;
type TstAnonMydataCombinatorAlias18 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator17>;
type TstAnonMydataCombinatorAlias19 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator18>;
type TstAnonMydataCombinatorAlias20 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator19>;
type TstAnonMydataCombinatorAlias21 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator20>;
type TstAnonMydataCombinatorAlias22 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator21>;
type TstAnonMydataCombinatorAlias23 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator22>;
type TstAnonMydataCombinatorAlias24 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator23>;
type TstAnonMydataCombinatorAlias25 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator24>;
type TstAnonMydataCombinatorAlias26 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator25>;
type TstAnonMydataCombinatorAlias27 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator26>;
type TstAnonMydataCombinatorAlias28 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator27>;
type TstAnonMydataCombinatorAlias29 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator28>;
type TstAnonMydataCombinatorAlias30 = Choice<Cond<MydataCombinator>, TstAnonMydataCombinator29>;
pub struct TstAnonMydataCombinator1(pub TstAnonMydataCombinatorAlias1);
impl View for TstAnonMydataCombinator1 {
    type V = SpecTstAnonMydataCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator1, TstAnonMydataCombinatorAlias1);

pub struct TstAnonMydataCombinator2(pub TstAnonMydataCombinatorAlias2);
impl View for TstAnonMydataCombinator2 {
    type V = SpecTstAnonMydataCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator2, TstAnonMydataCombinatorAlias2);

pub struct TstAnonMydataCombinator3(pub TstAnonMydataCombinatorAlias3);
impl View for TstAnonMydataCombinator3 {
    type V = SpecTstAnonMydataCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator3, TstAnonMydataCombinatorAlias3);

pub struct TstAnonMydataCombinator4(pub TstAnonMydataCombinatorAlias4);
impl View for TstAnonMydataCombinator4 {
    type V = SpecTstAnonMydataCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator4, TstAnonMydataCombinatorAlias4);

pub struct TstAnonMydataCombinator5(pub TstAnonMydataCombinatorAlias5);
impl View for TstAnonMydataCombinator5 {
    type V = SpecTstAnonMydataCombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator5, TstAnonMydataCombinatorAlias5);

pub struct TstAnonMydataCombinator6(pub TstAnonMydataCombinatorAlias6);
impl View for TstAnonMydataCombinator6 {
    type V = SpecTstAnonMydataCombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator6, TstAnonMydataCombinatorAlias6);

pub struct TstAnonMydataCombinator7(pub TstAnonMydataCombinatorAlias7);
impl View for TstAnonMydataCombinator7 {
    type V = SpecTstAnonMydataCombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator7, TstAnonMydataCombinatorAlias7);

pub struct TstAnonMydataCombinator8(pub TstAnonMydataCombinatorAlias8);
impl View for TstAnonMydataCombinator8 {
    type V = SpecTstAnonMydataCombinatorAlias8;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator8, TstAnonMydataCombinatorAlias8);

pub struct TstAnonMydataCombinator9(pub TstAnonMydataCombinatorAlias9);
impl View for TstAnonMydataCombinator9 {
    type V = SpecTstAnonMydataCombinatorAlias9;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator9, TstAnonMydataCombinatorAlias9);

pub struct TstAnonMydataCombinator10(pub TstAnonMydataCombinatorAlias10);
impl View for TstAnonMydataCombinator10 {
    type V = SpecTstAnonMydataCombinatorAlias10;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator10, TstAnonMydataCombinatorAlias10);

pub struct TstAnonMydataCombinator11(pub TstAnonMydataCombinatorAlias11);
impl View for TstAnonMydataCombinator11 {
    type V = SpecTstAnonMydataCombinatorAlias11;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator11, TstAnonMydataCombinatorAlias11);

pub struct TstAnonMydataCombinator12(pub TstAnonMydataCombinatorAlias12);
impl View for TstAnonMydataCombinator12 {
    type V = SpecTstAnonMydataCombinatorAlias12;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator12, TstAnonMydataCombinatorAlias12);

pub struct TstAnonMydataCombinator13(pub TstAnonMydataCombinatorAlias13);
impl View for TstAnonMydataCombinator13 {
    type V = SpecTstAnonMydataCombinatorAlias13;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator13, TstAnonMydataCombinatorAlias13);

pub struct TstAnonMydataCombinator14(pub TstAnonMydataCombinatorAlias14);
impl View for TstAnonMydataCombinator14 {
    type V = SpecTstAnonMydataCombinatorAlias14;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator14, TstAnonMydataCombinatorAlias14);

pub struct TstAnonMydataCombinator15(pub TstAnonMydataCombinatorAlias15);
impl View for TstAnonMydataCombinator15 {
    type V = SpecTstAnonMydataCombinatorAlias15;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator15, TstAnonMydataCombinatorAlias15);

pub struct TstAnonMydataCombinator16(pub TstAnonMydataCombinatorAlias16);
impl View for TstAnonMydataCombinator16 {
    type V = SpecTstAnonMydataCombinatorAlias16;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator16, TstAnonMydataCombinatorAlias16);

pub struct TstAnonMydataCombinator17(pub TstAnonMydataCombinatorAlias17);
impl View for TstAnonMydataCombinator17 {
    type V = SpecTstAnonMydataCombinatorAlias17;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator17, TstAnonMydataCombinatorAlias17);

pub struct TstAnonMydataCombinator18(pub TstAnonMydataCombinatorAlias18);
impl View for TstAnonMydataCombinator18 {
    type V = SpecTstAnonMydataCombinatorAlias18;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator18, TstAnonMydataCombinatorAlias18);

pub struct TstAnonMydataCombinator19(pub TstAnonMydataCombinatorAlias19);
impl View for TstAnonMydataCombinator19 {
    type V = SpecTstAnonMydataCombinatorAlias19;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator19, TstAnonMydataCombinatorAlias19);

pub struct TstAnonMydataCombinator20(pub TstAnonMydataCombinatorAlias20);
impl View for TstAnonMydataCombinator20 {
    type V = SpecTstAnonMydataCombinatorAlias20;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator20, TstAnonMydataCombinatorAlias20);

pub struct TstAnonMydataCombinator21(pub TstAnonMydataCombinatorAlias21);
impl View for TstAnonMydataCombinator21 {
    type V = SpecTstAnonMydataCombinatorAlias21;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator21, TstAnonMydataCombinatorAlias21);

pub struct TstAnonMydataCombinator22(pub TstAnonMydataCombinatorAlias22);
impl View for TstAnonMydataCombinator22 {
    type V = SpecTstAnonMydataCombinatorAlias22;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator22, TstAnonMydataCombinatorAlias22);

pub struct TstAnonMydataCombinator23(pub TstAnonMydataCombinatorAlias23);
impl View for TstAnonMydataCombinator23 {
    type V = SpecTstAnonMydataCombinatorAlias23;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator23, TstAnonMydataCombinatorAlias23);

pub struct TstAnonMydataCombinator24(pub TstAnonMydataCombinatorAlias24);
impl View for TstAnonMydataCombinator24 {
    type V = SpecTstAnonMydataCombinatorAlias24;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator24, TstAnonMydataCombinatorAlias24);

pub struct TstAnonMydataCombinator25(pub TstAnonMydataCombinatorAlias25);
impl View for TstAnonMydataCombinator25 {
    type V = SpecTstAnonMydataCombinatorAlias25;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator25, TstAnonMydataCombinatorAlias25);

pub struct TstAnonMydataCombinator26(pub TstAnonMydataCombinatorAlias26);
impl View for TstAnonMydataCombinator26 {
    type V = SpecTstAnonMydataCombinatorAlias26;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator26, TstAnonMydataCombinatorAlias26);

pub struct TstAnonMydataCombinator27(pub TstAnonMydataCombinatorAlias27);
impl View for TstAnonMydataCombinator27 {
    type V = SpecTstAnonMydataCombinatorAlias27;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator27, TstAnonMydataCombinatorAlias27);

pub struct TstAnonMydataCombinator28(pub TstAnonMydataCombinatorAlias28);
impl View for TstAnonMydataCombinator28 {
    type V = SpecTstAnonMydataCombinatorAlias28;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator28, TstAnonMydataCombinatorAlias28);

pub struct TstAnonMydataCombinator29(pub TstAnonMydataCombinatorAlias29);
impl View for TstAnonMydataCombinator29 {
    type V = SpecTstAnonMydataCombinatorAlias29;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator29, TstAnonMydataCombinatorAlias29);

pub struct TstAnonMydataCombinator30(pub TstAnonMydataCombinatorAlias30);
impl View for TstAnonMydataCombinator30 {
    type V = SpecTstAnonMydataCombinatorAlias30;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstAnonMydataCombinator30, TstAnonMydataCombinatorAlias30);

pub struct TstAnonMydataCombinator(pub TstAnonMydataCombinatorAlias);

impl View for TstAnonMydataCombinator {
    type V = SpecTstAnonMydataCombinator;
    open spec fn view(&self) -> Self::V { SpecTstAnonMydataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TstAnonMydataCombinator {
    type Type = TstAnonMydata<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type TstAnonMydataCombinatorAlias = Mapped<TstAnonMydataCombinator30, TstAnonMydataMapper>;


pub open spec fn spec_tst_anon_mydata(tag: u8) -> SpecTstAnonMydataCombinator {
    SpecTstAnonMydataCombinator(Mapped { inner: Choice(Cond { cond: tag == TstTag::SPEC_C0, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C1, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C2, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C3, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C4, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C5, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C6, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C7, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C8, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C9, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C10, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C11, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C12, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C13, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C14, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C15, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C16, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C17, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C18, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C19, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C20, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C21, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C22, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C23, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C24, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C25, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C26, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C27, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C28, inner: spec_mydata() }, Choice(Cond { cond: tag == TstTag::SPEC_C29, inner: spec_mydata() }, Cond { cond: tag == TstTag::SPEC_C30, inner: spec_mydata() })))))))))))))))))))))))))))))), mapper: TstAnonMydataMapper })
}

pub fn tst_anon_mydata<'a>(tag: u8) -> (o: TstAnonMydataCombinator)
    requires
        spec_tst_tag().wf(tag@),

    ensures o@ == spec_tst_anon_mydata(tag@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TstAnonMydataCombinator(Mapped { inner: TstAnonMydataCombinator30(Choice::new(Cond { cond: tag == TstTag::C0, inner: mydata() }, TstAnonMydataCombinator29(Choice::new(Cond { cond: tag == TstTag::C1, inner: mydata() }, TstAnonMydataCombinator28(Choice::new(Cond { cond: tag == TstTag::C2, inner: mydata() }, TstAnonMydataCombinator27(Choice::new(Cond { cond: tag == TstTag::C3, inner: mydata() }, TstAnonMydataCombinator26(Choice::new(Cond { cond: tag == TstTag::C4, inner: mydata() }, TstAnonMydataCombinator25(Choice::new(Cond { cond: tag == TstTag::C5, inner: mydata() }, TstAnonMydataCombinator24(Choice::new(Cond { cond: tag == TstTag::C6, inner: mydata() }, TstAnonMydataCombinator23(Choice::new(Cond { cond: tag == TstTag::C7, inner: mydata() }, TstAnonMydataCombinator22(Choice::new(Cond { cond: tag == TstTag::C8, inner: mydata() }, TstAnonMydataCombinator21(Choice::new(Cond { cond: tag == TstTag::C9, inner: mydata() }, TstAnonMydataCombinator20(Choice::new(Cond { cond: tag == TstTag::C10, inner: mydata() }, TstAnonMydataCombinator19(Choice::new(Cond { cond: tag == TstTag::C11, inner: mydata() }, TstAnonMydataCombinator18(Choice::new(Cond { cond: tag == TstTag::C12, inner: mydata() }, TstAnonMydataCombinator17(Choice::new(Cond { cond: tag == TstTag::C13, inner: mydata() }, TstAnonMydataCombinator16(Choice::new(Cond { cond: tag == TstTag::C14, inner: mydata() }, TstAnonMydataCombinator15(Choice::new(Cond { cond: tag == TstTag::C15, inner: mydata() }, TstAnonMydataCombinator14(Choice::new(Cond { cond: tag == TstTag::C16, inner: mydata() }, TstAnonMydataCombinator13(Choice::new(Cond { cond: tag == TstTag::C17, inner: mydata() }, TstAnonMydataCombinator12(Choice::new(Cond { cond: tag == TstTag::C18, inner: mydata() }, TstAnonMydataCombinator11(Choice::new(Cond { cond: tag == TstTag::C19, inner: mydata() }, TstAnonMydataCombinator10(Choice::new(Cond { cond: tag == TstTag::C20, inner: mydata() }, TstAnonMydataCombinator9(Choice::new(Cond { cond: tag == TstTag::C21, inner: mydata() }, TstAnonMydataCombinator8(Choice::new(Cond { cond: tag == TstTag::C22, inner: mydata() }, TstAnonMydataCombinator7(Choice::new(Cond { cond: tag == TstTag::C23, inner: mydata() }, TstAnonMydataCombinator6(Choice::new(Cond { cond: tag == TstTag::C24, inner: mydata() }, TstAnonMydataCombinator5(Choice::new(Cond { cond: tag == TstTag::C25, inner: mydata() }, TstAnonMydataCombinator4(Choice::new(Cond { cond: tag == TstTag::C26, inner: mydata() }, TstAnonMydataCombinator3(Choice::new(Cond { cond: tag == TstTag::C27, inner: mydata() }, TstAnonMydataCombinator2(Choice::new(Cond { cond: tag == TstTag::C28, inner: mydata() }, TstAnonMydataCombinator1(Choice::new(Cond { cond: tag == TstTag::C29, inner: mydata() }, Cond { cond: tag == TstTag::C30, inner: mydata() })))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), mapper: TstAnonMydataMapper });
    // assert({
    //     &&& combinator@ == spec_tst_anon_mydata(tag@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_tst_anon_mydata<'a>(input: &'a [u8], tag: u8) -> (res: PResult<<TstAnonMydataCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_tst_tag().wf(tag@),

    ensures
        res matches Ok((n, v)) ==> spec_tst_anon_mydata(tag@).spec_parse(input@) == Some((n as int, v@)),
        spec_tst_anon_mydata(tag@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_tst_anon_mydata(tag@).spec_parse(input@) is None,
        spec_tst_anon_mydata(tag@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = tst_anon_mydata( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_tst_anon_mydata<'a>(v: <TstAnonMydataCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, tag: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_tst_anon_mydata(tag@).wf(v@),
        spec_tst_tag().wf(tag@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_tst_anon_mydata(tag@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_tst_anon_mydata(tag@).spec_serialize(v@))
        },
{
    let combinator = tst_anon_mydata( tag );
    combinator.serialize(v, data, pos)
}

pub fn tst_anon_mydata_len<'a>(v: <TstAnonMydataCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, tag: u8) -> (serialize_len: usize)
    requires
        spec_tst_anon_mydata(tag@).wf(v@),
        spec_tst_anon_mydata(tag@).spec_serialize(v@).len() <= usize::MAX,
        spec_tst_tag().wf(tag@),

    ensures
        serialize_len == spec_tst_anon_mydata(tag@).spec_serialize(v@).len(),
{
    let combinator = tst_anon_mydata( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecTst {
    pub tag: u8,
    pub mydata: SpecTstAnonMydata,
}

pub type SpecTstInner = (u8, SpecTstAnonMydata);


impl SpecFrom<SpecTst> for SpecTstInner {
    open spec fn spec_from(m: SpecTst) -> SpecTstInner {
        (m.tag, m.mydata)
    }
}

impl SpecFrom<SpecTstInner> for SpecTst {
    open spec fn spec_from(m: SpecTstInner) -> SpecTst {
        let (tag, mydata) = m;
        SpecTst { tag, mydata }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Tst<'a> {
    pub tag: u8,
    pub mydata: TstAnonMydata<'a>,
}

impl View for Tst<'_> {
    type V = SpecTst;

    open spec fn view(&self) -> Self::V {
        SpecTst {
            tag: self.tag@,
            mydata: self.mydata@,
        }
    }
}
pub type TstInner<'a> = (u8, TstAnonMydata<'a>);

pub type TstInnerRef<'a> = (&'a u8, &'a TstAnonMydata<'a>);
impl<'a> From<&'a Tst<'a>> for TstInnerRef<'a> {
    fn ex_from(m: &'a Tst) -> TstInnerRef<'a> {
        (&m.tag, &m.mydata)
    }
}

impl<'a> From<TstInner<'a>> for Tst<'a> {
    fn ex_from(m: TstInner) -> Tst {
        let (tag, mydata) = m;
        Tst { tag, mydata }
    }
}

pub struct TstMapper;
impl View for TstMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TstMapper {
    type Src = SpecTstInner;
    type Dst = SpecTst;
}
impl SpecIsoProof for TstMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TstMapper {
    type Src = TstInner<'a>;
    type Dst = Tst<'a>;
    type RefSrc = TstInnerRef<'a>;
}

pub struct SpecTstCombinator(pub SpecTstCombinatorAlias);

impl SpecCombinator for SpecTstCombinator {
    type Type = SpecTst;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTstCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTstCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTstCombinatorAlias = Mapped<SpecPair<SpecTstTagCombinator, SpecTstAnonMydataCombinator>, TstMapper>;

pub struct TstCombinator(pub TstCombinatorAlias);

impl View for TstCombinator {
    type V = SpecTstCombinator;
    open spec fn view(&self) -> Self::V { SpecTstCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TstCombinator {
    type Type = Tst<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type TstCombinatorAlias = Mapped<Pair<TstTagCombinator, TstAnonMydataCombinator, TstCont0>, TstMapper>;


pub open spec fn spec_tst() -> SpecTstCombinator {
    SpecTstCombinator(
    Mapped {
        inner: Pair::spec_new(spec_tst_tag(), |deps| spec_tst_cont0(deps)),
        mapper: TstMapper,
    })
}

pub open spec fn spec_tst_cont0(deps: u8) -> SpecTstAnonMydataCombinator {
    let tag = deps;
    spec_tst_anon_mydata(tag)
}

impl View for TstCont0 {
    type V = spec_fn(u8) -> SpecTstAnonMydataCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_tst_cont0(deps)
        }
    }
}

                
pub fn tst<'a>() -> (o: TstCombinator)
    ensures o@ == spec_tst(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TstCombinator(
    Mapped {
        inner: Pair::new(tst_tag(), TstCont0),
        mapper: TstMapper,
    });
    // assert({
    //     &&& combinator@ == spec_tst()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_tst<'a>(input: &'a [u8]) -> (res: PResult<<TstCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_tst().spec_parse(input@) == Some((n as int, v@)),
        spec_tst().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_tst().spec_parse(input@) is None,
        spec_tst().spec_parse(input@) is None ==> res is Err,
{
    let combinator = tst();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_tst<'a>(v: <TstCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_tst().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_tst().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_tst().spec_serialize(v@))
        },
{
    let combinator = tst();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn tst_len<'a>(v: <TstCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_tst().wf(v@),
        spec_tst().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_tst().spec_serialize(v@).len(),
{
    let combinator = tst();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct TstCont0;
type TstCont0Type<'a, 'b> = &'b u8;
type TstCont0SType<'a, 'x> = &'x u8;
type TstCont0Input<'a, 'b, 'x> = POrSType<TstCont0Type<'a, 'b>, TstCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TstCont0Input<'a, 'b, 'x>> for TstCont0 {
    type Output = TstAnonMydataCombinator;

    open spec fn requires(&self, deps: TstCont0Input<'a, 'b, 'x>) -> bool {
        &&& (spec_tst_tag()).wf(deps@)
        }

    open spec fn ensures(&self, deps: TstCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_tst_cont0(deps@)
    }

    fn apply(&self, deps: TstCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = deps;
                let tag = *tag;
                tst_anon_mydata(tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let tag = *tag;
                tst_anon_mydata(tag)
            }
        }
    }
}
                

pub struct SpecPairStress {
    pub f1: u8,
    pub f2: u16,
    pub f3: u32,
    pub f4: u8,
    pub f5: u8,
    pub f6: u8,
    pub f7: u8,
    pub f8: u8,
    pub f9: u8,
    pub f10: u8,
    pub f11: u8,
    pub f12: u8,
    pub f13: u8,
    pub f14: u8,
    pub f15: u8,
}

pub type SpecPairStressInner = (u8, (u16, (u32, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8))))))))))))));


impl SpecFrom<SpecPairStress> for SpecPairStressInner {
    open spec fn spec_from(m: SpecPairStress) -> SpecPairStressInner {
        (m.f1, (m.f2, (m.f3, (m.f4, (m.f5, (m.f6, (m.f7, (m.f8, (m.f9, (m.f10, (m.f11, (m.f12, (m.f13, (m.f14, m.f15))))))))))))))
    }
}

impl SpecFrom<SpecPairStressInner> for SpecPairStress {
    open spec fn spec_from(m: SpecPairStressInner) -> SpecPairStress {
        let (f1, (f2, (f3, (f4, (f5, (f6, (f7, (f8, (f9, (f10, (f11, (f12, (f13, (f14, f15)))))))))))))) = m;
        SpecPairStress { f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PairStress {
    pub f1: u8,
    pub f2: u16,
    pub f3: u32,
    pub f4: u8,
    pub f5: u8,
    pub f6: u8,
    pub f7: u8,
    pub f8: u8,
    pub f9: u8,
    pub f10: u8,
    pub f11: u8,
    pub f12: u8,
    pub f13: u8,
    pub f14: u8,
    pub f15: u8,
}

impl View for PairStress {
    type V = SpecPairStress;

    open spec fn view(&self) -> Self::V {
        SpecPairStress {
            f1: self.f1@,
            f2: self.f2@,
            f3: self.f3@,
            f4: self.f4@,
            f5: self.f5@,
            f6: self.f6@,
            f7: self.f7@,
            f8: self.f8@,
            f9: self.f9@,
            f10: self.f10@,
            f11: self.f11@,
            f12: self.f12@,
            f13: self.f13@,
            f14: self.f14@,
            f15: self.f15@,
        }
    }
}
pub type PairStressInner = (u8, (u16, (u32, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8))))))))))))));

pub type PairStressInnerRef<'a> = (&'a u8, (&'a u16, (&'a u32, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, &'a u8))))))))))))));
impl<'a> From<&'a PairStress> for PairStressInnerRef<'a> {
    fn ex_from(m: &'a PairStress) -> PairStressInnerRef<'a> {
        (&m.f1, (&m.f2, (&m.f3, (&m.f4, (&m.f5, (&m.f6, (&m.f7, (&m.f8, (&m.f9, (&m.f10, (&m.f11, (&m.f12, (&m.f13, (&m.f14, &m.f15))))))))))))))
    }
}

impl From<PairStressInner> for PairStress {
    fn ex_from(m: PairStressInner) -> PairStress {
        let (f1, (f2, (f3, (f4, (f5, (f6, (f7, (f8, (f9, (f10, (f11, (f12, (f13, (f14, f15)))))))))))))) = m;
        PairStress { f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15 }
    }
}

pub struct PairStressMapper;
impl View for PairStressMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PairStressMapper {
    type Src = SpecPairStressInner;
    type Dst = SpecPairStress;
}
impl SpecIsoProof for PairStressMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PairStressMapper {
    type Src = PairStressInner;
    type Dst = PairStress;
    type RefSrc = PairStressInnerRef<'a>;
}
type SpecPairStressCombinatorAlias1 = (U8, U8);
type SpecPairStressCombinatorAlias2 = (U8, SpecPairStressCombinatorAlias1);
type SpecPairStressCombinatorAlias3 = (U8, SpecPairStressCombinatorAlias2);
type SpecPairStressCombinatorAlias4 = (U8, SpecPairStressCombinatorAlias3);
type SpecPairStressCombinatorAlias5 = (U8, SpecPairStressCombinatorAlias4);
type SpecPairStressCombinatorAlias6 = (U8, SpecPairStressCombinatorAlias5);
type SpecPairStressCombinatorAlias7 = (U8, SpecPairStressCombinatorAlias6);
type SpecPairStressCombinatorAlias8 = (U8, SpecPairStressCombinatorAlias7);
type SpecPairStressCombinatorAlias9 = (U8, SpecPairStressCombinatorAlias8);
type SpecPairStressCombinatorAlias10 = (U8, SpecPairStressCombinatorAlias9);
type SpecPairStressCombinatorAlias11 = (U8, SpecPairStressCombinatorAlias10);
type SpecPairStressCombinatorAlias12 = (U32Le, SpecPairStressCombinatorAlias11);
type SpecPairStressCombinatorAlias13 = (U16Le, SpecPairStressCombinatorAlias12);
type SpecPairStressCombinatorAlias14 = (U8, SpecPairStressCombinatorAlias13);
pub struct SpecPairStressCombinator(pub SpecPairStressCombinatorAlias);

impl SpecCombinator for SpecPairStressCombinator {
    type Type = SpecPairStress;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPairStressCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecPairStressCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecPairStressCombinatorAlias = Mapped<SpecPairStressCombinatorAlias14, PairStressMapper>;
type PairStressCombinatorAlias1 = (U8, U8);
type PairStressCombinatorAlias2 = (U8, PairStressCombinator1);
type PairStressCombinatorAlias3 = (U8, PairStressCombinator2);
type PairStressCombinatorAlias4 = (U8, PairStressCombinator3);
type PairStressCombinatorAlias5 = (U8, PairStressCombinator4);
type PairStressCombinatorAlias6 = (U8, PairStressCombinator5);
type PairStressCombinatorAlias7 = (U8, PairStressCombinator6);
type PairStressCombinatorAlias8 = (U8, PairStressCombinator7);
type PairStressCombinatorAlias9 = (U8, PairStressCombinator8);
type PairStressCombinatorAlias10 = (U8, PairStressCombinator9);
type PairStressCombinatorAlias11 = (U8, PairStressCombinator10);
type PairStressCombinatorAlias12 = (U32Le, PairStressCombinator11);
type PairStressCombinatorAlias13 = (U16Le, PairStressCombinator12);
type PairStressCombinatorAlias14 = (U8, PairStressCombinator13);
pub struct PairStressCombinator1(pub PairStressCombinatorAlias1);
impl View for PairStressCombinator1 {
    type V = SpecPairStressCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator1, PairStressCombinatorAlias1);

pub struct PairStressCombinator2(pub PairStressCombinatorAlias2);
impl View for PairStressCombinator2 {
    type V = SpecPairStressCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator2, PairStressCombinatorAlias2);

pub struct PairStressCombinator3(pub PairStressCombinatorAlias3);
impl View for PairStressCombinator3 {
    type V = SpecPairStressCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator3, PairStressCombinatorAlias3);

pub struct PairStressCombinator4(pub PairStressCombinatorAlias4);
impl View for PairStressCombinator4 {
    type V = SpecPairStressCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator4, PairStressCombinatorAlias4);

pub struct PairStressCombinator5(pub PairStressCombinatorAlias5);
impl View for PairStressCombinator5 {
    type V = SpecPairStressCombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator5, PairStressCombinatorAlias5);

pub struct PairStressCombinator6(pub PairStressCombinatorAlias6);
impl View for PairStressCombinator6 {
    type V = SpecPairStressCombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator6, PairStressCombinatorAlias6);

pub struct PairStressCombinator7(pub PairStressCombinatorAlias7);
impl View for PairStressCombinator7 {
    type V = SpecPairStressCombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator7, PairStressCombinatorAlias7);

pub struct PairStressCombinator8(pub PairStressCombinatorAlias8);
impl View for PairStressCombinator8 {
    type V = SpecPairStressCombinatorAlias8;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator8, PairStressCombinatorAlias8);

pub struct PairStressCombinator9(pub PairStressCombinatorAlias9);
impl View for PairStressCombinator9 {
    type V = SpecPairStressCombinatorAlias9;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator9, PairStressCombinatorAlias9);

pub struct PairStressCombinator10(pub PairStressCombinatorAlias10);
impl View for PairStressCombinator10 {
    type V = SpecPairStressCombinatorAlias10;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator10, PairStressCombinatorAlias10);

pub struct PairStressCombinator11(pub PairStressCombinatorAlias11);
impl View for PairStressCombinator11 {
    type V = SpecPairStressCombinatorAlias11;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator11, PairStressCombinatorAlias11);

pub struct PairStressCombinator12(pub PairStressCombinatorAlias12);
impl View for PairStressCombinator12 {
    type V = SpecPairStressCombinatorAlias12;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator12, PairStressCombinatorAlias12);

pub struct PairStressCombinator13(pub PairStressCombinatorAlias13);
impl View for PairStressCombinator13 {
    type V = SpecPairStressCombinatorAlias13;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator13, PairStressCombinatorAlias13);

pub struct PairStressCombinator14(pub PairStressCombinatorAlias14);
impl View for PairStressCombinator14 {
    type V = SpecPairStressCombinatorAlias14;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator14, PairStressCombinatorAlias14);

pub struct PairStressCombinator(pub PairStressCombinatorAlias);

impl View for PairStressCombinator {
    type V = SpecPairStressCombinator;
    open spec fn view(&self) -> Self::V { SpecPairStressCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator {
    type Type = PairStress;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type PairStressCombinatorAlias = Mapped<PairStressCombinator14, PairStressMapper>;


pub open spec fn spec_pair_stress() -> SpecPairStressCombinator {
    SpecPairStressCombinator(
    Mapped {
        inner: (U8, (U16Le, (U32Le, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, U8)))))))))))))),
        mapper: PairStressMapper,
    })
}

                
pub fn pair_stress<'a>() -> (o: PairStressCombinator)
    ensures o@ == spec_pair_stress(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = PairStressCombinator(
    Mapped {
        inner: PairStressCombinator14((U8, PairStressCombinator13((U16Le, PairStressCombinator12((U32Le, PairStressCombinator11((U8, PairStressCombinator10((U8, PairStressCombinator9((U8, PairStressCombinator8((U8, PairStressCombinator7((U8, PairStressCombinator6((U8, PairStressCombinator5((U8, PairStressCombinator4((U8, PairStressCombinator3((U8, PairStressCombinator2((U8, PairStressCombinator1((U8, U8)))))))))))))))))))))))))))),
        mapper: PairStressMapper,
    });
    // assert({
    //     &&& combinator@ == spec_pair_stress()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_pair_stress<'a>(input: &'a [u8]) -> (res: PResult<<PairStressCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_pair_stress().spec_parse(input@) == Some((n as int, v@)),
        spec_pair_stress().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_pair_stress().spec_parse(input@) is None,
        spec_pair_stress().spec_parse(input@) is None ==> res is Err,
{
    let combinator = pair_stress();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_pair_stress<'a>(v: <PairStressCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_pair_stress().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_pair_stress().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_pair_stress().spec_serialize(v@))
        },
{
    let combinator = pair_stress();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn pair_stress_len<'a>(v: <PairStressCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_pair_stress().wf(v@),
        spec_pair_stress().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_pair_stress().spec_serialize(v@).len(),
{
    let combinator = pair_stress();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
