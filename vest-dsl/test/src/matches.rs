
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

pub enum SpecMsg3AnonContent {
    Variant0(u16),
    Variant1(u32),
    Variant2(u32),
    Variant3(Seq<u8>),
}

pub type SpecMsg3AnonContentInner = Either<u16, Either<u32, Either<u32, Seq<u8>>>>;

impl SpecFrom<SpecMsg3AnonContent> for SpecMsg3AnonContentInner {
    open spec fn spec_from(m: SpecMsg3AnonContent) -> SpecMsg3AnonContentInner {
        match m {
            SpecMsg3AnonContent::Variant0(m) => Either::Left(m),
            SpecMsg3AnonContent::Variant1(m) => Either::Right(Either::Left(m)),
            SpecMsg3AnonContent::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecMsg3AnonContent::Variant3(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

                
impl SpecFrom<SpecMsg3AnonContentInner> for SpecMsg3AnonContent {
    open spec fn spec_from(m: SpecMsg3AnonContentInner) -> SpecMsg3AnonContent {
        match m {
            Either::Left(m) => SpecMsg3AnonContent::Variant0(m),
            Either::Right(Either::Left(m)) => SpecMsg3AnonContent::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecMsg3AnonContent::Variant2(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecMsg3AnonContent::Variant3(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg3AnonContent<'a> {
    Variant0(u16),
    Variant1(u32),
    Variant2(u32),
    Variant3(&'a [u8]),
}

pub type Msg3AnonContentInner<'a> = Either<u16, Either<u32, Either<u32, &'a [u8]>>>;

pub type Msg3AnonContentInnerRef<'a> = Either<&'a u16, Either<&'a u32, Either<&'a u32, &'a &'a [u8]>>>;


impl<'a> View for Msg3AnonContent<'a> {
    type V = SpecMsg3AnonContent;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg3AnonContent::Variant0(m) => SpecMsg3AnonContent::Variant0(m@),
            Msg3AnonContent::Variant1(m) => SpecMsg3AnonContent::Variant1(m@),
            Msg3AnonContent::Variant2(m) => SpecMsg3AnonContent::Variant2(m@),
            Msg3AnonContent::Variant3(m) => SpecMsg3AnonContent::Variant3(m@),
        }
    }
}


impl<'a> From<&'a Msg3AnonContent<'a>> for Msg3AnonContentInnerRef<'a> {
    fn ex_from(m: &'a Msg3AnonContent<'a>) -> Msg3AnonContentInnerRef<'a> {
        match m {
            Msg3AnonContent::Variant0(m) => Either::Left(m),
            Msg3AnonContent::Variant1(m) => Either::Right(Either::Left(m)),
            Msg3AnonContent::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            Msg3AnonContent::Variant3(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl<'a> From<Msg3AnonContentInner<'a>> for Msg3AnonContent<'a> {
    fn ex_from(m: Msg3AnonContentInner<'a>) -> Msg3AnonContent<'a> {
        match m {
            Either::Left(m) => Msg3AnonContent::Variant0(m),
            Either::Right(Either::Left(m)) => Msg3AnonContent::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => Msg3AnonContent::Variant2(m),
            Either::Right(Either::Right(Either::Right(m))) => Msg3AnonContent::Variant3(m),
        }
    }
    
}


pub struct Msg3AnonContentMapper;
impl View for Msg3AnonContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg3AnonContentMapper {
    type Src = SpecMsg3AnonContentInner;
    type Dst = SpecMsg3AnonContent;
}
impl SpecIsoProof for Msg3AnonContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg3AnonContentMapper {
    type Src = Msg3AnonContentInner<'a>;
    type Dst = Msg3AnonContent<'a>;
    type RefSrc = Msg3AnonContentInnerRef<'a>;
}

type SpecMsg3AnonContentCombinatorAlias1 = Choice<Cond<U32Le>, Cond<bytes::Tail>>;
type SpecMsg3AnonContentCombinatorAlias2 = Choice<Cond<U32Le>, SpecMsg3AnonContentCombinatorAlias1>;
type SpecMsg3AnonContentCombinatorAlias3 = Choice<Cond<U16Le>, SpecMsg3AnonContentCombinatorAlias2>;
pub struct SpecMsg3AnonContentCombinator(pub SpecMsg3AnonContentCombinatorAlias);

impl SpecCombinator for SpecMsg3AnonContentCombinator {
    type Type = SpecMsg3AnonContent;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg3AnonContentCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsg3AnonContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg3AnonContentCombinatorAlias = Mapped<SpecMsg3AnonContentCombinatorAlias3, Msg3AnonContentMapper>;
type Msg3AnonContentCombinatorAlias1 = Choice<Cond<U32Le>, Cond<bytes::Tail>>;
type Msg3AnonContentCombinatorAlias2 = Choice<Cond<U32Le>, Msg3AnonContentCombinator1>;
type Msg3AnonContentCombinatorAlias3 = Choice<Cond<U16Le>, Msg3AnonContentCombinator2>;
pub struct Msg3AnonContentCombinator1(pub Msg3AnonContentCombinatorAlias1);
impl View for Msg3AnonContentCombinator1 {
    type V = SpecMsg3AnonContentCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg3AnonContentCombinator1, Msg3AnonContentCombinatorAlias1);

pub struct Msg3AnonContentCombinator2(pub Msg3AnonContentCombinatorAlias2);
impl View for Msg3AnonContentCombinator2 {
    type V = SpecMsg3AnonContentCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg3AnonContentCombinator2, Msg3AnonContentCombinatorAlias2);

pub struct Msg3AnonContentCombinator3(pub Msg3AnonContentCombinatorAlias3);
impl View for Msg3AnonContentCombinator3 {
    type V = SpecMsg3AnonContentCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg3AnonContentCombinator3, Msg3AnonContentCombinatorAlias3);

pub struct Msg3AnonContentCombinator(pub Msg3AnonContentCombinatorAlias);

impl View for Msg3AnonContentCombinator {
    type V = SpecMsg3AnonContentCombinator;
    open spec fn view(&self) -> Self::V { SpecMsg3AnonContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg3AnonContentCombinator {
    type Type = Msg3AnonContent<'a>;
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
pub type Msg3AnonContentCombinatorAlias = Mapped<Msg3AnonContentCombinator3, Msg3AnonContentMapper>;


pub open spec fn spec_msg3_anon_content(i: u8) -> SpecMsg3AnonContentCombinator {
    SpecMsg3AnonContentCombinator(Mapped { inner: Choice(Cond { cond: i == 1, inner: U16Le }, Choice(Cond { cond: i == 2, inner: U32Le }, Choice(Cond { cond: i == 3, inner: U32Le }, Cond { cond: !(i == 1 || i == 2 || i == 3), inner: bytes::Tail }))), mapper: Msg3AnonContentMapper })
}

pub fn msg3_anon_content<'a>(i: u8) -> (o: Msg3AnonContentCombinator)

    ensures o@ == spec_msg3_anon_content(i@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg3AnonContentCombinator(Mapped { inner: Msg3AnonContentCombinator3(Choice::new(Cond { cond: i == 1, inner: U16Le }, Msg3AnonContentCombinator2(Choice::new(Cond { cond: i == 2, inner: U32Le }, Msg3AnonContentCombinator1(Choice::new(Cond { cond: i == 3, inner: U32Le }, Cond { cond: !(i == 1 || i == 2 || i == 3), inner: bytes::Tail })))))), mapper: Msg3AnonContentMapper });
    // assert({
    //     &&& combinator@ == spec_msg3_anon_content(i@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg3_anon_content<'a>(input: &'a [u8], i: u8) -> (res: PResult<<Msg3AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_msg3_anon_content(i@).spec_parse(input@) == Some((n as int, v@)),
        spec_msg3_anon_content(i@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg3_anon_content(i@).spec_parse(input@) is None,
        spec_msg3_anon_content(i@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg3_anon_content( i );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg3_anon_content<'a>(v: <Msg3AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, i: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg3_anon_content(i@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg3_anon_content(i@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg3_anon_content(i@).spec_serialize(v@))
        },
{
    let combinator = msg3_anon_content( i );
    combinator.serialize(v, data, pos)
}

pub fn msg3_anon_content_len<'a>(v: <Msg3AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, i: u8) -> (serialize_len: usize)
    requires
        spec_msg3_anon_content(i@).wf(v@),
        spec_msg3_anon_content(i@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_msg3_anon_content(i@).spec_serialize(v@).len(),
{
    let combinator = msg3_anon_content( i );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecMsg5AnonContent {
    Variant0(u16),
    Variant1(Seq<u8>),
}

pub type SpecMsg5AnonContentInner = Either<u16, Seq<u8>>;

impl SpecFrom<SpecMsg5AnonContent> for SpecMsg5AnonContentInner {
    open spec fn spec_from(m: SpecMsg5AnonContent) -> SpecMsg5AnonContentInner {
        match m {
            SpecMsg5AnonContent::Variant0(m) => Either::Left(m),
            SpecMsg5AnonContent::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecMsg5AnonContentInner> for SpecMsg5AnonContent {
    open spec fn spec_from(m: SpecMsg5AnonContentInner) -> SpecMsg5AnonContent {
        match m {
            Either::Left(m) => SpecMsg5AnonContent::Variant0(m),
            Either::Right(m) => SpecMsg5AnonContent::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg5AnonContent<'a> {
    Variant0(u16),
    Variant1(&'a [u8]),
}

pub type Msg5AnonContentInner<'a> = Either<u16, &'a [u8]>;

pub type Msg5AnonContentInnerRef<'a> = Either<&'a u16, &'a &'a [u8]>;


impl<'a> View for Msg5AnonContent<'a> {
    type V = SpecMsg5AnonContent;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg5AnonContent::Variant0(m) => SpecMsg5AnonContent::Variant0(m@),
            Msg5AnonContent::Variant1(m) => SpecMsg5AnonContent::Variant1(m@),
        }
    }
}


impl<'a> From<&'a Msg5AnonContent<'a>> for Msg5AnonContentInnerRef<'a> {
    fn ex_from(m: &'a Msg5AnonContent<'a>) -> Msg5AnonContentInnerRef<'a> {
        match m {
            Msg5AnonContent::Variant0(m) => Either::Left(m),
            Msg5AnonContent::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<Msg5AnonContentInner<'a>> for Msg5AnonContent<'a> {
    fn ex_from(m: Msg5AnonContentInner<'a>) -> Msg5AnonContent<'a> {
        match m {
            Either::Left(m) => Msg5AnonContent::Variant0(m),
            Either::Right(m) => Msg5AnonContent::Variant1(m),
        }
    }
    
}


pub struct Msg5AnonContentMapper;
impl View for Msg5AnonContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg5AnonContentMapper {
    type Src = SpecMsg5AnonContentInner;
    type Dst = SpecMsg5AnonContent;
}
impl SpecIsoProof for Msg5AnonContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg5AnonContentMapper {
    type Src = Msg5AnonContentInner<'a>;
    type Dst = Msg5AnonContent<'a>;
    type RefSrc = Msg5AnonContentInnerRef<'a>;
}

type SpecMsg5AnonContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<bytes::Tail>>;
pub struct SpecMsg5AnonContentCombinator(pub SpecMsg5AnonContentCombinatorAlias);

impl SpecCombinator for SpecMsg5AnonContentCombinator {
    type Type = SpecMsg5AnonContent;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg5AnonContentCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsg5AnonContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg5AnonContentCombinatorAlias = Mapped<SpecMsg5AnonContentCombinatorAlias1, Msg5AnonContentMapper>;
type Msg5AnonContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<bytes::Tail>>;
pub struct Msg5AnonContentCombinator1(pub Msg5AnonContentCombinatorAlias1);
impl View for Msg5AnonContentCombinator1 {
    type V = SpecMsg5AnonContentCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg5AnonContentCombinator1, Msg5AnonContentCombinatorAlias1);

pub struct Msg5AnonContentCombinator(pub Msg5AnonContentCombinatorAlias);

impl View for Msg5AnonContentCombinator {
    type V = SpecMsg5AnonContentCombinator;
    open spec fn view(&self) -> Self::V { SpecMsg5AnonContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg5AnonContentCombinator {
    type Type = Msg5AnonContent<'a>;
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
pub type Msg5AnonContentCombinatorAlias = Mapped<Msg5AnonContentCombinator1, Msg5AnonContentMapper>;


pub open spec fn spec_msg5_anon_content(i: VarInt) -> SpecMsg5AnonContentCombinator {
    SpecMsg5AnonContentCombinator(Mapped { inner: Choice(Cond { cond: i.spec_as_usize() == 1, inner: U16Le }, Cond { cond: !(i.spec_as_usize() == 1), inner: bytes::Tail }), mapper: Msg5AnonContentMapper })
}

pub fn msg5_anon_content<'a>(i: VarInt) -> (o: Msg5AnonContentCombinator)

    ensures o@ == spec_msg5_anon_content(i@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg5AnonContentCombinator(Mapped { inner: Msg5AnonContentCombinator1(Choice::new(Cond { cond: i.as_usize() == 1, inner: U16Le }, Cond { cond: !(i.as_usize() == 1), inner: bytes::Tail })), mapper: Msg5AnonContentMapper });
    // assert({
    //     &&& combinator@ == spec_msg5_anon_content(i@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg5_anon_content<'a>(input: &'a [u8], i: VarInt) -> (res: PResult<<Msg5AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_msg5_anon_content(i@).spec_parse(input@) == Some((n as int, v@)),
        spec_msg5_anon_content(i@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg5_anon_content(i@).spec_parse(input@) is None,
        spec_msg5_anon_content(i@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg5_anon_content( i );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg5_anon_content<'a>(v: <Msg5AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, i: VarInt) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg5_anon_content(i@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg5_anon_content(i@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg5_anon_content(i@).spec_serialize(v@))
        },
{
    let combinator = msg5_anon_content( i );
    combinator.serialize(v, data, pos)
}

pub fn msg5_anon_content_len<'a>(v: <Msg5AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, i: VarInt) -> (serialize_len: usize)
    requires
        spec_msg5_anon_content(i@).wf(v@),
        spec_msg5_anon_content(i@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_msg5_anon_content(i@).spec_serialize(v@).len(),
{
    let combinator = msg5_anon_content( i );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecMsg3 {
    pub i: u8,
    pub content: SpecMsg3AnonContent,
}

pub type SpecMsg3Inner = (u8, SpecMsg3AnonContent);


impl SpecFrom<SpecMsg3> for SpecMsg3Inner {
    open spec fn spec_from(m: SpecMsg3) -> SpecMsg3Inner {
        (m.i, m.content)
    }
}

impl SpecFrom<SpecMsg3Inner> for SpecMsg3 {
    open spec fn spec_from(m: SpecMsg3Inner) -> SpecMsg3 {
        let (i, content) = m;
        SpecMsg3 { i, content }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg3<'a> {
    pub i: u8,
    pub content: Msg3AnonContent<'a>,
}

impl View for Msg3<'_> {
    type V = SpecMsg3;

    open spec fn view(&self) -> Self::V {
        SpecMsg3 {
            i: self.i@,
            content: self.content@,
        }
    }
}
pub type Msg3Inner<'a> = (u8, Msg3AnonContent<'a>);

pub type Msg3InnerRef<'a> = (&'a u8, &'a Msg3AnonContent<'a>);
impl<'a> From<&'a Msg3<'a>> for Msg3InnerRef<'a> {
    fn ex_from(m: &'a Msg3) -> Msg3InnerRef<'a> {
        (&m.i, &m.content)
    }
}

impl<'a> From<Msg3Inner<'a>> for Msg3<'a> {
    fn ex_from(m: Msg3Inner) -> Msg3 {
        let (i, content) = m;
        Msg3 { i, content }
    }
}

pub struct Msg3Mapper;
impl View for Msg3Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg3Mapper {
    type Src = SpecMsg3Inner;
    type Dst = SpecMsg3;
}
impl SpecIsoProof for Msg3Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg3Mapper {
    type Src = Msg3Inner<'a>;
    type Dst = Msg3<'a>;
    type RefSrc = Msg3InnerRef<'a>;
}

pub struct SpecMsg3Combinator(pub SpecMsg3CombinatorAlias);

impl SpecCombinator for SpecMsg3Combinator {
    type Type = SpecMsg3;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
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
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMsg3CombinatorAlias = Mapped<SpecPair<U8, SpecMsg3AnonContentCombinator>, Msg3Mapper>;

pub struct Msg3Combinator(pub Msg3CombinatorAlias);

impl View for Msg3Combinator {
    type V = SpecMsg3Combinator;
    open spec fn view(&self) -> Self::V { SpecMsg3Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg3Combinator {
    type Type = Msg3<'a>;
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
pub type Msg3CombinatorAlias = Mapped<Pair<U8, Msg3AnonContentCombinator, Msg3Cont0>, Msg3Mapper>;


pub open spec fn spec_msg3() -> SpecMsg3Combinator {
    SpecMsg3Combinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_msg3_cont0(deps)),
        mapper: Msg3Mapper,
    })
}

pub open spec fn spec_msg3_cont0(deps: u8) -> SpecMsg3AnonContentCombinator {
    let i = deps;
    spec_msg3_anon_content(i)
}

impl View for Msg3Cont0 {
    type V = spec_fn(u8) -> SpecMsg3AnonContentCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_msg3_cont0(deps)
        }
    }
}

                
pub fn msg3<'a>() -> (o: Msg3Combinator)
    ensures o@ == spec_msg3(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg3Combinator(
    Mapped {
        inner: Pair::new(U8, Msg3Cont0),
        mapper: Msg3Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_msg3()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
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

pub fn msg3_len<'a>(v: <Msg3Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_msg3().wf(v@),
        spec_msg3().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_msg3().spec_serialize(v@).len(),
{
    let combinator = msg3();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct Msg3Cont0;
type Msg3Cont0Type<'a, 'b> = &'b u8;
type Msg3Cont0SType<'a, 'x> = &'x u8;
type Msg3Cont0Input<'a, 'b, 'x> = POrSType<Msg3Cont0Type<'a, 'b>, Msg3Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg3Cont0Input<'a, 'b, 'x>> for Msg3Cont0 {
    type Output = Msg3AnonContentCombinator;

    open spec fn requires(&self, deps: Msg3Cont0Input<'a, 'b, 'x>) -> bool {
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: Msg3Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_msg3_cont0(deps@)
    }

    fn apply(&self, deps: Msg3Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let i = deps;
                let i = *i;
                msg3_anon_content(i)
            }
            POrSType::S(deps) => {
                let i = deps;
                let i = *i;
                msg3_anon_content(i)
            }
        }
    }
}
                

pub struct SpecMsg5 {
    pub i: VarInt,
    pub content: SpecMsg5AnonContent,
}

pub type SpecMsg5Inner = (VarInt, SpecMsg5AnonContent);


impl SpecFrom<SpecMsg5> for SpecMsg5Inner {
    open spec fn spec_from(m: SpecMsg5) -> SpecMsg5Inner {
        (m.i, m.content)
    }
}

impl SpecFrom<SpecMsg5Inner> for SpecMsg5 {
    open spec fn spec_from(m: SpecMsg5Inner) -> SpecMsg5 {
        let (i, content) = m;
        SpecMsg5 { i, content }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg5<'a> {
    pub i: VarInt,
    pub content: Msg5AnonContent<'a>,
}

impl View for Msg5<'_> {
    type V = SpecMsg5;

    open spec fn view(&self) -> Self::V {
        SpecMsg5 {
            i: self.i@,
            content: self.content@,
        }
    }
}
pub type Msg5Inner<'a> = (VarInt, Msg5AnonContent<'a>);

pub type Msg5InnerRef<'a> = (&'a VarInt, &'a Msg5AnonContent<'a>);
impl<'a> From<&'a Msg5<'a>> for Msg5InnerRef<'a> {
    fn ex_from(m: &'a Msg5) -> Msg5InnerRef<'a> {
        (&m.i, &m.content)
    }
}

impl<'a> From<Msg5Inner<'a>> for Msg5<'a> {
    fn ex_from(m: Msg5Inner) -> Msg5 {
        let (i, content) = m;
        Msg5 { i, content }
    }
}

pub struct Msg5Mapper;
impl View for Msg5Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg5Mapper {
    type Src = SpecMsg5Inner;
    type Dst = SpecMsg5;
}
impl SpecIsoProof for Msg5Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg5Mapper {
    type Src = Msg5Inner<'a>;
    type Dst = Msg5<'a>;
    type RefSrc = Msg5InnerRef<'a>;
}

pub struct SpecMsg5Combinator(pub SpecMsg5CombinatorAlias);

impl SpecCombinator for SpecMsg5Combinator {
    type Type = SpecMsg5;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg5Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsg5CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg5CombinatorAlias = Mapped<SpecPair<BtcVarint, SpecMsg5AnonContentCombinator>, Msg5Mapper>;

pub struct Msg5Combinator(pub Msg5CombinatorAlias);

impl View for Msg5Combinator {
    type V = SpecMsg5Combinator;
    open spec fn view(&self) -> Self::V { SpecMsg5Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg5Combinator {
    type Type = Msg5<'a>;
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
pub type Msg5CombinatorAlias = Mapped<Pair<BtcVarint, Msg5AnonContentCombinator, Msg5Cont0>, Msg5Mapper>;


pub open spec fn spec_msg5() -> SpecMsg5Combinator {
    SpecMsg5Combinator(
    Mapped {
        inner: Pair::spec_new(BtcVarint, |deps| spec_msg5_cont0(deps)),
        mapper: Msg5Mapper,
    })
}

pub open spec fn spec_msg5_cont0(deps: VarInt) -> SpecMsg5AnonContentCombinator {
    let i = deps;
    spec_msg5_anon_content(i)
}

impl View for Msg5Cont0 {
    type V = spec_fn(VarInt) -> SpecMsg5AnonContentCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: VarInt| {
            spec_msg5_cont0(deps)
        }
    }
}

                
pub fn msg5<'a>() -> (o: Msg5Combinator)
    ensures o@ == spec_msg5(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg5Combinator(
    Mapped {
        inner: Pair::new(BtcVarint, Msg5Cont0),
        mapper: Msg5Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_msg5()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg5<'a>(input: &'a [u8]) -> (res: PResult<<Msg5Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_msg5().spec_parse(input@) == Some((n as int, v@)),
        spec_msg5().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg5().spec_parse(input@) is None,
        spec_msg5().spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg5();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg5<'a>(v: <Msg5Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg5().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg5().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg5().spec_serialize(v@))
        },
{
    let combinator = msg5();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn msg5_len<'a>(v: <Msg5Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_msg5().wf(v@),
        spec_msg5().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_msg5().spec_serialize(v@).len(),
{
    let combinator = msg5();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct Msg5Cont0;
type Msg5Cont0Type<'a, 'b> = &'b VarInt;
type Msg5Cont0SType<'a, 'x> = &'x VarInt;
type Msg5Cont0Input<'a, 'b, 'x> = POrSType<Msg5Cont0Type<'a, 'b>, Msg5Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg5Cont0Input<'a, 'b, 'x>> for Msg5Cont0 {
    type Output = Msg5AnonContentCombinator;

    open spec fn requires(&self, deps: Msg5Cont0Input<'a, 'b, 'x>) -> bool {
        &&& (BtcVarint).wf(deps@)
        }

    open spec fn ensures(&self, deps: Msg5Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_msg5_cont0(deps@)
    }

    fn apply(&self, deps: Msg5Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let i = deps;
                let i = *i;
                msg5_anon_content(i)
            }
            POrSType::S(deps) => {
                let i = deps;
                let i = *i;
                msg5_anon_content(i)
            }
        }
    }
}
                

pub enum SpecMsg4AnonContent {
    Variant0(u16),
    Variant1(Seq<u8>),
}

pub type SpecMsg4AnonContentInner = Either<u16, Seq<u8>>;

impl SpecFrom<SpecMsg4AnonContent> for SpecMsg4AnonContentInner {
    open spec fn spec_from(m: SpecMsg4AnonContent) -> SpecMsg4AnonContentInner {
        match m {
            SpecMsg4AnonContent::Variant0(m) => Either::Left(m),
            SpecMsg4AnonContent::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecMsg4AnonContentInner> for SpecMsg4AnonContent {
    open spec fn spec_from(m: SpecMsg4AnonContentInner) -> SpecMsg4AnonContent {
        match m {
            Either::Left(m) => SpecMsg4AnonContent::Variant0(m),
            Either::Right(m) => SpecMsg4AnonContent::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg4AnonContent<'a> {
    Variant0(u16),
    Variant1(&'a [u8]),
}

pub type Msg4AnonContentInner<'a> = Either<u16, &'a [u8]>;

pub type Msg4AnonContentInnerRef<'a> = Either<&'a u16, &'a &'a [u8]>;


impl<'a> View for Msg4AnonContent<'a> {
    type V = SpecMsg4AnonContent;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg4AnonContent::Variant0(m) => SpecMsg4AnonContent::Variant0(m@),
            Msg4AnonContent::Variant1(m) => SpecMsg4AnonContent::Variant1(m@),
        }
    }
}


impl<'a> From<&'a Msg4AnonContent<'a>> for Msg4AnonContentInnerRef<'a> {
    fn ex_from(m: &'a Msg4AnonContent<'a>) -> Msg4AnonContentInnerRef<'a> {
        match m {
            Msg4AnonContent::Variant0(m) => Either::Left(m),
            Msg4AnonContent::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<Msg4AnonContentInner<'a>> for Msg4AnonContent<'a> {
    fn ex_from(m: Msg4AnonContentInner<'a>) -> Msg4AnonContent<'a> {
        match m {
            Either::Left(m) => Msg4AnonContent::Variant0(m),
            Either::Right(m) => Msg4AnonContent::Variant1(m),
        }
    }
    
}


pub struct Msg4AnonContentMapper;
impl View for Msg4AnonContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg4AnonContentMapper {
    type Src = SpecMsg4AnonContentInner;
    type Dst = SpecMsg4AnonContent;
}
impl SpecIsoProof for Msg4AnonContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg4AnonContentMapper {
    type Src = Msg4AnonContentInner<'a>;
    type Dst = Msg4AnonContent<'a>;
    type RefSrc = Msg4AnonContentInnerRef<'a>;
}

type SpecMsg4AnonContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<bytes::Tail>>;
pub struct SpecMsg4AnonContentCombinator(pub SpecMsg4AnonContentCombinatorAlias);

impl SpecCombinator for SpecMsg4AnonContentCombinator {
    type Type = SpecMsg4AnonContent;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg4AnonContentCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsg4AnonContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg4AnonContentCombinatorAlias = Mapped<SpecMsg4AnonContentCombinatorAlias1, Msg4AnonContentMapper>;
type Msg4AnonContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<bytes::Tail>>;
pub struct Msg4AnonContentCombinator1(pub Msg4AnonContentCombinatorAlias1);
impl View for Msg4AnonContentCombinator1 {
    type V = SpecMsg4AnonContentCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg4AnonContentCombinator1, Msg4AnonContentCombinatorAlias1);

pub struct Msg4AnonContentCombinator(pub Msg4AnonContentCombinatorAlias);

impl View for Msg4AnonContentCombinator {
    type V = SpecMsg4AnonContentCombinator;
    open spec fn view(&self) -> Self::V { SpecMsg4AnonContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg4AnonContentCombinator {
    type Type = Msg4AnonContent<'a>;
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
pub type Msg4AnonContentCombinatorAlias = Mapped<Msg4AnonContentCombinator1, Msg4AnonContentMapper>;


pub open spec fn spec_msg4_anon_content(i: u24) -> SpecMsg4AnonContentCombinator {
    SpecMsg4AnonContentCombinator(Mapped { inner: Choice(Cond { cond: i.spec_as_u32() == 1, inner: U16Le }, Cond { cond: !(i.spec_as_u32() == 1), inner: bytes::Tail }), mapper: Msg4AnonContentMapper })
}

pub fn msg4_anon_content<'a>(i: u24) -> (o: Msg4AnonContentCombinator)

    ensures o@ == spec_msg4_anon_content(i@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg4AnonContentCombinator(Mapped { inner: Msg4AnonContentCombinator1(Choice::new(Cond { cond: i.as_u32() == 1, inner: U16Le }, Cond { cond: !(i.as_u32() == 1), inner: bytes::Tail })), mapper: Msg4AnonContentMapper });
    // assert({
    //     &&& combinator@ == spec_msg4_anon_content(i@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg4_anon_content<'a>(input: &'a [u8], i: u24) -> (res: PResult<<Msg4AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_msg4_anon_content(i@).spec_parse(input@) == Some((n as int, v@)),
        spec_msg4_anon_content(i@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg4_anon_content(i@).spec_parse(input@) is None,
        spec_msg4_anon_content(i@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg4_anon_content( i );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg4_anon_content<'a>(v: <Msg4AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, i: u24) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg4_anon_content(i@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg4_anon_content(i@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg4_anon_content(i@).spec_serialize(v@))
        },
{
    let combinator = msg4_anon_content( i );
    combinator.serialize(v, data, pos)
}

pub fn msg4_anon_content_len<'a>(v: <Msg4AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, i: u24) -> (serialize_len: usize)
    requires
        spec_msg4_anon_content(i@).wf(v@),
        spec_msg4_anon_content(i@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_msg4_anon_content(i@).spec_serialize(v@).len(),
{
    let combinator = msg4_anon_content( i );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub type SpecHelloRetryRequest = u16;
pub type HelloRetryRequest = u16;
pub type HelloRetryRequestRef<'a> = &'a u16;


pub struct SpecHelloRetryRequestCombinator(pub SpecHelloRetryRequestCombinatorAlias);

impl SpecCombinator for SpecHelloRetryRequestCombinator {
    type Type = SpecHelloRetryRequest;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHelloRetryRequestCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecHelloRetryRequestCombinatorAlias::is_prefix_secure() }
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
pub type SpecHelloRetryRequestCombinatorAlias = U16Le;

pub struct HelloRetryRequestCombinator(pub HelloRetryRequestCombinatorAlias);

impl View for HelloRetryRequestCombinator {
    type V = SpecHelloRetryRequestCombinator;
    open spec fn view(&self) -> Self::V { SpecHelloRetryRequestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HelloRetryRequestCombinator {
    type Type = HelloRetryRequest;
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
pub type HelloRetryRequestCombinatorAlias = U16Le;


pub open spec fn spec_hello_retry_request() -> SpecHelloRetryRequestCombinator {
    SpecHelloRetryRequestCombinator(U16Le)
}

                
pub fn hello_retry_request<'a>() -> (o: HelloRetryRequestCombinator)
    ensures o@ == spec_hello_retry_request(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = HelloRetryRequestCombinator(U16Le);
    // assert({
    //     &&& combinator@ == spec_hello_retry_request()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_hello_retry_request<'a>(input: &'a [u8]) -> (res: PResult<<HelloRetryRequestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_hello_retry_request().spec_parse(input@) == Some((n as int, v@)),
        spec_hello_retry_request().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_hello_retry_request().spec_parse(input@) is None,
        spec_hello_retry_request().spec_parse(input@) is None ==> res is Err,
{
    let combinator = hello_retry_request();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_hello_retry_request<'a>(v: <HelloRetryRequestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_hello_retry_request().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_hello_retry_request().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_hello_retry_request().spec_serialize(v@))
        },
{
    let combinator = hello_retry_request();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn hello_retry_request_len<'a>(v: <HelloRetryRequestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_hello_retry_request().wf(v@),
        spec_hello_retry_request().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_hello_retry_request().spec_serialize(v@).len(),
{
    let combinator = hello_retry_request();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecServerHello = u32;
pub type ServerHello = u32;
pub type ServerHelloRef<'a> = &'a u32;


pub struct SpecServerHelloCombinator(pub SpecServerHelloCombinatorAlias);

impl SpecCombinator for SpecServerHelloCombinator {
    type Type = SpecServerHello;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecServerHelloCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecServerHelloCombinatorAlias::is_prefix_secure() }
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
pub type SpecServerHelloCombinatorAlias = U32Le;

pub struct ServerHelloCombinator(pub ServerHelloCombinatorAlias);

impl View for ServerHelloCombinator {
    type V = SpecServerHelloCombinator;
    open spec fn view(&self) -> Self::V { SpecServerHelloCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ServerHelloCombinator {
    type Type = ServerHello;
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
pub type ServerHelloCombinatorAlias = U32Le;


pub open spec fn spec_server_hello() -> SpecServerHelloCombinator {
    SpecServerHelloCombinator(U32Le)
}

                
pub fn server_hello<'a>() -> (o: ServerHelloCombinator)
    ensures o@ == spec_server_hello(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ServerHelloCombinator(U32Le);
    // assert({
    //     &&& combinator@ == spec_server_hello()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_server_hello<'a>(input: &'a [u8]) -> (res: PResult<<ServerHelloCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_server_hello().spec_parse(input@) == Some((n as int, v@)),
        spec_server_hello().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_server_hello().spec_parse(input@) is None,
        spec_server_hello().spec_parse(input@) is None ==> res is Err,
{
    let combinator = server_hello();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_server_hello<'a>(v: <ServerHelloCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_server_hello().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_server_hello().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_server_hello().spec_serialize(v@))
        },
{
    let combinator = server_hello();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn server_hello_len<'a>(v: <ServerHelloCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_server_hello().wf(v@),
        spec_server_hello().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_server_hello().spec_serialize(v@).len(),
{
    let combinator = server_hello();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecMsg1AnonPayload {
    Variant0(SpecHelloRetryRequest),
    Variant1(SpecServerHello),
}

pub type SpecMsg1AnonPayloadInner = Either<SpecHelloRetryRequest, SpecServerHello>;

impl SpecFrom<SpecMsg1AnonPayload> for SpecMsg1AnonPayloadInner {
    open spec fn spec_from(m: SpecMsg1AnonPayload) -> SpecMsg1AnonPayloadInner {
        match m {
            SpecMsg1AnonPayload::Variant0(m) => Either::Left(m),
            SpecMsg1AnonPayload::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecMsg1AnonPayloadInner> for SpecMsg1AnonPayload {
    open spec fn spec_from(m: SpecMsg1AnonPayloadInner) -> SpecMsg1AnonPayload {
        match m {
            Either::Left(m) => SpecMsg1AnonPayload::Variant0(m),
            Either::Right(m) => SpecMsg1AnonPayload::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg1AnonPayload {
    Variant0(HelloRetryRequest),
    Variant1(ServerHello),
}

pub type Msg1AnonPayloadInner = Either<HelloRetryRequest, ServerHello>;

pub type Msg1AnonPayloadInnerRef<'a> = Either<&'a HelloRetryRequest, &'a ServerHello>;


impl View for Msg1AnonPayload {
    type V = SpecMsg1AnonPayload;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg1AnonPayload::Variant0(m) => SpecMsg1AnonPayload::Variant0(m@),
            Msg1AnonPayload::Variant1(m) => SpecMsg1AnonPayload::Variant1(m@),
        }
    }
}


impl<'a> From<&'a Msg1AnonPayload> for Msg1AnonPayloadInnerRef<'a> {
    fn ex_from(m: &'a Msg1AnonPayload) -> Msg1AnonPayloadInnerRef<'a> {
        match m {
            Msg1AnonPayload::Variant0(m) => Either::Left(m),
            Msg1AnonPayload::Variant1(m) => Either::Right(m),
        }
    }

}

impl From<Msg1AnonPayloadInner> for Msg1AnonPayload {
    fn ex_from(m: Msg1AnonPayloadInner) -> Msg1AnonPayload {
        match m {
            Either::Left(m) => Msg1AnonPayload::Variant0(m),
            Either::Right(m) => Msg1AnonPayload::Variant1(m),
        }
    }
    
}


pub struct Msg1AnonPayloadMapper;
impl View for Msg1AnonPayloadMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg1AnonPayloadMapper {
    type Src = SpecMsg1AnonPayloadInner;
    type Dst = SpecMsg1AnonPayload;
}
impl SpecIsoProof for Msg1AnonPayloadMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg1AnonPayloadMapper {
    type Src = Msg1AnonPayloadInner;
    type Dst = Msg1AnonPayload;
    type RefSrc = Msg1AnonPayloadInnerRef<'a>;
}

type SpecMsg1AnonPayloadCombinatorAlias1 = Choice<Cond<SpecHelloRetryRequestCombinator>, Cond<SpecServerHelloCombinator>>;
pub struct SpecMsg1AnonPayloadCombinator(pub SpecMsg1AnonPayloadCombinatorAlias);

impl SpecCombinator for SpecMsg1AnonPayloadCombinator {
    type Type = SpecMsg1AnonPayload;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg1AnonPayloadCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsg1AnonPayloadCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg1AnonPayloadCombinatorAlias = Mapped<SpecMsg1AnonPayloadCombinatorAlias1, Msg1AnonPayloadMapper>;
type Msg1AnonPayloadCombinatorAlias1 = Choice<Cond<HelloRetryRequestCombinator>, Cond<ServerHelloCombinator>>;
pub struct Msg1AnonPayloadCombinator1(pub Msg1AnonPayloadCombinatorAlias1);
impl View for Msg1AnonPayloadCombinator1 {
    type V = SpecMsg1AnonPayloadCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg1AnonPayloadCombinator1, Msg1AnonPayloadCombinatorAlias1);

pub struct Msg1AnonPayloadCombinator(pub Msg1AnonPayloadCombinatorAlias);

impl View for Msg1AnonPayloadCombinator {
    type V = SpecMsg1AnonPayloadCombinator;
    open spec fn view(&self) -> Self::V { SpecMsg1AnonPayloadCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg1AnonPayloadCombinator {
    type Type = Msg1AnonPayload;
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
pub type Msg1AnonPayloadCombinatorAlias = Mapped<Msg1AnonPayloadCombinator1, Msg1AnonPayloadMapper>;


pub open spec fn spec_msg1_anon_payload(b: Seq<u8>) -> SpecMsg1AnonPayloadCombinator {
    SpecMsg1AnonPayloadCombinator(Mapped { inner: Choice(Cond { cond: b == seq![207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8], inner: spec_hello_retry_request() }, Cond { cond: !(b == seq![207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8]), inner: spec_server_hello() }), mapper: Msg1AnonPayloadMapper })
}

pub fn msg1_anon_payload<'a>(b: &'a [u8]) -> (o: Msg1AnonPayloadCombinator)

    ensures o@ == spec_msg1_anon_payload(b@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg1AnonPayloadCombinator(Mapped { inner: Msg1AnonPayloadCombinator1(Choice::new(Cond { cond: compare_slice(b, [207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8].as_slice()), inner: hello_retry_request() }, Cond { cond: !(compare_slice(b, [207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8].as_slice())), inner: server_hello() })), mapper: Msg1AnonPayloadMapper });
    // assert({
    //     &&& combinator@ == spec_msg1_anon_payload(b@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg1_anon_payload<'a>(input: &'a [u8], b: &'a [u8]) -> (res: PResult<<Msg1AnonPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_msg1_anon_payload(b@).spec_parse(input@) == Some((n as int, v@)),
        spec_msg1_anon_payload(b@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg1_anon_payload(b@).spec_parse(input@) is None,
        spec_msg1_anon_payload(b@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg1_anon_payload( b );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg1_anon_payload<'a>(v: <Msg1AnonPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, b: &'a [u8]) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg1_anon_payload(b@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg1_anon_payload(b@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg1_anon_payload(b@).spec_serialize(v@))
        },
{
    let combinator = msg1_anon_payload( b );
    combinator.serialize(v, data, pos)
}

pub fn msg1_anon_payload_len<'a>(v: <Msg1AnonPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, b: &'a [u8]) -> (serialize_len: usize)
    requires
        spec_msg1_anon_payload(b@).wf(v@),
        spec_msg1_anon_payload(b@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_msg1_anon_payload(b@).spec_serialize(v@).len(),
{
    let combinator = msg1_anon_payload( b );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecMsg1 {
    pub b: Seq<u8>,
    pub payload: SpecMsg1AnonPayload,
}

pub type SpecMsg1Inner = (Seq<u8>, SpecMsg1AnonPayload);


impl SpecFrom<SpecMsg1> for SpecMsg1Inner {
    open spec fn spec_from(m: SpecMsg1) -> SpecMsg1Inner {
        (m.b, m.payload)
    }
}

impl SpecFrom<SpecMsg1Inner> for SpecMsg1 {
    open spec fn spec_from(m: SpecMsg1Inner) -> SpecMsg1 {
        let (b, payload) = m;
        SpecMsg1 { b, payload }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg1<'a> {
    pub b: &'a [u8],
    pub payload: Msg1AnonPayload,
}

impl View for Msg1<'_> {
    type V = SpecMsg1;

    open spec fn view(&self) -> Self::V {
        SpecMsg1 {
            b: self.b@,
            payload: self.payload@,
        }
    }
}
pub type Msg1Inner<'a> = (&'a [u8], Msg1AnonPayload);

pub type Msg1InnerRef<'a> = (&'a &'a [u8], &'a Msg1AnonPayload);
impl<'a> From<&'a Msg1<'a>> for Msg1InnerRef<'a> {
    fn ex_from(m: &'a Msg1) -> Msg1InnerRef<'a> {
        (&m.b, &m.payload)
    }
}

impl<'a> From<Msg1Inner<'a>> for Msg1<'a> {
    fn ex_from(m: Msg1Inner) -> Msg1 {
        let (b, payload) = m;
        Msg1 { b, payload }
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

pub struct SpecMsg1Combinator(pub SpecMsg1CombinatorAlias);

impl SpecCombinator for SpecMsg1Combinator {
    type Type = SpecMsg1;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
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
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMsg1CombinatorAlias = Mapped<SpecPair<bytes::Fixed<32>, SpecMsg1AnonPayloadCombinator>, Msg1Mapper>;

pub struct Msg1Combinator(pub Msg1CombinatorAlias);

impl View for Msg1Combinator {
    type V = SpecMsg1Combinator;
    open spec fn view(&self) -> Self::V { SpecMsg1Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg1Combinator {
    type Type = Msg1<'a>;
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
pub type Msg1CombinatorAlias = Mapped<Pair<bytes::Fixed<32>, Msg1AnonPayloadCombinator, Msg1Cont0>, Msg1Mapper>;


pub open spec fn spec_msg1() -> SpecMsg1Combinator {
    SpecMsg1Combinator(
    Mapped {
        inner: Pair::spec_new(bytes::Fixed::<32>, |deps| spec_msg1_cont0(deps)),
        mapper: Msg1Mapper,
    })
}

pub open spec fn spec_msg1_cont0(deps: Seq<u8>) -> SpecMsg1AnonPayloadCombinator {
    let b = deps;
    spec_msg1_anon_payload(b)
}

impl View for Msg1Cont0 {
    type V = spec_fn(Seq<u8>) -> SpecMsg1AnonPayloadCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: Seq<u8>| {
            spec_msg1_cont0(deps)
        }
    }
}

                
pub fn msg1<'a>() -> (o: Msg1Combinator)
    ensures o@ == spec_msg1(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg1Combinator(
    Mapped {
        inner: Pair::new(bytes::Fixed::<32>, Msg1Cont0),
        mapper: Msg1Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_msg1()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
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

pub fn msg1_len<'a>(v: <Msg1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_msg1().wf(v@),
        spec_msg1().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_msg1().spec_serialize(v@).len(),
{
    let combinator = msg1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct Msg1Cont0;
type Msg1Cont0Type<'a, 'b> = &'b &'a [u8];
type Msg1Cont0SType<'a, 'x> = &'x &'a [u8];
type Msg1Cont0Input<'a, 'b, 'x> = POrSType<Msg1Cont0Type<'a, 'b>, Msg1Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg1Cont0Input<'a, 'b, 'x>> for Msg1Cont0 {
    type Output = Msg1AnonPayloadCombinator;

    open spec fn requires(&self, deps: Msg1Cont0Input<'a, 'b, 'x>) -> bool {
        &&& (bytes::Fixed::<32>).wf(deps@)
        }

    open spec fn ensures(&self, deps: Msg1Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_msg1_cont0(deps@)
    }

    fn apply(&self, deps: Msg1Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let b = deps;
                let b = *b;
                msg1_anon_payload(b)
            }
            POrSType::S(deps) => {
                let b = deps;
                let b = *b;
                msg1_anon_payload(b)
            }
        }
    }
}
                

pub enum SpecMsg2AnonContent {
    Variant0(u16),
    Variant1(u32),
}

pub type SpecMsg2AnonContentInner = Either<u16, u32>;

impl SpecFrom<SpecMsg2AnonContent> for SpecMsg2AnonContentInner {
    open spec fn spec_from(m: SpecMsg2AnonContent) -> SpecMsg2AnonContentInner {
        match m {
            SpecMsg2AnonContent::Variant0(m) => Either::Left(m),
            SpecMsg2AnonContent::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecMsg2AnonContentInner> for SpecMsg2AnonContent {
    open spec fn spec_from(m: SpecMsg2AnonContentInner) -> SpecMsg2AnonContent {
        match m {
            Either::Left(m) => SpecMsg2AnonContent::Variant0(m),
            Either::Right(m) => SpecMsg2AnonContent::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg2AnonContent {
    Variant0(u16),
    Variant1(u32),
}

pub type Msg2AnonContentInner = Either<u16, u32>;

pub type Msg2AnonContentInnerRef<'a> = Either<&'a u16, &'a u32>;


impl View for Msg2AnonContent {
    type V = SpecMsg2AnonContent;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg2AnonContent::Variant0(m) => SpecMsg2AnonContent::Variant0(m@),
            Msg2AnonContent::Variant1(m) => SpecMsg2AnonContent::Variant1(m@),
        }
    }
}


impl<'a> From<&'a Msg2AnonContent> for Msg2AnonContentInnerRef<'a> {
    fn ex_from(m: &'a Msg2AnonContent) -> Msg2AnonContentInnerRef<'a> {
        match m {
            Msg2AnonContent::Variant0(m) => Either::Left(m),
            Msg2AnonContent::Variant1(m) => Either::Right(m),
        }
    }

}

impl From<Msg2AnonContentInner> for Msg2AnonContent {
    fn ex_from(m: Msg2AnonContentInner) -> Msg2AnonContent {
        match m {
            Either::Left(m) => Msg2AnonContent::Variant0(m),
            Either::Right(m) => Msg2AnonContent::Variant1(m),
        }
    }
    
}


pub struct Msg2AnonContentMapper;
impl View for Msg2AnonContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg2AnonContentMapper {
    type Src = SpecMsg2AnonContentInner;
    type Dst = SpecMsg2AnonContent;
}
impl SpecIsoProof for Msg2AnonContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg2AnonContentMapper {
    type Src = Msg2AnonContentInner;
    type Dst = Msg2AnonContent;
    type RefSrc = Msg2AnonContentInnerRef<'a>;
}

type SpecMsg2AnonContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U32Le>>;
pub struct SpecMsg2AnonContentCombinator(pub SpecMsg2AnonContentCombinatorAlias);

impl SpecCombinator for SpecMsg2AnonContentCombinator {
    type Type = SpecMsg2AnonContent;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg2AnonContentCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsg2AnonContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg2AnonContentCombinatorAlias = Mapped<SpecMsg2AnonContentCombinatorAlias1, Msg2AnonContentMapper>;
type Msg2AnonContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U32Le>>;
pub struct Msg2AnonContentCombinator1(pub Msg2AnonContentCombinatorAlias1);
impl View for Msg2AnonContentCombinator1 {
    type V = SpecMsg2AnonContentCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg2AnonContentCombinator1, Msg2AnonContentCombinatorAlias1);

pub struct Msg2AnonContentCombinator(pub Msg2AnonContentCombinatorAlias);

impl View for Msg2AnonContentCombinator {
    type V = SpecMsg2AnonContentCombinator;
    open spec fn view(&self) -> Self::V { SpecMsg2AnonContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg2AnonContentCombinator {
    type Type = Msg2AnonContent;
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
pub type Msg2AnonContentCombinatorAlias = Mapped<Msg2AnonContentCombinator1, Msg2AnonContentMapper>;


pub open spec fn spec_msg2_anon_content(b: Seq<u8>) -> SpecMsg2AnonContentCombinator {
    SpecMsg2AnonContentCombinator(Mapped { inner: Choice(Cond { cond: b == seq![22u8, 3u8, 1u8], inner: U16Le }, Cond { cond: !(b == seq![22u8, 3u8, 1u8]), inner: U32Le }), mapper: Msg2AnonContentMapper })
}

pub fn msg2_anon_content<'a>(b: &'a [u8]) -> (o: Msg2AnonContentCombinator)

    ensures o@ == spec_msg2_anon_content(b@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg2AnonContentCombinator(Mapped { inner: Msg2AnonContentCombinator1(Choice::new(Cond { cond: compare_slice(b, [22u8, 3u8, 1u8].as_slice()), inner: U16Le }, Cond { cond: !(compare_slice(b, [22u8, 3u8, 1u8].as_slice())), inner: U32Le })), mapper: Msg2AnonContentMapper });
    // assert({
    //     &&& combinator@ == spec_msg2_anon_content(b@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg2_anon_content<'a>(input: &'a [u8], b: &'a [u8]) -> (res: PResult<<Msg2AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_msg2_anon_content(b@).spec_parse(input@) == Some((n as int, v@)),
        spec_msg2_anon_content(b@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg2_anon_content(b@).spec_parse(input@) is None,
        spec_msg2_anon_content(b@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg2_anon_content( b );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg2_anon_content<'a>(v: <Msg2AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, b: &'a [u8]) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg2_anon_content(b@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg2_anon_content(b@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg2_anon_content(b@).spec_serialize(v@))
        },
{
    let combinator = msg2_anon_content( b );
    combinator.serialize(v, data, pos)
}

pub fn msg2_anon_content_len<'a>(v: <Msg2AnonContentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, b: &'a [u8]) -> (serialize_len: usize)
    requires
        spec_msg2_anon_content(b@).wf(v@),
        spec_msg2_anon_content(b@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_msg2_anon_content(b@).spec_serialize(v@).len(),
{
    let combinator = msg2_anon_content( b );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecMsg2 {
    pub b: Seq<u8>,
    pub content: SpecMsg2AnonContent,
}

pub type SpecMsg2Inner = (Seq<u8>, SpecMsg2AnonContent);


impl SpecFrom<SpecMsg2> for SpecMsg2Inner {
    open spec fn spec_from(m: SpecMsg2) -> SpecMsg2Inner {
        (m.b, m.content)
    }
}

impl SpecFrom<SpecMsg2Inner> for SpecMsg2 {
    open spec fn spec_from(m: SpecMsg2Inner) -> SpecMsg2 {
        let (b, content) = m;
        SpecMsg2 { b, content }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg2<'a> {
    pub b: &'a [u8],
    pub content: Msg2AnonContent,
}

impl View for Msg2<'_> {
    type V = SpecMsg2;

    open spec fn view(&self) -> Self::V {
        SpecMsg2 {
            b: self.b@,
            content: self.content@,
        }
    }
}
pub type Msg2Inner<'a> = (&'a [u8], Msg2AnonContent);

pub type Msg2InnerRef<'a> = (&'a &'a [u8], &'a Msg2AnonContent);
impl<'a> From<&'a Msg2<'a>> for Msg2InnerRef<'a> {
    fn ex_from(m: &'a Msg2) -> Msg2InnerRef<'a> {
        (&m.b, &m.content)
    }
}

impl<'a> From<Msg2Inner<'a>> for Msg2<'a> {
    fn ex_from(m: Msg2Inner) -> Msg2 {
        let (b, content) = m;
        Msg2 { b, content }
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
    type Src = Msg2Inner<'a>;
    type Dst = Msg2<'a>;
    type RefSrc = Msg2InnerRef<'a>;
}

pub struct SpecMsg2Combinator(pub SpecMsg2CombinatorAlias);

impl SpecCombinator for SpecMsg2Combinator {
    type Type = SpecMsg2;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
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
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMsg2CombinatorAlias = Mapped<SpecPair<bytes::Fixed<3>, SpecMsg2AnonContentCombinator>, Msg2Mapper>;

pub struct Msg2Combinator(pub Msg2CombinatorAlias);

impl View for Msg2Combinator {
    type V = SpecMsg2Combinator;
    open spec fn view(&self) -> Self::V { SpecMsg2Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg2Combinator {
    type Type = Msg2<'a>;
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
pub type Msg2CombinatorAlias = Mapped<Pair<bytes::Fixed<3>, Msg2AnonContentCombinator, Msg2Cont0>, Msg2Mapper>;


pub open spec fn spec_msg2() -> SpecMsg2Combinator {
    SpecMsg2Combinator(
    Mapped {
        inner: Pair::spec_new(bytes::Fixed::<3>, |deps| spec_msg2_cont0(deps)),
        mapper: Msg2Mapper,
    })
}

pub open spec fn spec_msg2_cont0(deps: Seq<u8>) -> SpecMsg2AnonContentCombinator {
    let b = deps;
    spec_msg2_anon_content(b)
}

impl View for Msg2Cont0 {
    type V = spec_fn(Seq<u8>) -> SpecMsg2AnonContentCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: Seq<u8>| {
            spec_msg2_cont0(deps)
        }
    }
}

                
pub fn msg2<'a>() -> (o: Msg2Combinator)
    ensures o@ == spec_msg2(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg2Combinator(
    Mapped {
        inner: Pair::new(bytes::Fixed::<3>, Msg2Cont0),
        mapper: Msg2Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_msg2()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
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

pub fn msg2_len<'a>(v: <Msg2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_msg2().wf(v@),
        spec_msg2().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_msg2().spec_serialize(v@).len(),
{
    let combinator = msg2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct Msg2Cont0;
type Msg2Cont0Type<'a, 'b> = &'b &'a [u8];
type Msg2Cont0SType<'a, 'x> = &'x &'a [u8];
type Msg2Cont0Input<'a, 'b, 'x> = POrSType<Msg2Cont0Type<'a, 'b>, Msg2Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg2Cont0Input<'a, 'b, 'x>> for Msg2Cont0 {
    type Output = Msg2AnonContentCombinator;

    open spec fn requires(&self, deps: Msg2Cont0Input<'a, 'b, 'x>) -> bool {
        &&& (bytes::Fixed::<3>).wf(deps@)
        }

    open spec fn ensures(&self, deps: Msg2Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_msg2_cont0(deps@)
    }

    fn apply(&self, deps: Msg2Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let b = deps;
                let b = *b;
                msg2_anon_content(b)
            }
            POrSType::S(deps) => {
                let b = deps;
                let b = *b;
                msg2_anon_content(b)
            }
        }
    }
}
                

pub struct SpecMsg4 {
    pub i: u24,
    pub content: SpecMsg4AnonContent,
}

pub type SpecMsg4Inner = (u24, SpecMsg4AnonContent);


impl SpecFrom<SpecMsg4> for SpecMsg4Inner {
    open spec fn spec_from(m: SpecMsg4) -> SpecMsg4Inner {
        (m.i, m.content)
    }
}

impl SpecFrom<SpecMsg4Inner> for SpecMsg4 {
    open spec fn spec_from(m: SpecMsg4Inner) -> SpecMsg4 {
        let (i, content) = m;
        SpecMsg4 { i, content }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg4<'a> {
    pub i: u24,
    pub content: Msg4AnonContent<'a>,
}

impl View for Msg4<'_> {
    type V = SpecMsg4;

    open spec fn view(&self) -> Self::V {
        SpecMsg4 {
            i: self.i@,
            content: self.content@,
        }
    }
}
pub type Msg4Inner<'a> = (u24, Msg4AnonContent<'a>);

pub type Msg4InnerRef<'a> = (&'a u24, &'a Msg4AnonContent<'a>);
impl<'a> From<&'a Msg4<'a>> for Msg4InnerRef<'a> {
    fn ex_from(m: &'a Msg4) -> Msg4InnerRef<'a> {
        (&m.i, &m.content)
    }
}

impl<'a> From<Msg4Inner<'a>> for Msg4<'a> {
    fn ex_from(m: Msg4Inner) -> Msg4 {
        let (i, content) = m;
        Msg4 { i, content }
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

pub struct SpecMsg4Combinator(pub SpecMsg4CombinatorAlias);

impl SpecCombinator for SpecMsg4Combinator {
    type Type = SpecMsg4;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
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
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMsg4CombinatorAlias = Mapped<SpecPair<U24Le, SpecMsg4AnonContentCombinator>, Msg4Mapper>;

pub struct Msg4Combinator(pub Msg4CombinatorAlias);

impl View for Msg4Combinator {
    type V = SpecMsg4Combinator;
    open spec fn view(&self) -> Self::V { SpecMsg4Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg4Combinator {
    type Type = Msg4<'a>;
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
pub type Msg4CombinatorAlias = Mapped<Pair<U24Le, Msg4AnonContentCombinator, Msg4Cont0>, Msg4Mapper>;


pub open spec fn spec_msg4() -> SpecMsg4Combinator {
    SpecMsg4Combinator(
    Mapped {
        inner: Pair::spec_new(U24Le, |deps| spec_msg4_cont0(deps)),
        mapper: Msg4Mapper,
    })
}

pub open spec fn spec_msg4_cont0(deps: u24) -> SpecMsg4AnonContentCombinator {
    let i = deps;
    spec_msg4_anon_content(i)
}

impl View for Msg4Cont0 {
    type V = spec_fn(u24) -> SpecMsg4AnonContentCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u24| {
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
        inner: Pair::new(U24Le, Msg4Cont0),
        mapper: Msg4Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_msg4()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
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

pub fn msg4_len<'a>(v: <Msg4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_msg4().wf(v@),
        spec_msg4().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_msg4().spec_serialize(v@).len(),
{
    let combinator = msg4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct Msg4Cont0;
type Msg4Cont0Type<'a, 'b> = &'b u24;
type Msg4Cont0SType<'a, 'x> = &'x u24;
type Msg4Cont0Input<'a, 'b, 'x> = POrSType<Msg4Cont0Type<'a, 'b>, Msg4Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg4Cont0Input<'a, 'b, 'x>> for Msg4Cont0 {
    type Output = Msg4AnonContentCombinator;

    open spec fn requires(&self, deps: Msg4Cont0Input<'a, 'b, 'x>) -> bool {
        &&& (U24Le).wf(deps@)
        }

    open spec fn ensures(&self, deps: Msg4Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_msg4_cont0(deps@)
    }

    fn apply(&self, deps: Msg4Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let i = deps;
                let i = *i;
                msg4_anon_content(i)
            }
            POrSType::S(deps) => {
                let i = deps;
                let i = *i;
                msg4_anon_content(i)
            }
        }
    }
}
                

}
