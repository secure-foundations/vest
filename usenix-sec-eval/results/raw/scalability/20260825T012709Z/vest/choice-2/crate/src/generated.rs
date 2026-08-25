
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
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
            }
        } // verus!
    };
}
verus!{

pub enum SpecChoiceWidth2 {
    Variant0(u8),
    Variant1(u8),
}

pub type SpecChoiceWidth2Inner = Either<u8, u8>;

impl SpecFrom<SpecChoiceWidth2> for SpecChoiceWidth2Inner {
    open spec fn spec_from(m: SpecChoiceWidth2) -> SpecChoiceWidth2Inner {
        match m {
            SpecChoiceWidth2::Variant0(m) => Either::Left(m),
            SpecChoiceWidth2::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecChoiceWidth2Inner> for SpecChoiceWidth2 {
    open spec fn spec_from(m: SpecChoiceWidth2Inner) -> SpecChoiceWidth2 {
        match m {
            Either::Left(m) => SpecChoiceWidth2::Variant0(m),
            Either::Right(m) => SpecChoiceWidth2::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChoiceWidth2 {
    Variant0(u8),
    Variant1(u8),
}

pub type ChoiceWidth2Inner = Either<u8, u8>;

pub type ChoiceWidth2InnerRef<'a> = Either<&'a u8, &'a u8>;


impl View for ChoiceWidth2 {
    type V = SpecChoiceWidth2;
    open spec fn view(&self) -> Self::V {
        match self {
            ChoiceWidth2::Variant0(m) => SpecChoiceWidth2::Variant0(m@),
            ChoiceWidth2::Variant1(m) => SpecChoiceWidth2::Variant1(m@),
        }
    }
}


impl<'a> From<&'a ChoiceWidth2> for ChoiceWidth2InnerRef<'a> {
    fn ex_from(m: &'a ChoiceWidth2) -> ChoiceWidth2InnerRef<'a> {
        match m {
            ChoiceWidth2::Variant0(m) => Either::Left(m),
            ChoiceWidth2::Variant1(m) => Either::Right(m),
        }
    }

}

impl From<ChoiceWidth2Inner> for ChoiceWidth2 {
    fn ex_from(m: ChoiceWidth2Inner) -> ChoiceWidth2 {
        match m {
            Either::Left(m) => ChoiceWidth2::Variant0(m),
            Either::Right(m) => ChoiceWidth2::Variant1(m),
        }
    }
    
}


pub struct ChoiceWidth2Mapper;
impl View for ChoiceWidth2Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ChoiceWidth2Mapper {
    type Src = SpecChoiceWidth2Inner;
    type Dst = SpecChoiceWidth2;
}
impl SpecIsoProof for ChoiceWidth2Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ChoiceWidth2Mapper {
    type Src = ChoiceWidth2Inner;
    type Dst = ChoiceWidth2;
    type RefSrc = ChoiceWidth2InnerRef<'a>;
}

type SpecChoiceWidth2CombinatorAlias1 = Choice<Refined<U8, Predicate2576612288366319398>, Refined<U8, Predicate3768926651291043512>>;
pub struct SpecChoiceWidth2Combinator(pub SpecChoiceWidth2CombinatorAlias);

impl SpecCombinator for SpecChoiceWidth2Combinator {
    type Type = SpecChoiceWidth2;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecChoiceWidth2Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecChoiceWidth2CombinatorAlias::is_prefix_secure() }
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
pub type SpecChoiceWidth2CombinatorAlias = Mapped<SpecChoiceWidth2CombinatorAlias1, ChoiceWidth2Mapper>;
pub struct Predicate2576612288366319398;
impl View for Predicate2576612288366319398 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2576612288366319398 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0)
    }
}
impl SpecPred<u8> for Predicate2576612288366319398 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0)
    }
}
pub struct Predicate3768926651291043512;
impl View for Predicate3768926651291043512 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate3768926651291043512 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 1)
    }
}
impl SpecPred<u8> for Predicate3768926651291043512 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 1)
    }
}
type ChoiceWidth2CombinatorAlias1 = Choice<Refined<U8, Predicate2576612288366319398>, Refined<U8, Predicate3768926651291043512>>;
pub struct ChoiceWidth2Combinator1(pub ChoiceWidth2CombinatorAlias1);
impl View for ChoiceWidth2Combinator1 {
    type V = SpecChoiceWidth2CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth2Combinator1, ChoiceWidth2CombinatorAlias1);

pub struct ChoiceWidth2Combinator(pub ChoiceWidth2CombinatorAlias);

impl View for ChoiceWidth2Combinator {
    type V = SpecChoiceWidth2Combinator;
    open spec fn view(&self) -> Self::V { SpecChoiceWidth2Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ChoiceWidth2Combinator {
    type Type = ChoiceWidth2;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type ChoiceWidth2CombinatorAlias = Mapped<ChoiceWidth2Combinator1, ChoiceWidth2Mapper>;


pub open spec fn spec_choice_width2() -> SpecChoiceWidth2Combinator {
    SpecChoiceWidth2Combinator(Mapped { inner: Choice(Refined { inner: U8, predicate: Predicate2576612288366319398 }, Refined { inner: U8, predicate: Predicate3768926651291043512 }), mapper: ChoiceWidth2Mapper })
}

                
pub fn choice_width2<'a>() -> (o: ChoiceWidth2Combinator)
    ensures o@ == spec_choice_width2(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ChoiceWidth2Combinator(Mapped { inner: ChoiceWidth2Combinator1(Choice::new(Refined { inner: U8, predicate: Predicate2576612288366319398 }, Refined { inner: U8, predicate: Predicate3768926651291043512 })), mapper: ChoiceWidth2Mapper });
    // assert({
    //     &&& combinator@ == spec_choice_width2()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_choice_width2<'a>(input: &'a [u8]) -> (res: PResult<<ChoiceWidth2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_choice_width2().spec_parse(input@) == Some((n as int, v@)),
        spec_choice_width2().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_choice_width2().spec_parse(input@) is None,
        spec_choice_width2().spec_parse(input@) is None ==> res is Err,
{
    let combinator = choice_width2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_choice_width2<'a>(v: <ChoiceWidth2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_choice_width2().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_choice_width2().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_choice_width2().spec_serialize(v@))
        },
{
    let combinator = choice_width2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn choice_width2_len<'a>(v: <ChoiceWidth2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_choice_width2().wf(v@),
        spec_choice_width2().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_choice_width2().spec_serialize(v@).len(),
{
    let combinator = choice_width2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
