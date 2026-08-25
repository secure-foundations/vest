
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

pub enum SpecChoiceWidth8 {
    Variant0(u8),
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
    Variant4(u8),
    Variant5(u8),
    Variant6(u8),
    Variant7(u8),
}

pub type SpecChoiceWidth8Inner = Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, u8>>>>>>>;

impl SpecFrom<SpecChoiceWidth8> for SpecChoiceWidth8Inner {
    open spec fn spec_from(m: SpecChoiceWidth8) -> SpecChoiceWidth8Inner {
        match m {
            SpecChoiceWidth8::Variant0(m) => Either::Left(m),
            SpecChoiceWidth8::Variant1(m) => Either::Right(Either::Left(m)),
            SpecChoiceWidth8::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecChoiceWidth8::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecChoiceWidth8::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecChoiceWidth8::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecChoiceWidth8::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecChoiceWidth8::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))),
        }
    }

}

                
impl SpecFrom<SpecChoiceWidth8Inner> for SpecChoiceWidth8 {
    open spec fn spec_from(m: SpecChoiceWidth8Inner) -> SpecChoiceWidth8 {
        match m {
            Either::Left(m) => SpecChoiceWidth8::Variant0(m),
            Either::Right(Either::Left(m)) => SpecChoiceWidth8::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecChoiceWidth8::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecChoiceWidth8::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecChoiceWidth8::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecChoiceWidth8::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecChoiceWidth8::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))) => SpecChoiceWidth8::Variant7(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChoiceWidth8 {
    Variant0(u8),
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
    Variant4(u8),
    Variant5(u8),
    Variant6(u8),
    Variant7(u8),
}

pub type ChoiceWidth8Inner = Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, u8>>>>>>>;

pub type ChoiceWidth8InnerRef<'a> = Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, &'a u8>>>>>>>;


impl View for ChoiceWidth8 {
    type V = SpecChoiceWidth8;
    open spec fn view(&self) -> Self::V {
        match self {
            ChoiceWidth8::Variant0(m) => SpecChoiceWidth8::Variant0(m@),
            ChoiceWidth8::Variant1(m) => SpecChoiceWidth8::Variant1(m@),
            ChoiceWidth8::Variant2(m) => SpecChoiceWidth8::Variant2(m@),
            ChoiceWidth8::Variant3(m) => SpecChoiceWidth8::Variant3(m@),
            ChoiceWidth8::Variant4(m) => SpecChoiceWidth8::Variant4(m@),
            ChoiceWidth8::Variant5(m) => SpecChoiceWidth8::Variant5(m@),
            ChoiceWidth8::Variant6(m) => SpecChoiceWidth8::Variant6(m@),
            ChoiceWidth8::Variant7(m) => SpecChoiceWidth8::Variant7(m@),
        }
    }
}


impl<'a> From<&'a ChoiceWidth8> for ChoiceWidth8InnerRef<'a> {
    fn ex_from(m: &'a ChoiceWidth8) -> ChoiceWidth8InnerRef<'a> {
        match m {
            ChoiceWidth8::Variant0(m) => Either::Left(m),
            ChoiceWidth8::Variant1(m) => Either::Right(Either::Left(m)),
            ChoiceWidth8::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            ChoiceWidth8::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ChoiceWidth8::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ChoiceWidth8::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            ChoiceWidth8::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            ChoiceWidth8::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))),
        }
    }

}

impl From<ChoiceWidth8Inner> for ChoiceWidth8 {
    fn ex_from(m: ChoiceWidth8Inner) -> ChoiceWidth8 {
        match m {
            Either::Left(m) => ChoiceWidth8::Variant0(m),
            Either::Right(Either::Left(m)) => ChoiceWidth8::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => ChoiceWidth8::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => ChoiceWidth8::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => ChoiceWidth8::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => ChoiceWidth8::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => ChoiceWidth8::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))) => ChoiceWidth8::Variant7(m),
        }
    }
    
}


pub struct ChoiceWidth8Mapper;
impl View for ChoiceWidth8Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ChoiceWidth8Mapper {
    type Src = SpecChoiceWidth8Inner;
    type Dst = SpecChoiceWidth8;
}
impl SpecIsoProof for ChoiceWidth8Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ChoiceWidth8Mapper {
    type Src = ChoiceWidth8Inner;
    type Dst = ChoiceWidth8;
    type RefSrc = ChoiceWidth8InnerRef<'a>;
}

type SpecChoiceWidth8CombinatorAlias1 = Choice<Refined<U8, Predicate4214186895105241400>, Refined<U8, Predicate18163385058579063098>>;
type SpecChoiceWidth8CombinatorAlias2 = Choice<Refined<U8, Predicate9186325526105272194>, SpecChoiceWidth8CombinatorAlias1>;
type SpecChoiceWidth8CombinatorAlias3 = Choice<Refined<U8, Predicate4589101901519479956>, SpecChoiceWidth8CombinatorAlias2>;
type SpecChoiceWidth8CombinatorAlias4 = Choice<Refined<U8, Predicate2671570727481267254>, SpecChoiceWidth8CombinatorAlias3>;
type SpecChoiceWidth8CombinatorAlias5 = Choice<Refined<U8, Predicate6170912057263668010>, SpecChoiceWidth8CombinatorAlias4>;
type SpecChoiceWidth8CombinatorAlias6 = Choice<Refined<U8, Predicate13385608959756530935>, SpecChoiceWidth8CombinatorAlias5>;
type SpecChoiceWidth8CombinatorAlias7 = Choice<Refined<U8, Predicate2576612288366319398>, SpecChoiceWidth8CombinatorAlias6>;
pub struct SpecChoiceWidth8Combinator(pub SpecChoiceWidth8CombinatorAlias);

impl SpecCombinator for SpecChoiceWidth8Combinator {
    type Type = SpecChoiceWidth8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecChoiceWidth8Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecChoiceWidth8CombinatorAlias::is_prefix_secure() }
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
pub type SpecChoiceWidth8CombinatorAlias = Mapped<SpecChoiceWidth8CombinatorAlias7, ChoiceWidth8Mapper>;
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
pub struct Predicate13385608959756530935;
impl View for Predicate13385608959756530935 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate13385608959756530935 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 1)
    }
}
impl SpecPred<u8> for Predicate13385608959756530935 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 1)
    }
}
pub struct Predicate6170912057263668010;
impl View for Predicate6170912057263668010 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate6170912057263668010 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 2)
    }
}
impl SpecPred<u8> for Predicate6170912057263668010 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 2)
    }
}
pub struct Predicate2671570727481267254;
impl View for Predicate2671570727481267254 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2671570727481267254 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 3)
    }
}
impl SpecPred<u8> for Predicate2671570727481267254 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 3)
    }
}
pub struct Predicate4589101901519479956;
impl View for Predicate4589101901519479956 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate4589101901519479956 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 4)
    }
}
impl SpecPred<u8> for Predicate4589101901519479956 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 4)
    }
}
pub struct Predicate9186325526105272194;
impl View for Predicate9186325526105272194 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate9186325526105272194 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 5)
    }
}
impl SpecPred<u8> for Predicate9186325526105272194 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 5)
    }
}
pub struct Predicate4214186895105241400;
impl View for Predicate4214186895105241400 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate4214186895105241400 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 6)
    }
}
impl SpecPred<u8> for Predicate4214186895105241400 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 6)
    }
}
pub struct Predicate18163385058579063098;
impl View for Predicate18163385058579063098 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate18163385058579063098 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 7)
    }
}
impl SpecPred<u8> for Predicate18163385058579063098 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 7)
    }
}
type ChoiceWidth8CombinatorAlias1 = Choice<Refined<U8, Predicate4214186895105241400>, Refined<U8, Predicate18163385058579063098>>;
type ChoiceWidth8CombinatorAlias2 = Choice<Refined<U8, Predicate9186325526105272194>, ChoiceWidth8Combinator1>;
type ChoiceWidth8CombinatorAlias3 = Choice<Refined<U8, Predicate4589101901519479956>, ChoiceWidth8Combinator2>;
type ChoiceWidth8CombinatorAlias4 = Choice<Refined<U8, Predicate2671570727481267254>, ChoiceWidth8Combinator3>;
type ChoiceWidth8CombinatorAlias5 = Choice<Refined<U8, Predicate6170912057263668010>, ChoiceWidth8Combinator4>;
type ChoiceWidth8CombinatorAlias6 = Choice<Refined<U8, Predicate13385608959756530935>, ChoiceWidth8Combinator5>;
type ChoiceWidth8CombinatorAlias7 = Choice<Refined<U8, Predicate2576612288366319398>, ChoiceWidth8Combinator6>;
pub struct ChoiceWidth8Combinator1(pub ChoiceWidth8CombinatorAlias1);
impl View for ChoiceWidth8Combinator1 {
    type V = SpecChoiceWidth8CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth8Combinator1, ChoiceWidth8CombinatorAlias1);

pub struct ChoiceWidth8Combinator2(pub ChoiceWidth8CombinatorAlias2);
impl View for ChoiceWidth8Combinator2 {
    type V = SpecChoiceWidth8CombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth8Combinator2, ChoiceWidth8CombinatorAlias2);

pub struct ChoiceWidth8Combinator3(pub ChoiceWidth8CombinatorAlias3);
impl View for ChoiceWidth8Combinator3 {
    type V = SpecChoiceWidth8CombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth8Combinator3, ChoiceWidth8CombinatorAlias3);

pub struct ChoiceWidth8Combinator4(pub ChoiceWidth8CombinatorAlias4);
impl View for ChoiceWidth8Combinator4 {
    type V = SpecChoiceWidth8CombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth8Combinator4, ChoiceWidth8CombinatorAlias4);

pub struct ChoiceWidth8Combinator5(pub ChoiceWidth8CombinatorAlias5);
impl View for ChoiceWidth8Combinator5 {
    type V = SpecChoiceWidth8CombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth8Combinator5, ChoiceWidth8CombinatorAlias5);

pub struct ChoiceWidth8Combinator6(pub ChoiceWidth8CombinatorAlias6);
impl View for ChoiceWidth8Combinator6 {
    type V = SpecChoiceWidth8CombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth8Combinator6, ChoiceWidth8CombinatorAlias6);

pub struct ChoiceWidth8Combinator7(pub ChoiceWidth8CombinatorAlias7);
impl View for ChoiceWidth8Combinator7 {
    type V = SpecChoiceWidth8CombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth8Combinator7, ChoiceWidth8CombinatorAlias7);

pub struct ChoiceWidth8Combinator(pub ChoiceWidth8CombinatorAlias);

impl View for ChoiceWidth8Combinator {
    type V = SpecChoiceWidth8Combinator;
    open spec fn view(&self) -> Self::V { SpecChoiceWidth8Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ChoiceWidth8Combinator {
    type Type = ChoiceWidth8;
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
pub type ChoiceWidth8CombinatorAlias = Mapped<ChoiceWidth8Combinator7, ChoiceWidth8Mapper>;


pub open spec fn spec_choice_width8() -> SpecChoiceWidth8Combinator {
    SpecChoiceWidth8Combinator(Mapped { inner: Choice(Refined { inner: U8, predicate: Predicate2576612288366319398 }, Choice(Refined { inner: U8, predicate: Predicate13385608959756530935 }, Choice(Refined { inner: U8, predicate: Predicate6170912057263668010 }, Choice(Refined { inner: U8, predicate: Predicate2671570727481267254 }, Choice(Refined { inner: U8, predicate: Predicate4589101901519479956 }, Choice(Refined { inner: U8, predicate: Predicate9186325526105272194 }, Choice(Refined { inner: U8, predicate: Predicate4214186895105241400 }, Refined { inner: U8, predicate: Predicate18163385058579063098 }))))))), mapper: ChoiceWidth8Mapper })
}

                
pub fn choice_width8<'a>() -> (o: ChoiceWidth8Combinator)
    ensures o@ == spec_choice_width8(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ChoiceWidth8Combinator(Mapped { inner: ChoiceWidth8Combinator7(Choice::new(Refined { inner: U8, predicate: Predicate2576612288366319398 }, ChoiceWidth8Combinator6(Choice::new(Refined { inner: U8, predicate: Predicate13385608959756530935 }, ChoiceWidth8Combinator5(Choice::new(Refined { inner: U8, predicate: Predicate6170912057263668010 }, ChoiceWidth8Combinator4(Choice::new(Refined { inner: U8, predicate: Predicate2671570727481267254 }, ChoiceWidth8Combinator3(Choice::new(Refined { inner: U8, predicate: Predicate4589101901519479956 }, ChoiceWidth8Combinator2(Choice::new(Refined { inner: U8, predicate: Predicate9186325526105272194 }, ChoiceWidth8Combinator1(Choice::new(Refined { inner: U8, predicate: Predicate4214186895105241400 }, Refined { inner: U8, predicate: Predicate18163385058579063098 })))))))))))))), mapper: ChoiceWidth8Mapper });
    // assert({
    //     &&& combinator@ == spec_choice_width8()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_choice_width8<'a>(input: &'a [u8]) -> (res: PResult<<ChoiceWidth8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_choice_width8().spec_parse(input@) == Some((n as int, v@)),
        spec_choice_width8().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_choice_width8().spec_parse(input@) is None,
        spec_choice_width8().spec_parse(input@) is None ==> res is Err,
{
    let combinator = choice_width8();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_choice_width8<'a>(v: <ChoiceWidth8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_choice_width8().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_choice_width8().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_choice_width8().spec_serialize(v@))
        },
{
    let combinator = choice_width8();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn choice_width8_len<'a>(v: <ChoiceWidth8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_choice_width8().wf(v@),
        spec_choice_width8().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_choice_width8().spec_serialize(v@).len(),
{
    let combinator = choice_width8();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
