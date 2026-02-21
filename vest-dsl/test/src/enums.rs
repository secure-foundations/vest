
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

pub enum SpecATypedChoose {
    X(u8),
    Y(u16),
    Z(u32),
}

pub type SpecATypedChooseInner = Either<u8, Either<u16, u32>>;

impl SpecFrom<SpecATypedChoose> for SpecATypedChooseInner {
    open spec fn spec_from(m: SpecATypedChoose) -> SpecATypedChooseInner {
        match m {
            SpecATypedChoose::X(m) => Either::Left(m),
            SpecATypedChoose::Y(m) => Either::Right(Either::Left(m)),
            SpecATypedChoose::Z(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecATypedChooseInner> for SpecATypedChoose {
    open spec fn spec_from(m: SpecATypedChooseInner) -> SpecATypedChoose {
        match m {
            Either::Left(m) => SpecATypedChoose::X(m),
            Either::Right(Either::Left(m)) => SpecATypedChoose::Y(m),
            Either::Right(Either::Right(m)) => SpecATypedChoose::Z(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ATypedChoose {
    X(u8),
    Y(u16),
    Z(u32),
}

pub type ATypedChooseInner = Either<u8, Either<u16, u32>>;

pub type ATypedChooseInnerRef<'a> = Either<&'a u8, Either<&'a u16, &'a u32>>;


impl View for ATypedChoose {
    type V = SpecATypedChoose;
    open spec fn view(&self) -> Self::V {
        match self {
            ATypedChoose::X(m) => SpecATypedChoose::X(m@),
            ATypedChoose::Y(m) => SpecATypedChoose::Y(m@),
            ATypedChoose::Z(m) => SpecATypedChoose::Z(m@),
        }
    }
}


impl<'a> From<&'a ATypedChoose> for ATypedChooseInnerRef<'a> {
    fn ex_from(m: &'a ATypedChoose) -> ATypedChooseInnerRef<'a> {
        match m {
            ATypedChoose::X(m) => Either::Left(m),
            ATypedChoose::Y(m) => Either::Right(Either::Left(m)),
            ATypedChoose::Z(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl From<ATypedChooseInner> for ATypedChoose {
    fn ex_from(m: ATypedChooseInner) -> ATypedChoose {
        match m {
            Either::Left(m) => ATypedChoose::X(m),
            Either::Right(Either::Left(m)) => ATypedChoose::Y(m),
            Either::Right(Either::Right(m)) => ATypedChoose::Z(m),
        }
    }
    
}


pub struct ATypedChooseMapper;
impl View for ATypedChooseMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ATypedChooseMapper {
    type Src = SpecATypedChooseInner;
    type Dst = SpecATypedChoose;
}
impl SpecIsoProof for ATypedChooseMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ATypedChooseMapper {
    type Src = ATypedChooseInner;
    type Dst = ATypedChoose;
    type RefSrc = ATypedChooseInnerRef<'a>;
}

type SpecATypedChooseCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U32Le>>;
type SpecATypedChooseCombinatorAlias2 = Choice<Cond<U8>, SpecATypedChooseCombinatorAlias1>;
pub struct SpecATypedChooseCombinator(pub SpecATypedChooseCombinatorAlias);

impl SpecCombinator for SpecATypedChooseCombinator {
    type Type = SpecATypedChoose;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecATypedChooseCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecATypedChooseCombinatorAlias::is_prefix_secure() }
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
pub type SpecATypedChooseCombinatorAlias = Mapped<SpecATypedChooseCombinatorAlias2, ATypedChooseMapper>;
type ATypedChooseCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U32Le>>;
type ATypedChooseCombinatorAlias2 = Choice<Cond<U8>, ATypedChooseCombinator1>;
pub struct ATypedChooseCombinator1(pub ATypedChooseCombinatorAlias1);
impl View for ATypedChooseCombinator1 {
    type V = SpecATypedChooseCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ATypedChooseCombinator1, ATypedChooseCombinatorAlias1);

pub struct ATypedChooseCombinator2(pub ATypedChooseCombinatorAlias2);
impl View for ATypedChooseCombinator2 {
    type V = SpecATypedChooseCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ATypedChooseCombinator2, ATypedChooseCombinatorAlias2);

pub struct ATypedChooseCombinator(pub ATypedChooseCombinatorAlias);

impl View for ATypedChooseCombinator {
    type V = SpecATypedChooseCombinator;
    open spec fn view(&self) -> Self::V { SpecATypedChooseCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ATypedChooseCombinator {
    type Type = ATypedChoose;
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
pub type ATypedChooseCombinatorAlias = Mapped<ATypedChooseCombinator2, ATypedChooseMapper>;


pub open spec fn spec_a_typed_choose(e: SpecATypedClosedEnum) -> SpecATypedChooseCombinator {
    SpecATypedChooseCombinator(Mapped { inner: Choice(Cond { cond: e == ATypedClosedEnum::X, inner: U8 }, Choice(Cond { cond: e == ATypedClosedEnum::Y, inner: U16Le }, Cond { cond: e == ATypedClosedEnum::Z, inner: U32Le })), mapper: ATypedChooseMapper })
}

pub fn a_typed_choose<'a>(e: ATypedClosedEnum) -> (o: ATypedChooseCombinator)
    ensures o@ == spec_a_typed_choose(e@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ATypedChooseCombinator(Mapped { inner: ATypedChooseCombinator2(Choice::new(Cond { cond: e == ATypedClosedEnum::X, inner: U8 }, ATypedChooseCombinator1(Choice::new(Cond { cond: e == ATypedClosedEnum::Y, inner: U16Le }, Cond { cond: e == ATypedClosedEnum::Z, inner: U32Le })))), mapper: ATypedChooseMapper });
    // assert({
    //     &&& combinator@ == spec_a_typed_choose(e@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_a_typed_choose<'a>(input: &'a [u8], e: ATypedClosedEnum) -> (res: PResult<<ATypedChooseCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_typed_choose(e@).spec_parse(input@) == Some((n as int, v@)),
        spec_a_typed_choose(e@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_typed_choose(e@).spec_parse(input@) is None,
        spec_a_typed_choose(e@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_typed_choose( e );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_typed_choose<'a>(v: <ATypedChooseCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, e: ATypedClosedEnum) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_typed_choose(e@).wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_typed_choose(e@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_typed_choose(e@).spec_serialize(v@))
        },
{
    let combinator = a_typed_choose( e );
    combinator.serialize(v, data, pos)
}

pub fn a_typed_choose_len<'a>(v: <ATypedChooseCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, e: ATypedClosedEnum) -> (serialize_len: usize)
    requires
        spec_a_typed_choose(e@).wf(v@),
        spec_a_typed_choose(e@).spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_a_typed_choose(e@).spec_serialize(v@).len(),
{
    let combinator = a_typed_choose( e );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub mod ATypedOpenEnum {
    use super::*;
    pub spec const SPEC_P: u32 = 0;
    pub spec const SPEC_Q: u32 = 1;
    pub spec const SPEC_R: u32 = 2;
    pub exec const P: u32 ensures P == SPEC_P { 0 }
    pub exec const Q: u32 ensures Q == SPEC_Q { 1 }
    pub exec const R: u32 ensures R == SPEC_R { 2 }
}


pub struct SpecATypedOpenEnumCombinator(pub SpecATypedOpenEnumCombinatorAlias);

impl SpecCombinator for SpecATypedOpenEnumCombinator {
    type Type = u32;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecATypedOpenEnumCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecATypedOpenEnumCombinatorAlias::is_prefix_secure() }
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
pub type SpecATypedOpenEnumCombinatorAlias = U32Le;

pub struct ATypedOpenEnumCombinator(pub ATypedOpenEnumCombinatorAlias);

impl View for ATypedOpenEnumCombinator {
    type V = SpecATypedOpenEnumCombinator;
    open spec fn view(&self) -> Self::V { SpecATypedOpenEnumCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ATypedOpenEnumCombinator {
    type Type = u32;
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
pub type ATypedOpenEnumCombinatorAlias = U32Le;


pub open spec fn spec_a_typed_open_enum() -> SpecATypedOpenEnumCombinator {
    SpecATypedOpenEnumCombinator(U32Le)
}

                
pub fn a_typed_open_enum<'a>() -> (o: ATypedOpenEnumCombinator)
    ensures o@ == spec_a_typed_open_enum(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ATypedOpenEnumCombinator(U32Le);
    // assert({
    //     &&& combinator@ == spec_a_typed_open_enum()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_a_typed_open_enum<'a>(input: &'a [u8]) -> (res: PResult<<ATypedOpenEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_typed_open_enum().spec_parse(input@) == Some((n as int, v@)),
        spec_a_typed_open_enum().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_typed_open_enum().spec_parse(input@) is None,
        spec_a_typed_open_enum().spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_typed_open_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_typed_open_enum<'a>(v: <ATypedOpenEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_typed_open_enum().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_typed_open_enum().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_typed_open_enum().spec_serialize(v@))
        },
{
    let combinator = a_typed_open_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn a_typed_open_enum_len<'a>(v: <ATypedOpenEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_a_typed_open_enum().wf(v@),
        spec_a_typed_open_enum().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_a_typed_open_enum().spec_serialize(v@).len(),
{
    let combinator = a_typed_open_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecANonDependentChoose {
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
}

pub type SpecANonDependentChooseInner = Either<u8, Either<u8, u8>>;

impl SpecFrom<SpecANonDependentChoose> for SpecANonDependentChooseInner {
    open spec fn spec_from(m: SpecANonDependentChoose) -> SpecANonDependentChooseInner {
        match m {
            SpecANonDependentChoose::Variant1(m) => Either::Left(m),
            SpecANonDependentChoose::Variant2(m) => Either::Right(Either::Left(m)),
            SpecANonDependentChoose::Variant3(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecANonDependentChooseInner> for SpecANonDependentChoose {
    open spec fn spec_from(m: SpecANonDependentChooseInner) -> SpecANonDependentChoose {
        match m {
            Either::Left(m) => SpecANonDependentChoose::Variant1(m),
            Either::Right(Either::Left(m)) => SpecANonDependentChoose::Variant2(m),
            Either::Right(Either::Right(m)) => SpecANonDependentChoose::Variant3(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ANonDependentChoose {
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
}

pub type ANonDependentChooseInner = Either<u8, Either<u8, u8>>;

pub type ANonDependentChooseInnerRef<'a> = Either<&'a u8, Either<&'a u8, &'a u8>>;


impl View for ANonDependentChoose {
    type V = SpecANonDependentChoose;
    open spec fn view(&self) -> Self::V {
        match self {
            ANonDependentChoose::Variant1(m) => SpecANonDependentChoose::Variant1(m@),
            ANonDependentChoose::Variant2(m) => SpecANonDependentChoose::Variant2(m@),
            ANonDependentChoose::Variant3(m) => SpecANonDependentChoose::Variant3(m@),
        }
    }
}


impl<'a> From<&'a ANonDependentChoose> for ANonDependentChooseInnerRef<'a> {
    fn ex_from(m: &'a ANonDependentChoose) -> ANonDependentChooseInnerRef<'a> {
        match m {
            ANonDependentChoose::Variant1(m) => Either::Left(m),
            ANonDependentChoose::Variant2(m) => Either::Right(Either::Left(m)),
            ANonDependentChoose::Variant3(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl From<ANonDependentChooseInner> for ANonDependentChoose {
    fn ex_from(m: ANonDependentChooseInner) -> ANonDependentChoose {
        match m {
            Either::Left(m) => ANonDependentChoose::Variant1(m),
            Either::Right(Either::Left(m)) => ANonDependentChoose::Variant2(m),
            Either::Right(Either::Right(m)) => ANonDependentChoose::Variant3(m),
        }
    }
    
}


pub struct ANonDependentChooseMapper;
impl View for ANonDependentChooseMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ANonDependentChooseMapper {
    type Src = SpecANonDependentChooseInner;
    type Dst = SpecANonDependentChoose;
}
impl SpecIsoProof for ANonDependentChooseMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ANonDependentChooseMapper {
    type Src = ANonDependentChooseInner;
    type Dst = ANonDependentChoose;
    type RefSrc = ANonDependentChooseInnerRef<'a>;
}

type SpecANonDependentChooseCombinatorAlias1 = Choice<Refined<U8, Predicate3779459584691363859>, Refined<U8, Predicate16013864750610309580>>;
type SpecANonDependentChooseCombinatorAlias2 = Choice<Refined<U8, Predicate8434700403445569729>, SpecANonDependentChooseCombinatorAlias1>;
pub struct SpecANonDependentChooseCombinator(pub SpecANonDependentChooseCombinatorAlias);

impl SpecCombinator for SpecANonDependentChooseCombinator {
    type Type = SpecANonDependentChoose;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecANonDependentChooseCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecANonDependentChooseCombinatorAlias::is_prefix_secure() }
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
pub type SpecANonDependentChooseCombinatorAlias = Mapped<SpecANonDependentChooseCombinatorAlias2, ANonDependentChooseMapper>;
pub struct Predicate8434700403445569729;
impl View for Predicate8434700403445569729 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate8434700403445569729 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 0 && i <= 10)
    }
}
impl SpecPred<u8> for Predicate8434700403445569729 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 0 && i <= 10)
    }
}
pub struct Predicate3779459584691363859;
impl View for Predicate3779459584691363859 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate3779459584691363859 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 11 && i <= 20)
    }
}
impl SpecPred<u8> for Predicate3779459584691363859 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 11 && i <= 20)
    }
}
pub struct Predicate16013864750610309580;
impl View for Predicate16013864750610309580 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate16013864750610309580 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 21)
    }
}
impl SpecPred<u8> for Predicate16013864750610309580 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 21)
    }
}
type ANonDependentChooseCombinatorAlias1 = Choice<Refined<U8, Predicate3779459584691363859>, Refined<U8, Predicate16013864750610309580>>;
type ANonDependentChooseCombinatorAlias2 = Choice<Refined<U8, Predicate8434700403445569729>, ANonDependentChooseCombinator1>;
pub struct ANonDependentChooseCombinator1(pub ANonDependentChooseCombinatorAlias1);
impl View for ANonDependentChooseCombinator1 {
    type V = SpecANonDependentChooseCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ANonDependentChooseCombinator1, ANonDependentChooseCombinatorAlias1);

pub struct ANonDependentChooseCombinator2(pub ANonDependentChooseCombinatorAlias2);
impl View for ANonDependentChooseCombinator2 {
    type V = SpecANonDependentChooseCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ANonDependentChooseCombinator2, ANonDependentChooseCombinatorAlias2);

pub struct ANonDependentChooseCombinator(pub ANonDependentChooseCombinatorAlias);

impl View for ANonDependentChooseCombinator {
    type V = SpecANonDependentChooseCombinator;
    open spec fn view(&self) -> Self::V { SpecANonDependentChooseCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ANonDependentChooseCombinator {
    type Type = ANonDependentChoose;
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
pub type ANonDependentChooseCombinatorAlias = Mapped<ANonDependentChooseCombinator2, ANonDependentChooseMapper>;


pub open spec fn spec_a_non_dependent_choose() -> SpecANonDependentChooseCombinator {
    SpecANonDependentChooseCombinator(Mapped { inner: Choice(Refined { inner: U8, predicate: Predicate8434700403445569729 }, Choice(Refined { inner: U8, predicate: Predicate3779459584691363859 }, Refined { inner: U8, predicate: Predicate16013864750610309580 })), mapper: ANonDependentChooseMapper })
}

                
pub fn a_non_dependent_choose<'a>() -> (o: ANonDependentChooseCombinator)
    ensures o@ == spec_a_non_dependent_choose(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ANonDependentChooseCombinator(Mapped { inner: ANonDependentChooseCombinator2(Choice::new(Refined { inner: U8, predicate: Predicate8434700403445569729 }, ANonDependentChooseCombinator1(Choice::new(Refined { inner: U8, predicate: Predicate3779459584691363859 }, Refined { inner: U8, predicate: Predicate16013864750610309580 })))), mapper: ANonDependentChooseMapper });
    // assert({
    //     &&& combinator@ == spec_a_non_dependent_choose()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_a_non_dependent_choose<'a>(input: &'a [u8]) -> (res: PResult<<ANonDependentChooseCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_non_dependent_choose().spec_parse(input@) == Some((n as int, v@)),
        spec_a_non_dependent_choose().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_non_dependent_choose().spec_parse(input@) is None,
        spec_a_non_dependent_choose().spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_non_dependent_choose();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_non_dependent_choose<'a>(v: <ANonDependentChooseCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_non_dependent_choose().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_non_dependent_choose().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_non_dependent_choose().spec_serialize(v@))
        },
{
    let combinator = a_non_dependent_choose();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn a_non_dependent_choose_len<'a>(v: <ANonDependentChooseCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_a_non_dependent_choose().wf(v@),
        spec_a_non_dependent_choose().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_a_non_dependent_choose().spec_serialize(v@).len(),
{
    let combinator = a_non_dependent_choose();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecARegularChoose {
    A(u8),
    B(u16),
    C(u32),
}

pub type SpecARegularChooseInner = Either<u8, Either<u16, u32>>;

impl SpecFrom<SpecARegularChoose> for SpecARegularChooseInner {
    open spec fn spec_from(m: SpecARegularChoose) -> SpecARegularChooseInner {
        match m {
            SpecARegularChoose::A(m) => Either::Left(m),
            SpecARegularChoose::B(m) => Either::Right(Either::Left(m)),
            SpecARegularChoose::C(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecARegularChooseInner> for SpecARegularChoose {
    open spec fn spec_from(m: SpecARegularChooseInner) -> SpecARegularChoose {
        match m {
            Either::Left(m) => SpecARegularChoose::A(m),
            Either::Right(Either::Left(m)) => SpecARegularChoose::B(m),
            Either::Right(Either::Right(m)) => SpecARegularChoose::C(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ARegularChoose {
    A(u8),
    B(u16),
    C(u32),
}

pub type ARegularChooseInner = Either<u8, Either<u16, u32>>;

pub type ARegularChooseInnerRef<'a> = Either<&'a u8, Either<&'a u16, &'a u32>>;


impl View for ARegularChoose {
    type V = SpecARegularChoose;
    open spec fn view(&self) -> Self::V {
        match self {
            ARegularChoose::A(m) => SpecARegularChoose::A(m@),
            ARegularChoose::B(m) => SpecARegularChoose::B(m@),
            ARegularChoose::C(m) => SpecARegularChoose::C(m@),
        }
    }
}


impl<'a> From<&'a ARegularChoose> for ARegularChooseInnerRef<'a> {
    fn ex_from(m: &'a ARegularChoose) -> ARegularChooseInnerRef<'a> {
        match m {
            ARegularChoose::A(m) => Either::Left(m),
            ARegularChoose::B(m) => Either::Right(Either::Left(m)),
            ARegularChoose::C(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl From<ARegularChooseInner> for ARegularChoose {
    fn ex_from(m: ARegularChooseInner) -> ARegularChoose {
        match m {
            Either::Left(m) => ARegularChoose::A(m),
            Either::Right(Either::Left(m)) => ARegularChoose::B(m),
            Either::Right(Either::Right(m)) => ARegularChoose::C(m),
        }
    }
    
}


pub struct ARegularChooseMapper;
impl View for ARegularChooseMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ARegularChooseMapper {
    type Src = SpecARegularChooseInner;
    type Dst = SpecARegularChoose;
}
impl SpecIsoProof for ARegularChooseMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ARegularChooseMapper {
    type Src = ARegularChooseInner;
    type Dst = ARegularChoose;
    type RefSrc = ARegularChooseInnerRef<'a>;
}

type SpecARegularChooseCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U32Le>>;
type SpecARegularChooseCombinatorAlias2 = Choice<Cond<U8>, SpecARegularChooseCombinatorAlias1>;
pub struct SpecARegularChooseCombinator(pub SpecARegularChooseCombinatorAlias);

impl SpecCombinator for SpecARegularChooseCombinator {
    type Type = SpecARegularChoose;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecARegularChooseCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecARegularChooseCombinatorAlias::is_prefix_secure() }
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
pub type SpecARegularChooseCombinatorAlias = Mapped<SpecARegularChooseCombinatorAlias2, ARegularChooseMapper>;
type ARegularChooseCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U32Le>>;
type ARegularChooseCombinatorAlias2 = Choice<Cond<U8>, ARegularChooseCombinator1>;
pub struct ARegularChooseCombinator1(pub ARegularChooseCombinatorAlias1);
impl View for ARegularChooseCombinator1 {
    type V = SpecARegularChooseCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ARegularChooseCombinator1, ARegularChooseCombinatorAlias1);

pub struct ARegularChooseCombinator2(pub ARegularChooseCombinatorAlias2);
impl View for ARegularChooseCombinator2 {
    type V = SpecARegularChooseCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ARegularChooseCombinator2, ARegularChooseCombinatorAlias2);

pub struct ARegularChooseCombinator(pub ARegularChooseCombinatorAlias);

impl View for ARegularChooseCombinator {
    type V = SpecARegularChooseCombinator;
    open spec fn view(&self) -> Self::V { SpecARegularChooseCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ARegularChooseCombinator {
    type Type = ARegularChoose;
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
pub type ARegularChooseCombinatorAlias = Mapped<ARegularChooseCombinator2, ARegularChooseMapper>;


pub open spec fn spec_a_regular_choose(e: SpecAClosedEnum) -> SpecARegularChooseCombinator {
    SpecARegularChooseCombinator(Mapped { inner: Choice(Cond { cond: e == AClosedEnum::A, inner: U8 }, Choice(Cond { cond: e == AClosedEnum::B, inner: U16Le }, Cond { cond: e == AClosedEnum::C, inner: U32Le })), mapper: ARegularChooseMapper })
}

pub fn a_regular_choose<'a>(e: AClosedEnum) -> (o: ARegularChooseCombinator)
    ensures o@ == spec_a_regular_choose(e@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ARegularChooseCombinator(Mapped { inner: ARegularChooseCombinator2(Choice::new(Cond { cond: e == AClosedEnum::A, inner: U8 }, ARegularChooseCombinator1(Choice::new(Cond { cond: e == AClosedEnum::B, inner: U16Le }, Cond { cond: e == AClosedEnum::C, inner: U32Le })))), mapper: ARegularChooseMapper });
    // assert({
    //     &&& combinator@ == spec_a_regular_choose(e@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_a_regular_choose<'a>(input: &'a [u8], e: AClosedEnum) -> (res: PResult<<ARegularChooseCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_regular_choose(e@).spec_parse(input@) == Some((n as int, v@)),
        spec_a_regular_choose(e@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_regular_choose(e@).spec_parse(input@) is None,
        spec_a_regular_choose(e@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_regular_choose( e );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_regular_choose<'a>(v: <ARegularChooseCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, e: AClosedEnum) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_regular_choose(e@).wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_regular_choose(e@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_regular_choose(e@).spec_serialize(v@))
        },
{
    let combinator = a_regular_choose( e );
    combinator.serialize(v, data, pos)
}

pub fn a_regular_choose_len<'a>(v: <ARegularChooseCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, e: AClosedEnum) -> (serialize_len: usize)
    requires
        spec_a_regular_choose(e@).wf(v@),
        spec_a_regular_choose(e@).spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_a_regular_choose(e@).spec_serialize(v@).len(),
{
    let combinator = a_regular_choose( e );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub spec const SPEC_AMixedTypedEnum_M: u8 = 0;
pub spec const SPEC_AMixedTypedEnum_N: u8 = 1;
pub spec const SPEC_AMixedTypedEnum_O: u8 = 2;
pub exec static EXEC_AMixedTypedEnum_M: u8 ensures EXEC_AMixedTypedEnum_M == SPEC_AMixedTypedEnum_M { 0 }
pub exec static EXEC_AMixedTypedEnum_N: u8 ensures EXEC_AMixedTypedEnum_N == SPEC_AMixedTypedEnum_N { 1 }
pub exec static EXEC_AMixedTypedEnum_O: u8 ensures EXEC_AMixedTypedEnum_O == SPEC_AMixedTypedEnum_O { 2 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AMixedTypedEnum {
    M = 0,
N = 1,
O = 2
}
pub type SpecAMixedTypedEnum = AMixedTypedEnum;

pub type AMixedTypedEnumInner = u8;

pub type AMixedTypedEnumInnerRef<'a> = &'a u8;

impl View for AMixedTypedEnum {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<AMixedTypedEnumInner> for AMixedTypedEnum {
    type Error = ();

    open spec fn spec_try_from(v: AMixedTypedEnumInner) -> Result<AMixedTypedEnum, ()> {
        match v {
            0u8 => Ok(AMixedTypedEnum::M),
            1u8 => Ok(AMixedTypedEnum::N),
            2u8 => Ok(AMixedTypedEnum::O),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AMixedTypedEnum> for AMixedTypedEnumInner {
    type Error = ();

    open spec fn spec_try_from(v: AMixedTypedEnum) -> Result<AMixedTypedEnumInner, ()> {
        match v {
            AMixedTypedEnum::M => Ok(SPEC_AMixedTypedEnum_M),
            AMixedTypedEnum::N => Ok(SPEC_AMixedTypedEnum_N),
            AMixedTypedEnum::O => Ok(SPEC_AMixedTypedEnum_O),
        }
    }
}

impl TryFrom<AMixedTypedEnumInner> for AMixedTypedEnum {
    type Error = ();

    fn ex_try_from(v: AMixedTypedEnumInner) -> Result<AMixedTypedEnum, ()> {
        match v {
            0u8 => Ok(AMixedTypedEnum::M),
            1u8 => Ok(AMixedTypedEnum::N),
            2u8 => Ok(AMixedTypedEnum::O),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a AMixedTypedEnum> for AMixedTypedEnumInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a AMixedTypedEnum) -> Result<AMixedTypedEnumInnerRef<'a>, ()> {
        match v {
            AMixedTypedEnum::M => Ok(&EXEC_AMixedTypedEnum_M),
            AMixedTypedEnum::N => Ok(&EXEC_AMixedTypedEnum_N),
            AMixedTypedEnum::O => Ok(&EXEC_AMixedTypedEnum_O),
        }
    }
}

pub struct AMixedTypedEnumMapper;

impl View for AMixedTypedEnumMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for AMixedTypedEnumMapper {
    type Src = AMixedTypedEnumInner;
    type Dst = AMixedTypedEnum;
}

impl SpecPartialIsoProof for AMixedTypedEnumMapper {
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

impl<'a> PartialIso<'a> for AMixedTypedEnumMapper {
    type Src = AMixedTypedEnumInner;
    type Dst = AMixedTypedEnum;
    type RefSrc = AMixedTypedEnumInnerRef<'a>;
}


pub struct SpecAMixedTypedEnumCombinator(pub SpecAMixedTypedEnumCombinatorAlias);

impl SpecCombinator for SpecAMixedTypedEnumCombinator {
    type Type = SpecAMixedTypedEnum;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAMixedTypedEnumCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecAMixedTypedEnumCombinatorAlias::is_prefix_secure() }
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
pub type SpecAMixedTypedEnumCombinatorAlias = TryMap<U8, AMixedTypedEnumMapper>;

pub struct AMixedTypedEnumCombinator(pub AMixedTypedEnumCombinatorAlias);

impl View for AMixedTypedEnumCombinator {
    type V = SpecAMixedTypedEnumCombinator;
    open spec fn view(&self) -> Self::V { SpecAMixedTypedEnumCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AMixedTypedEnumCombinator {
    type Type = AMixedTypedEnum;
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
pub type AMixedTypedEnumCombinatorAlias = TryMap<U8, AMixedTypedEnumMapper>;


pub open spec fn spec_a_mixed_typed_enum() -> SpecAMixedTypedEnumCombinator {
    SpecAMixedTypedEnumCombinator(TryMap { inner: U8, mapper: AMixedTypedEnumMapper })
}

                
pub fn a_mixed_typed_enum<'a>() -> (o: AMixedTypedEnumCombinator)
    ensures o@ == spec_a_mixed_typed_enum(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = AMixedTypedEnumCombinator(TryMap { inner: U8, mapper: AMixedTypedEnumMapper });
    // assert({
    //     &&& combinator@ == spec_a_mixed_typed_enum()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_a_mixed_typed_enum<'a>(input: &'a [u8]) -> (res: PResult<<AMixedTypedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_mixed_typed_enum().spec_parse(input@) == Some((n as int, v@)),
        spec_a_mixed_typed_enum().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_mixed_typed_enum().spec_parse(input@) is None,
        spec_a_mixed_typed_enum().spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_mixed_typed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_mixed_typed_enum<'a>(v: <AMixedTypedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_mixed_typed_enum().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_mixed_typed_enum().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_mixed_typed_enum().spec_serialize(v@))
        },
{
    let combinator = a_mixed_typed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn a_mixed_typed_enum_len<'a>(v: <AMixedTypedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_a_mixed_typed_enum().wf(v@),
        spec_a_mixed_typed_enum().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_a_mixed_typed_enum().spec_serialize(v@).len(),
{
    let combinator = a_mixed_typed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub spec const SPEC_AClosedEnum_A: u8 = 0;
pub spec const SPEC_AClosedEnum_B: u8 = 1;
pub spec const SPEC_AClosedEnum_C: u8 = 2;
pub exec static EXEC_AClosedEnum_A: u8 ensures EXEC_AClosedEnum_A == SPEC_AClosedEnum_A { 0 }
pub exec static EXEC_AClosedEnum_B: u8 ensures EXEC_AClosedEnum_B == SPEC_AClosedEnum_B { 1 }
pub exec static EXEC_AClosedEnum_C: u8 ensures EXEC_AClosedEnum_C == SPEC_AClosedEnum_C { 2 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AClosedEnum {
    A = 0,
B = 1,
C = 2
}
pub type SpecAClosedEnum = AClosedEnum;

pub type AClosedEnumInner = u8;

pub type AClosedEnumInnerRef<'a> = &'a u8;

impl View for AClosedEnum {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<AClosedEnumInner> for AClosedEnum {
    type Error = ();

    open spec fn spec_try_from(v: AClosedEnumInner) -> Result<AClosedEnum, ()> {
        match v {
            0u8 => Ok(AClosedEnum::A),
            1u8 => Ok(AClosedEnum::B),
            2u8 => Ok(AClosedEnum::C),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AClosedEnum> for AClosedEnumInner {
    type Error = ();

    open spec fn spec_try_from(v: AClosedEnum) -> Result<AClosedEnumInner, ()> {
        match v {
            AClosedEnum::A => Ok(SPEC_AClosedEnum_A),
            AClosedEnum::B => Ok(SPEC_AClosedEnum_B),
            AClosedEnum::C => Ok(SPEC_AClosedEnum_C),
        }
    }
}

impl TryFrom<AClosedEnumInner> for AClosedEnum {
    type Error = ();

    fn ex_try_from(v: AClosedEnumInner) -> Result<AClosedEnum, ()> {
        match v {
            0u8 => Ok(AClosedEnum::A),
            1u8 => Ok(AClosedEnum::B),
            2u8 => Ok(AClosedEnum::C),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a AClosedEnum> for AClosedEnumInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a AClosedEnum) -> Result<AClosedEnumInnerRef<'a>, ()> {
        match v {
            AClosedEnum::A => Ok(&EXEC_AClosedEnum_A),
            AClosedEnum::B => Ok(&EXEC_AClosedEnum_B),
            AClosedEnum::C => Ok(&EXEC_AClosedEnum_C),
        }
    }
}

pub struct AClosedEnumMapper;

impl View for AClosedEnumMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for AClosedEnumMapper {
    type Src = AClosedEnumInner;
    type Dst = AClosedEnum;
}

impl SpecPartialIsoProof for AClosedEnumMapper {
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

impl<'a> PartialIso<'a> for AClosedEnumMapper {
    type Src = AClosedEnumInner;
    type Dst = AClosedEnum;
    type RefSrc = AClosedEnumInnerRef<'a>;
}


pub struct SpecAClosedEnumCombinator(pub SpecAClosedEnumCombinatorAlias);

impl SpecCombinator for SpecAClosedEnumCombinator {
    type Type = SpecAClosedEnum;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAClosedEnumCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecAClosedEnumCombinatorAlias::is_prefix_secure() }
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
pub type SpecAClosedEnumCombinatorAlias = TryMap<U8, AClosedEnumMapper>;

pub struct AClosedEnumCombinator(pub AClosedEnumCombinatorAlias);

impl View for AClosedEnumCombinator {
    type V = SpecAClosedEnumCombinator;
    open spec fn view(&self) -> Self::V { SpecAClosedEnumCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AClosedEnumCombinator {
    type Type = AClosedEnum;
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
pub type AClosedEnumCombinatorAlias = TryMap<U8, AClosedEnumMapper>;


pub open spec fn spec_a_closed_enum() -> SpecAClosedEnumCombinator {
    SpecAClosedEnumCombinator(TryMap { inner: U8, mapper: AClosedEnumMapper })
}

                
pub fn a_closed_enum<'a>() -> (o: AClosedEnumCombinator)
    ensures o@ == spec_a_closed_enum(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = AClosedEnumCombinator(TryMap { inner: U8, mapper: AClosedEnumMapper });
    // assert({
    //     &&& combinator@ == spec_a_closed_enum()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_a_closed_enum<'a>(input: &'a [u8]) -> (res: PResult<<AClosedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_closed_enum().spec_parse(input@) == Some((n as int, v@)),
        spec_a_closed_enum().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_closed_enum().spec_parse(input@) is None,
        spec_a_closed_enum().spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_closed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_closed_enum<'a>(v: <AClosedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_closed_enum().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_closed_enum().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_closed_enum().spec_serialize(v@))
        },
{
    let combinator = a_closed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn a_closed_enum_len<'a>(v: <AClosedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_a_closed_enum().wf(v@),
        spec_a_closed_enum().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_a_closed_enum().spec_serialize(v@).len(),
{
    let combinator = a_closed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub spec const SPEC_ATypedClosedEnum_X: u16 = 0;
pub spec const SPEC_ATypedClosedEnum_Y: u16 = 1;
pub spec const SPEC_ATypedClosedEnum_Z: u16 = 2;
pub exec static EXEC_ATypedClosedEnum_X: u16 ensures EXEC_ATypedClosedEnum_X == SPEC_ATypedClosedEnum_X { 0 }
pub exec static EXEC_ATypedClosedEnum_Y: u16 ensures EXEC_ATypedClosedEnum_Y == SPEC_ATypedClosedEnum_Y { 1 }
pub exec static EXEC_ATypedClosedEnum_Z: u16 ensures EXEC_ATypedClosedEnum_Z == SPEC_ATypedClosedEnum_Z { 2 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum ATypedClosedEnum {
    X = 0,
Y = 1,
Z = 2
}
pub type SpecATypedClosedEnum = ATypedClosedEnum;

pub type ATypedClosedEnumInner = u16;

pub type ATypedClosedEnumInnerRef<'a> = &'a u16;

impl View for ATypedClosedEnum {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<ATypedClosedEnumInner> for ATypedClosedEnum {
    type Error = ();

    open spec fn spec_try_from(v: ATypedClosedEnumInner) -> Result<ATypedClosedEnum, ()> {
        match v {
            0u16 => Ok(ATypedClosedEnum::X),
            1u16 => Ok(ATypedClosedEnum::Y),
            2u16 => Ok(ATypedClosedEnum::Z),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<ATypedClosedEnum> for ATypedClosedEnumInner {
    type Error = ();

    open spec fn spec_try_from(v: ATypedClosedEnum) -> Result<ATypedClosedEnumInner, ()> {
        match v {
            ATypedClosedEnum::X => Ok(SPEC_ATypedClosedEnum_X),
            ATypedClosedEnum::Y => Ok(SPEC_ATypedClosedEnum_Y),
            ATypedClosedEnum::Z => Ok(SPEC_ATypedClosedEnum_Z),
        }
    }
}

impl TryFrom<ATypedClosedEnumInner> for ATypedClosedEnum {
    type Error = ();

    fn ex_try_from(v: ATypedClosedEnumInner) -> Result<ATypedClosedEnum, ()> {
        match v {
            0u16 => Ok(ATypedClosedEnum::X),
            1u16 => Ok(ATypedClosedEnum::Y),
            2u16 => Ok(ATypedClosedEnum::Z),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a ATypedClosedEnum> for ATypedClosedEnumInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a ATypedClosedEnum) -> Result<ATypedClosedEnumInnerRef<'a>, ()> {
        match v {
            ATypedClosedEnum::X => Ok(&EXEC_ATypedClosedEnum_X),
            ATypedClosedEnum::Y => Ok(&EXEC_ATypedClosedEnum_Y),
            ATypedClosedEnum::Z => Ok(&EXEC_ATypedClosedEnum_Z),
        }
    }
}

pub struct ATypedClosedEnumMapper;

impl View for ATypedClosedEnumMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for ATypedClosedEnumMapper {
    type Src = ATypedClosedEnumInner;
    type Dst = ATypedClosedEnum;
}

impl SpecPartialIsoProof for ATypedClosedEnumMapper {
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

impl<'a> PartialIso<'a> for ATypedClosedEnumMapper {
    type Src = ATypedClosedEnumInner;
    type Dst = ATypedClosedEnum;
    type RefSrc = ATypedClosedEnumInnerRef<'a>;
}


pub struct SpecATypedClosedEnumCombinator(pub SpecATypedClosedEnumCombinatorAlias);

impl SpecCombinator for SpecATypedClosedEnumCombinator {
    type Type = SpecATypedClosedEnum;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecATypedClosedEnumCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecATypedClosedEnumCombinatorAlias::is_prefix_secure() }
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
pub type SpecATypedClosedEnumCombinatorAlias = TryMap<U16Le, ATypedClosedEnumMapper>;

pub struct ATypedClosedEnumCombinator(pub ATypedClosedEnumCombinatorAlias);

impl View for ATypedClosedEnumCombinator {
    type V = SpecATypedClosedEnumCombinator;
    open spec fn view(&self) -> Self::V { SpecATypedClosedEnumCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ATypedClosedEnumCombinator {
    type Type = ATypedClosedEnum;
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
pub type ATypedClosedEnumCombinatorAlias = TryMap<U16Le, ATypedClosedEnumMapper>;


pub open spec fn spec_a_typed_closed_enum() -> SpecATypedClosedEnumCombinator {
    SpecATypedClosedEnumCombinator(TryMap { inner: U16Le, mapper: ATypedClosedEnumMapper })
}

                
pub fn a_typed_closed_enum<'a>() -> (o: ATypedClosedEnumCombinator)
    ensures o@ == spec_a_typed_closed_enum(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ATypedClosedEnumCombinator(TryMap { inner: U16Le, mapper: ATypedClosedEnumMapper });
    // assert({
    //     &&& combinator@ == spec_a_typed_closed_enum()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_a_typed_closed_enum<'a>(input: &'a [u8]) -> (res: PResult<<ATypedClosedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_typed_closed_enum().spec_parse(input@) == Some((n as int, v@)),
        spec_a_typed_closed_enum().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_typed_closed_enum().spec_parse(input@) is None,
        spec_a_typed_closed_enum().spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_typed_closed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_typed_closed_enum<'a>(v: <ATypedClosedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_typed_closed_enum().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_typed_closed_enum().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_typed_closed_enum().spec_serialize(v@))
        },
{
    let combinator = a_typed_closed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn a_typed_closed_enum_len<'a>(v: <ATypedClosedEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_a_typed_closed_enum().wf(v@),
        spec_a_typed_closed_enum().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_a_typed_closed_enum().spec_serialize(v@).len(),
{
    let combinator = a_typed_closed_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod AnOpenEnum {
    use super::*;
    pub spec const SPEC_A: u8 = 0;
    pub spec const SPEC_B: u8 = 1;
    pub spec const SPEC_C: u8 = 2;
    pub exec const A: u8 ensures A == SPEC_A { 0 }
    pub exec const B: u8 ensures B == SPEC_B { 1 }
    pub exec const C: u8 ensures C == SPEC_C { 2 }
}


pub struct SpecAnOpenEnumCombinator(pub SpecAnOpenEnumCombinatorAlias);

impl SpecCombinator for SpecAnOpenEnumCombinator {
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
impl SecureSpecCombinator for SpecAnOpenEnumCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecAnOpenEnumCombinatorAlias::is_prefix_secure() }
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
pub type SpecAnOpenEnumCombinatorAlias = U8;

pub struct AnOpenEnumCombinator(pub AnOpenEnumCombinatorAlias);

impl View for AnOpenEnumCombinator {
    type V = SpecAnOpenEnumCombinator;
    open spec fn view(&self) -> Self::V { SpecAnOpenEnumCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AnOpenEnumCombinator {
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
pub type AnOpenEnumCombinatorAlias = U8;


pub open spec fn spec_an_open_enum() -> SpecAnOpenEnumCombinator {
    SpecAnOpenEnumCombinator(U8)
}

                
pub fn an_open_enum<'a>() -> (o: AnOpenEnumCombinator)
    ensures o@ == spec_an_open_enum(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = AnOpenEnumCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_an_open_enum()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_an_open_enum<'a>(input: &'a [u8]) -> (res: PResult<<AnOpenEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_an_open_enum().spec_parse(input@) == Some((n as int, v@)),
        spec_an_open_enum().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_an_open_enum().spec_parse(input@) is None,
        spec_an_open_enum().spec_parse(input@) is None ==> res is Err,
{
    let combinator = an_open_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_an_open_enum<'a>(v: <AnOpenEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_an_open_enum().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_an_open_enum().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_an_open_enum().spec_serialize(v@))
        },
{
    let combinator = an_open_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn an_open_enum_len<'a>(v: <AnOpenEnumCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_an_open_enum().wf(v@),
        spec_an_open_enum().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_an_open_enum().spec_serialize(v@).len(),
{
    let combinator = an_open_enum();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecATypedChooseWithDefault {
    P(u8),
    Q(u16),
    R(u32),
    Unrecognized(Seq<u8>),
}

pub type SpecATypedChooseWithDefaultInner = Either<u8, Either<u16, Either<u32, Seq<u8>>>>;

impl SpecFrom<SpecATypedChooseWithDefault> for SpecATypedChooseWithDefaultInner {
    open spec fn spec_from(m: SpecATypedChooseWithDefault) -> SpecATypedChooseWithDefaultInner {
        match m {
            SpecATypedChooseWithDefault::P(m) => Either::Left(m),
            SpecATypedChooseWithDefault::Q(m) => Either::Right(Either::Left(m)),
            SpecATypedChooseWithDefault::R(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecATypedChooseWithDefault::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

                
impl SpecFrom<SpecATypedChooseWithDefaultInner> for SpecATypedChooseWithDefault {
    open spec fn spec_from(m: SpecATypedChooseWithDefaultInner) -> SpecATypedChooseWithDefault {
        match m {
            Either::Left(m) => SpecATypedChooseWithDefault::P(m),
            Either::Right(Either::Left(m)) => SpecATypedChooseWithDefault::Q(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecATypedChooseWithDefault::R(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecATypedChooseWithDefault::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ATypedChooseWithDefault<'a> {
    P(u8),
    Q(u16),
    R(u32),
    Unrecognized(&'a [u8]),
}

pub type ATypedChooseWithDefaultInner<'a> = Either<u8, Either<u16, Either<u32, &'a [u8]>>>;

pub type ATypedChooseWithDefaultInnerRef<'a> = Either<&'a u8, Either<&'a u16, Either<&'a u32, &'a &'a [u8]>>>;


impl<'a> View for ATypedChooseWithDefault<'a> {
    type V = SpecATypedChooseWithDefault;
    open spec fn view(&self) -> Self::V {
        match self {
            ATypedChooseWithDefault::P(m) => SpecATypedChooseWithDefault::P(m@),
            ATypedChooseWithDefault::Q(m) => SpecATypedChooseWithDefault::Q(m@),
            ATypedChooseWithDefault::R(m) => SpecATypedChooseWithDefault::R(m@),
            ATypedChooseWithDefault::Unrecognized(m) => SpecATypedChooseWithDefault::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a ATypedChooseWithDefault<'a>> for ATypedChooseWithDefaultInnerRef<'a> {
    fn ex_from(m: &'a ATypedChooseWithDefault<'a>) -> ATypedChooseWithDefaultInnerRef<'a> {
        match m {
            ATypedChooseWithDefault::P(m) => Either::Left(m),
            ATypedChooseWithDefault::Q(m) => Either::Right(Either::Left(m)),
            ATypedChooseWithDefault::R(m) => Either::Right(Either::Right(Either::Left(m))),
            ATypedChooseWithDefault::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl<'a> From<ATypedChooseWithDefaultInner<'a>> for ATypedChooseWithDefault<'a> {
    fn ex_from(m: ATypedChooseWithDefaultInner<'a>) -> ATypedChooseWithDefault<'a> {
        match m {
            Either::Left(m) => ATypedChooseWithDefault::P(m),
            Either::Right(Either::Left(m)) => ATypedChooseWithDefault::Q(m),
            Either::Right(Either::Right(Either::Left(m))) => ATypedChooseWithDefault::R(m),
            Either::Right(Either::Right(Either::Right(m))) => ATypedChooseWithDefault::Unrecognized(m),
        }
    }
    
}


pub struct ATypedChooseWithDefaultMapper;
impl View for ATypedChooseWithDefaultMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ATypedChooseWithDefaultMapper {
    type Src = SpecATypedChooseWithDefaultInner;
    type Dst = SpecATypedChooseWithDefault;
}
impl SpecIsoProof for ATypedChooseWithDefaultMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ATypedChooseWithDefaultMapper {
    type Src = ATypedChooseWithDefaultInner<'a>;
    type Dst = ATypedChooseWithDefault<'a>;
    type RefSrc = ATypedChooseWithDefaultInnerRef<'a>;
}

type SpecATypedChooseWithDefaultCombinatorAlias1 = Choice<Cond<U32Le>, Cond<bytes::Tail>>;
type SpecATypedChooseWithDefaultCombinatorAlias2 = Choice<Cond<U16Le>, SpecATypedChooseWithDefaultCombinatorAlias1>;
type SpecATypedChooseWithDefaultCombinatorAlias3 = Choice<Cond<U8>, SpecATypedChooseWithDefaultCombinatorAlias2>;
pub struct SpecATypedChooseWithDefaultCombinator(pub SpecATypedChooseWithDefaultCombinatorAlias);

impl SpecCombinator for SpecATypedChooseWithDefaultCombinator {
    type Type = SpecATypedChooseWithDefault;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecATypedChooseWithDefaultCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecATypedChooseWithDefaultCombinatorAlias::is_prefix_secure() }
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
pub type SpecATypedChooseWithDefaultCombinatorAlias = Mapped<SpecATypedChooseWithDefaultCombinatorAlias3, ATypedChooseWithDefaultMapper>;
type ATypedChooseWithDefaultCombinatorAlias1 = Choice<Cond<U32Le>, Cond<bytes::Tail>>;
type ATypedChooseWithDefaultCombinatorAlias2 = Choice<Cond<U16Le>, ATypedChooseWithDefaultCombinator1>;
type ATypedChooseWithDefaultCombinatorAlias3 = Choice<Cond<U8>, ATypedChooseWithDefaultCombinator2>;
pub struct ATypedChooseWithDefaultCombinator1(pub ATypedChooseWithDefaultCombinatorAlias1);
impl View for ATypedChooseWithDefaultCombinator1 {
    type V = SpecATypedChooseWithDefaultCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ATypedChooseWithDefaultCombinator1, ATypedChooseWithDefaultCombinatorAlias1);

pub struct ATypedChooseWithDefaultCombinator2(pub ATypedChooseWithDefaultCombinatorAlias2);
impl View for ATypedChooseWithDefaultCombinator2 {
    type V = SpecATypedChooseWithDefaultCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ATypedChooseWithDefaultCombinator2, ATypedChooseWithDefaultCombinatorAlias2);

pub struct ATypedChooseWithDefaultCombinator3(pub ATypedChooseWithDefaultCombinatorAlias3);
impl View for ATypedChooseWithDefaultCombinator3 {
    type V = SpecATypedChooseWithDefaultCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ATypedChooseWithDefaultCombinator3, ATypedChooseWithDefaultCombinatorAlias3);

pub struct ATypedChooseWithDefaultCombinator(pub ATypedChooseWithDefaultCombinatorAlias);

impl View for ATypedChooseWithDefaultCombinator {
    type V = SpecATypedChooseWithDefaultCombinator;
    open spec fn view(&self) -> Self::V { SpecATypedChooseWithDefaultCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ATypedChooseWithDefaultCombinator {
    type Type = ATypedChooseWithDefault<'a>;
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
pub type ATypedChooseWithDefaultCombinatorAlias = Mapped<ATypedChooseWithDefaultCombinator3, ATypedChooseWithDefaultMapper>;


pub open spec fn spec_a_typed_choose_with_default(e: u32) -> SpecATypedChooseWithDefaultCombinator {
    SpecATypedChooseWithDefaultCombinator(Mapped { inner: Choice(Cond { cond: e == ATypedOpenEnum::SPEC_P, inner: U8 }, Choice(Cond { cond: e == ATypedOpenEnum::SPEC_Q, inner: U16Le }, Choice(Cond { cond: e == ATypedOpenEnum::SPEC_R, inner: U32Le }, Cond { cond: !(e == ATypedOpenEnum::SPEC_P || e == ATypedOpenEnum::SPEC_Q || e == ATypedOpenEnum::SPEC_R), inner: bytes::Tail }))), mapper: ATypedChooseWithDefaultMapper })
}

pub fn a_typed_choose_with_default<'a>(e: u32) -> (o: ATypedChooseWithDefaultCombinator)
    ensures o@ == spec_a_typed_choose_with_default(e@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ATypedChooseWithDefaultCombinator(Mapped { inner: ATypedChooseWithDefaultCombinator3(Choice::new(Cond { cond: e == ATypedOpenEnum::P, inner: U8 }, ATypedChooseWithDefaultCombinator2(Choice::new(Cond { cond: e == ATypedOpenEnum::Q, inner: U16Le }, ATypedChooseWithDefaultCombinator1(Choice::new(Cond { cond: e == ATypedOpenEnum::R, inner: U32Le }, Cond { cond: !(e == ATypedOpenEnum::P || e == ATypedOpenEnum::Q || e == ATypedOpenEnum::R), inner: bytes::Tail })))))), mapper: ATypedChooseWithDefaultMapper });
    // assert({
    //     &&& combinator@ == spec_a_typed_choose_with_default(e@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_a_typed_choose_with_default<'a>(input: &'a [u8], e: u32) -> (res: PResult<<ATypedChooseWithDefaultCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_typed_choose_with_default(e@).spec_parse(input@) == Some((n as int, v@)),
        spec_a_typed_choose_with_default(e@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_typed_choose_with_default(e@).spec_parse(input@) is None,
        spec_a_typed_choose_with_default(e@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_typed_choose_with_default( e );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_typed_choose_with_default<'a>(v: <ATypedChooseWithDefaultCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, e: u32) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_typed_choose_with_default(e@).wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_typed_choose_with_default(e@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_typed_choose_with_default(e@).spec_serialize(v@))
        },
{
    let combinator = a_typed_choose_with_default( e );
    combinator.serialize(v, data, pos)
}

pub fn a_typed_choose_with_default_len<'a>(v: <ATypedChooseWithDefaultCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, e: u32) -> (serialize_len: usize)
    requires
        spec_a_typed_choose_with_default(e@).wf(v@),
        spec_a_typed_choose_with_default(e@).spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_a_typed_choose_with_default(e@).spec_serialize(v@).len(),
{
    let combinator = a_typed_choose_with_default( e );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecAChooseWithDefault {
    A(u8),
    B(u16),
    C(u32),
    Unrecognized(Seq<u8>),
}

pub type SpecAChooseWithDefaultInner = Either<u8, Either<u16, Either<u32, Seq<u8>>>>;

impl SpecFrom<SpecAChooseWithDefault> for SpecAChooseWithDefaultInner {
    open spec fn spec_from(m: SpecAChooseWithDefault) -> SpecAChooseWithDefaultInner {
        match m {
            SpecAChooseWithDefault::A(m) => Either::Left(m),
            SpecAChooseWithDefault::B(m) => Either::Right(Either::Left(m)),
            SpecAChooseWithDefault::C(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecAChooseWithDefault::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

                
impl SpecFrom<SpecAChooseWithDefaultInner> for SpecAChooseWithDefault {
    open spec fn spec_from(m: SpecAChooseWithDefaultInner) -> SpecAChooseWithDefault {
        match m {
            Either::Left(m) => SpecAChooseWithDefault::A(m),
            Either::Right(Either::Left(m)) => SpecAChooseWithDefault::B(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecAChooseWithDefault::C(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecAChooseWithDefault::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AChooseWithDefault<'a> {
    A(u8),
    B(u16),
    C(u32),
    Unrecognized(&'a [u8]),
}

pub type AChooseWithDefaultInner<'a> = Either<u8, Either<u16, Either<u32, &'a [u8]>>>;

pub type AChooseWithDefaultInnerRef<'a> = Either<&'a u8, Either<&'a u16, Either<&'a u32, &'a &'a [u8]>>>;


impl<'a> View for AChooseWithDefault<'a> {
    type V = SpecAChooseWithDefault;
    open spec fn view(&self) -> Self::V {
        match self {
            AChooseWithDefault::A(m) => SpecAChooseWithDefault::A(m@),
            AChooseWithDefault::B(m) => SpecAChooseWithDefault::B(m@),
            AChooseWithDefault::C(m) => SpecAChooseWithDefault::C(m@),
            AChooseWithDefault::Unrecognized(m) => SpecAChooseWithDefault::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a AChooseWithDefault<'a>> for AChooseWithDefaultInnerRef<'a> {
    fn ex_from(m: &'a AChooseWithDefault<'a>) -> AChooseWithDefaultInnerRef<'a> {
        match m {
            AChooseWithDefault::A(m) => Either::Left(m),
            AChooseWithDefault::B(m) => Either::Right(Either::Left(m)),
            AChooseWithDefault::C(m) => Either::Right(Either::Right(Either::Left(m))),
            AChooseWithDefault::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl<'a> From<AChooseWithDefaultInner<'a>> for AChooseWithDefault<'a> {
    fn ex_from(m: AChooseWithDefaultInner<'a>) -> AChooseWithDefault<'a> {
        match m {
            Either::Left(m) => AChooseWithDefault::A(m),
            Either::Right(Either::Left(m)) => AChooseWithDefault::B(m),
            Either::Right(Either::Right(Either::Left(m))) => AChooseWithDefault::C(m),
            Either::Right(Either::Right(Either::Right(m))) => AChooseWithDefault::Unrecognized(m),
        }
    }
    
}


pub struct AChooseWithDefaultMapper;
impl View for AChooseWithDefaultMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for AChooseWithDefaultMapper {
    type Src = SpecAChooseWithDefaultInner;
    type Dst = SpecAChooseWithDefault;
}
impl SpecIsoProof for AChooseWithDefaultMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for AChooseWithDefaultMapper {
    type Src = AChooseWithDefaultInner<'a>;
    type Dst = AChooseWithDefault<'a>;
    type RefSrc = AChooseWithDefaultInnerRef<'a>;
}

type SpecAChooseWithDefaultCombinatorAlias1 = Choice<Cond<U32Le>, Cond<bytes::Tail>>;
type SpecAChooseWithDefaultCombinatorAlias2 = Choice<Cond<U16Le>, SpecAChooseWithDefaultCombinatorAlias1>;
type SpecAChooseWithDefaultCombinatorAlias3 = Choice<Cond<U8>, SpecAChooseWithDefaultCombinatorAlias2>;
pub struct SpecAChooseWithDefaultCombinator(pub SpecAChooseWithDefaultCombinatorAlias);

impl SpecCombinator for SpecAChooseWithDefaultCombinator {
    type Type = SpecAChooseWithDefault;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAChooseWithDefaultCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecAChooseWithDefaultCombinatorAlias::is_prefix_secure() }
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
pub type SpecAChooseWithDefaultCombinatorAlias = Mapped<SpecAChooseWithDefaultCombinatorAlias3, AChooseWithDefaultMapper>;
type AChooseWithDefaultCombinatorAlias1 = Choice<Cond<U32Le>, Cond<bytes::Tail>>;
type AChooseWithDefaultCombinatorAlias2 = Choice<Cond<U16Le>, AChooseWithDefaultCombinator1>;
type AChooseWithDefaultCombinatorAlias3 = Choice<Cond<U8>, AChooseWithDefaultCombinator2>;
pub struct AChooseWithDefaultCombinator1(pub AChooseWithDefaultCombinatorAlias1);
impl View for AChooseWithDefaultCombinator1 {
    type V = SpecAChooseWithDefaultCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(AChooseWithDefaultCombinator1, AChooseWithDefaultCombinatorAlias1);

pub struct AChooseWithDefaultCombinator2(pub AChooseWithDefaultCombinatorAlias2);
impl View for AChooseWithDefaultCombinator2 {
    type V = SpecAChooseWithDefaultCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(AChooseWithDefaultCombinator2, AChooseWithDefaultCombinatorAlias2);

pub struct AChooseWithDefaultCombinator3(pub AChooseWithDefaultCombinatorAlias3);
impl View for AChooseWithDefaultCombinator3 {
    type V = SpecAChooseWithDefaultCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(AChooseWithDefaultCombinator3, AChooseWithDefaultCombinatorAlias3);

pub struct AChooseWithDefaultCombinator(pub AChooseWithDefaultCombinatorAlias);

impl View for AChooseWithDefaultCombinator {
    type V = SpecAChooseWithDefaultCombinator;
    open spec fn view(&self) -> Self::V { SpecAChooseWithDefaultCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AChooseWithDefaultCombinator {
    type Type = AChooseWithDefault<'a>;
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
pub type AChooseWithDefaultCombinatorAlias = Mapped<AChooseWithDefaultCombinator3, AChooseWithDefaultMapper>;


pub open spec fn spec_a_choose_with_default(e: u8) -> SpecAChooseWithDefaultCombinator {
    SpecAChooseWithDefaultCombinator(Mapped { inner: Choice(Cond { cond: e == AnOpenEnum::SPEC_A, inner: U8 }, Choice(Cond { cond: e == AnOpenEnum::SPEC_B, inner: U16Le }, Choice(Cond { cond: e == AnOpenEnum::SPEC_C, inner: U32Le }, Cond { cond: !(e == AnOpenEnum::SPEC_A || e == AnOpenEnum::SPEC_B || e == AnOpenEnum::SPEC_C), inner: bytes::Tail }))), mapper: AChooseWithDefaultMapper })
}

pub fn a_choose_with_default<'a>(e: u8) -> (o: AChooseWithDefaultCombinator)
    ensures o@ == spec_a_choose_with_default(e@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = AChooseWithDefaultCombinator(Mapped { inner: AChooseWithDefaultCombinator3(Choice::new(Cond { cond: e == AnOpenEnum::A, inner: U8 }, AChooseWithDefaultCombinator2(Choice::new(Cond { cond: e == AnOpenEnum::B, inner: U16Le }, AChooseWithDefaultCombinator1(Choice::new(Cond { cond: e == AnOpenEnum::C, inner: U32Le }, Cond { cond: !(e == AnOpenEnum::A || e == AnOpenEnum::B || e == AnOpenEnum::C), inner: bytes::Tail })))))), mapper: AChooseWithDefaultMapper });
    // assert({
    //     &&& combinator@ == spec_a_choose_with_default(e@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_a_choose_with_default<'a>(input: &'a [u8], e: u8) -> (res: PResult<<AChooseWithDefaultCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_choose_with_default(e@).spec_parse(input@) == Some((n as int, v@)),
        spec_a_choose_with_default(e@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_choose_with_default(e@).spec_parse(input@) is None,
        spec_a_choose_with_default(e@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_choose_with_default( e );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_choose_with_default<'a>(v: <AChooseWithDefaultCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, e: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_choose_with_default(e@).wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_choose_with_default(e@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_choose_with_default(e@).spec_serialize(v@))
        },
{
    let combinator = a_choose_with_default( e );
    combinator.serialize(v, data, pos)
}

pub fn a_choose_with_default_len<'a>(v: <AChooseWithDefaultCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, e: u8) -> (serialize_len: usize)
    requires
        spec_a_choose_with_default(e@).wf(v@),
        spec_a_choose_with_default(e@).spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_a_choose_with_default(e@).spec_serialize(v@).len(),
{
    let combinator = a_choose_with_default( e );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


}
