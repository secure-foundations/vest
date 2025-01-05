#![allow(warnings)]
#![allow(unused)]
use std::marker::PhantomData;
use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::properties::*;
use vest::regular::and_then::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::choice::*;
use vest::regular::cond::*;
use vest::regular::depend::*;
use vest::regular::map::*;
use vest::regular::refined::*;
use vest::regular::repeat::*;
use vest::regular::repeat_n::*;
use vest::regular::tag::*;
use vest::regular::tail::*;
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;
verus! {

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
            SpecAChooseWithDefault::Unrecognized(m) => Either::Right(
                Either::Right(Either::Right(m)),
            ),
        }
    }
}

impl SpecFrom<SpecAChooseWithDefaultInner> for SpecAChooseWithDefault {
    open spec fn spec_from(m: SpecAChooseWithDefaultInner) -> SpecAChooseWithDefault {
        match m {
            Either::Left(m) => SpecAChooseWithDefault::A(m),
            Either::Right(Either::Left(m)) => SpecAChooseWithDefault::B(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecAChooseWithDefault::C(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecAChooseWithDefault::Unrecognized(
                m,
            ),
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

impl<'a> From<AChooseWithDefault<'a>> for AChooseWithDefaultInner<'a> {
    fn ex_from(m: AChooseWithDefault<'a>) -> AChooseWithDefaultInner<'a> {
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

pub struct AChooseWithDefaultMapper<'a>(PhantomData<&'a ()>);

impl<'a> AChooseWithDefaultMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        AChooseWithDefaultMapper(PhantomData)
    }

    pub fn new() -> Self {
        AChooseWithDefaultMapper(PhantomData)
    }
}

impl View for AChooseWithDefaultMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for AChooseWithDefaultMapper<'_> {
    type Src = SpecAChooseWithDefaultInner;

    type Dst = SpecAChooseWithDefault;

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl<'a> Iso for AChooseWithDefaultMapper<'a> {
    type Src = AChooseWithDefaultInner<'a>;

    type Dst = AChooseWithDefault<'a>;
}

pub struct SpecAChooseWithDefaultCombinator(SpecAChooseWithDefaultCombinatorAlias);

impl SpecCombinator for SpecAChooseWithDefaultCombinator {
    type Type = SpecAChooseWithDefault;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecAChooseWithDefaultCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecAChooseWithDefaultCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecAChooseWithDefaultCombinatorAlias = Mapped<
    OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, OrdChoice<Cond<U32Le>, Cond<Tail>>>>,
    AChooseWithDefaultMapper<'static>,
>;

pub struct AChooseWithDefaultCombinator<'a>(AChooseWithDefaultCombinatorAlias<'a>);

impl<'a> View for AChooseWithDefaultCombinator<'a> {
    type V = SpecAChooseWithDefaultCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecAChooseWithDefaultCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for AChooseWithDefaultCombinator<'a> {
    type Type = AChooseWithDefault<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type AChooseWithDefaultCombinatorAlias<'a> = Mapped<
    OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, OrdChoice<Cond<U32Le>, Cond<Tail>>>>,
    AChooseWithDefaultMapper<'a>,
>;

pub closed spec fn spec_a_choose_with_default(
    e: SpecAnOpenEnum,
) -> SpecAChooseWithDefaultCombinator {
    SpecAChooseWithDefaultCombinator(
        Mapped {
            inner: OrdChoice(
                Cond { cond: e == 0, inner: U8 },
                OrdChoice(
                    Cond { cond: e == 1, inner: U16Le },
                    OrdChoice(
                        Cond { cond: e == 2, inner: U32Le },
                        Cond { cond: !(e == 0 || e == 1 || e == 2), inner: Tail },
                    ),
                ),
            ),
            mapper: AChooseWithDefaultMapper::spec_new(),
        },
    )
}

pub fn a_choose_with_default<'a>(e: AnOpenEnum) -> (o: AChooseWithDefaultCombinator<'a>)
    ensures
        o@ == spec_a_choose_with_default(e@),
{
    AChooseWithDefaultCombinator(
        Mapped {
            inner: OrdChoice::new(
                Cond { cond: e == 0, inner: U8 },
                OrdChoice::new(
                    Cond { cond: e == 1, inner: U16Le },
                    OrdChoice::new(
                        Cond { cond: e == 2, inner: U32Le },
                        Cond { cond: !(e == 0 || e == 1 || e == 2), inner: Tail },
                    ),
                ),
            ),
            mapper: AChooseWithDefaultMapper::new(),
        },
    )
}

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AClosedEnum {
    A = 0,
    B = 1,
    C = 2,
}

pub type SpecAClosedEnum = AClosedEnum;

pub type AClosedEnumInner = u8;

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
            AClosedEnum::A => Ok(0u8),
            AClosedEnum::B => Ok(1u8),
            AClosedEnum::C => Ok(2u8),
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

impl TryFrom<AClosedEnum> for AClosedEnumInner {
    type Error = ();

    fn ex_try_from(v: AClosedEnum) -> Result<AClosedEnumInner, ()> {
        match v {
            AClosedEnum::A => Ok(0u8),
            AClosedEnum::B => Ok(1u8),
            AClosedEnum::C => Ok(2u8),
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

impl SpecTryFromInto for AClosedEnumMapper {
    type Src = AClosedEnumInner;

    type Dst = AClosedEnum;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl TryFromInto for AClosedEnumMapper {
    type Src = AClosedEnumInner;

    type Dst = AClosedEnum;
}

pub struct SpecAClosedEnumCombinator(SpecAClosedEnumCombinatorAlias);

impl SpecCombinator for SpecAClosedEnumCombinator {
    type Type = SpecAClosedEnum;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecAClosedEnumCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecAClosedEnumCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecAClosedEnumCombinatorAlias = TryMap<U8, AClosedEnumMapper>;

pub struct AClosedEnumCombinator(AClosedEnumCombinatorAlias);

impl View for AClosedEnumCombinator {
    type V = SpecAClosedEnumCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecAClosedEnumCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for AClosedEnumCombinator {
    type Type = AClosedEnum;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type AClosedEnumCombinatorAlias = TryMap<U8, AClosedEnumMapper>;

pub closed spec fn spec_a_closed_enum() -> SpecAClosedEnumCombinator {
    SpecAClosedEnumCombinator(TryMap { inner: U8, mapper: AClosedEnumMapper })
}

pub fn a_closed_enum() -> (o: AClosedEnumCombinator)
    ensures
        o@ == spec_a_closed_enum(),
{
    AClosedEnumCombinator(TryMap { inner: U8, mapper: AClosedEnumMapper })
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

impl From<ARegularChoose> for ARegularChooseInner {
    fn ex_from(m: ARegularChoose) -> ARegularChooseInner {
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

impl ARegularChooseMapper {
    pub closed spec fn spec_new() -> Self {
        ARegularChooseMapper
    }

    pub fn new() -> Self {
        ARegularChooseMapper
    }
}

impl View for ARegularChooseMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for ARegularChooseMapper {
    type Src = SpecARegularChooseInner;

    type Dst = SpecARegularChoose;

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl Iso for ARegularChooseMapper {
    type Src = ARegularChooseInner;

    type Dst = ARegularChoose;
}

pub struct SpecARegularChooseCombinator(SpecARegularChooseCombinatorAlias);

impl SpecCombinator for SpecARegularChooseCombinator {
    type Type = SpecARegularChoose;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecARegularChooseCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecARegularChooseCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecARegularChooseCombinatorAlias = Mapped<
    OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, Cond<U32Le>>>,
    ARegularChooseMapper,
>;

pub struct ARegularChooseCombinator(ARegularChooseCombinatorAlias);

impl View for ARegularChooseCombinator {
    type V = SpecARegularChooseCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecARegularChooseCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for ARegularChooseCombinator {
    type Type = ARegularChoose;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type ARegularChooseCombinatorAlias = Mapped<
    OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, Cond<U32Le>>>,
    ARegularChooseMapper,
>;

pub closed spec fn spec_a_regular_choose(e: SpecAClosedEnum) -> SpecARegularChooseCombinator {
    SpecARegularChooseCombinator(
        Mapped {
            inner: OrdChoice(
                Cond { cond: e == AClosedEnum::A, inner: U8 },
                OrdChoice(
                    Cond { cond: e == AClosedEnum::B, inner: U16Le },
                    Cond { cond: e == AClosedEnum::C, inner: U32Le },
                ),
            ),
            mapper: ARegularChooseMapper::spec_new(),
        },
    )
}

pub fn a_regular_choose<'a>(e: AClosedEnum) -> (o: ARegularChooseCombinator)
    ensures
        o@ == spec_a_regular_choose(e@),
{
    ARegularChooseCombinator(
        Mapped {
            inner: OrdChoice::new(
                Cond { cond: e == AClosedEnum::A, inner: U8 },
                OrdChoice::new(
                    Cond { cond: e == AClosedEnum::B, inner: U16Le },
                    Cond { cond: e == AClosedEnum::C, inner: U32Le },
                ),
            ),
            mapper: ARegularChooseMapper::new(),
        },
    )
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

impl From<ANonDependentChoose> for ANonDependentChooseInner {
    fn ex_from(m: ANonDependentChoose) -> ANonDependentChooseInner {
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

impl ANonDependentChooseMapper {
    pub closed spec fn spec_new() -> Self {
        ANonDependentChooseMapper
    }

    pub fn new() -> Self {
        ANonDependentChooseMapper
    }
}

impl View for ANonDependentChooseMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for ANonDependentChooseMapper {
    type Src = SpecANonDependentChooseInner;

    type Dst = SpecANonDependentChoose;

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl Iso for ANonDependentChooseMapper {
    type Src = ANonDependentChooseInner;

    type Dst = ANonDependentChoose;
}

pub struct SpecANonDependentChooseCombinator(SpecANonDependentChooseCombinatorAlias);

impl SpecCombinator for SpecANonDependentChooseCombinator {
    type Type = SpecANonDependentChoose;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecANonDependentChooseCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecANonDependentChooseCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecANonDependentChooseCombinatorAlias = Mapped<
    OrdChoice<
        Refined<U8, Predicate8434700403445569729>,
        OrdChoice<
            Refined<U8, Predicate3779459584691363859>,
            Refined<U8, Predicate16013864750610309580>,
        >,
    >,
    ANonDependentChooseMapper,
>;

pub struct Predicate8434700403445569729;

impl View for Predicate8434700403445569729 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred for Predicate8434700403445569729 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 10)
    }
}

impl SpecPred for Predicate8434700403445569729 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
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

impl Pred for Predicate3779459584691363859 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 11 && i <= 20)
    }
}

impl SpecPred for Predicate3779459584691363859 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
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

impl Pred for Predicate16013864750610309580 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 21)
    }
}

impl SpecPred for Predicate16013864750610309580 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 21)
    }
}

pub struct ANonDependentChooseCombinator(ANonDependentChooseCombinatorAlias);

impl View for ANonDependentChooseCombinator {
    type V = SpecANonDependentChooseCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecANonDependentChooseCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for ANonDependentChooseCombinator {
    type Type = ANonDependentChoose;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type ANonDependentChooseCombinatorAlias = Mapped<
    OrdChoice<
        Refined<U8, Predicate8434700403445569729>,
        OrdChoice<
            Refined<U8, Predicate3779459584691363859>,
            Refined<U8, Predicate16013864750610309580>,
        >,
    >,
    ANonDependentChooseMapper,
>;

pub closed spec fn spec_a_non_dependent_choose() -> SpecANonDependentChooseCombinator {
    SpecANonDependentChooseCombinator(
        Mapped {
            inner: OrdChoice(
                Refined { inner: U8, predicate: Predicate8434700403445569729 },
                OrdChoice(
                    Refined { inner: U8, predicate: Predicate3779459584691363859 },
                    Refined { inner: U8, predicate: Predicate16013864750610309580 },
                ),
            ),
            mapper: ANonDependentChooseMapper::spec_new(),
        },
    )
}

pub fn a_non_dependent_choose() -> (o: ANonDependentChooseCombinator)
    ensures
        o@ == spec_a_non_dependent_choose(),
{
    ANonDependentChooseCombinator(
        Mapped {
            inner: OrdChoice::new(
                Refined { inner: U8, predicate: Predicate8434700403445569729 },
                OrdChoice::new(
                    Refined { inner: U8, predicate: Predicate3779459584691363859 },
                    Refined { inner: U8, predicate: Predicate16013864750610309580 },
                ),
            ),
            mapper: ANonDependentChooseMapper::new(),
        },
    )
}

pub type SpecAnOpenEnum = u8;

pub type AnOpenEnum = u8;

pub struct SpecAnOpenEnumCombinator(SpecAnOpenEnumCombinatorAlias);

impl SpecCombinator for SpecAnOpenEnumCombinator {
    type Type = SpecAnOpenEnum;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecAnOpenEnumCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecAnOpenEnumCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecAnOpenEnumCombinatorAlias = U8;

pub struct AnOpenEnumCombinator(AnOpenEnumCombinatorAlias);

impl View for AnOpenEnumCombinator {
    type V = SpecAnOpenEnumCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecAnOpenEnumCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for AnOpenEnumCombinator {
    type Type = AnOpenEnum;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type AnOpenEnumCombinatorAlias = U8;

pub closed spec fn spec_an_open_enum() -> SpecAnOpenEnumCombinator {
    SpecAnOpenEnumCombinator(U8)
}

pub fn an_open_enum() -> (o: AnOpenEnumCombinator)
    ensures
        o@ == spec_an_open_enum(),
{
    AnOpenEnumCombinator(U8)
}

} // verus!
