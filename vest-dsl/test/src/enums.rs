#![allow(unused_imports)]
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

impl View for AChooseWithDefault<'_> {
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

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for AChooseWithDefaultMapper {
    type Src<'a> = AChooseWithDefaultInner<'a>;

    type Dst<'a> = AChooseWithDefault<'a>;

    type SrcOwned = AChooseWithDefaultOwnedInner;

    type DstOwned = AChooseWithDefaultOwned;
}

pub enum AChooseWithDefaultOwned {
    A(u8),
    B(u16),
    C(u32),
    Unrecognized(Vec<u8>),
}

pub type AChooseWithDefaultOwnedInner = Either<u8, Either<u16, Either<u32, Vec<u8>>>>;

impl View for AChooseWithDefaultOwned {
    type V = SpecAChooseWithDefault;

    open spec fn view(&self) -> Self::V {
        match self {
            AChooseWithDefaultOwned::A(m) => SpecAChooseWithDefault::A(m@),
            AChooseWithDefaultOwned::B(m) => SpecAChooseWithDefault::B(m@),
            AChooseWithDefaultOwned::C(m) => SpecAChooseWithDefault::C(m@),
            AChooseWithDefaultOwned::Unrecognized(m) => SpecAChooseWithDefault::Unrecognized(m@),
        }
    }
}

impl From<AChooseWithDefaultOwned> for AChooseWithDefaultOwnedInner {
    fn ex_from(m: AChooseWithDefaultOwned) -> AChooseWithDefaultOwnedInner {
        match m {
            AChooseWithDefaultOwned::A(m) => Either::Left(m),
            AChooseWithDefaultOwned::B(m) => Either::Right(Either::Left(m)),
            AChooseWithDefaultOwned::C(m) => Either::Right(Either::Right(Either::Left(m))),
            AChooseWithDefaultOwned::Unrecognized(m) => Either::Right(
                Either::Right(Either::Right(m)),
            ),
        }
    }
}

impl From<AChooseWithDefaultOwnedInner> for AChooseWithDefaultOwned {
    fn ex_from(m: AChooseWithDefaultOwnedInner) -> AChooseWithDefaultOwned {
        match m {
            Either::Left(m) => AChooseWithDefaultOwned::A(m),
            Either::Right(Either::Left(m)) => AChooseWithDefaultOwned::B(m),
            Either::Right(Either::Right(Either::Left(m))) => AChooseWithDefaultOwned::C(m),
            Either::Right(Either::Right(Either::Right(m))) => AChooseWithDefaultOwned::Unrecognized(
                m,
            ),
        }
    }
}

pub type SpecAnOpenEnum = u8;

pub type AnOpenEnum = u8;

pub type AnOpenEnumOwned = u8;

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AClosedEnum {
    A = 0,
    B = 1,
    C = 2,
}

pub type SpecAClosedEnum = AClosedEnum;

pub type AClosedEnumOwned = AClosedEnum;

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
    type Src<'a> = AClosedEnumInner;

    type Dst<'a> = AClosedEnum;

    type SrcOwned = AClosedEnumInner;

    type DstOwned = AClosedEnum;
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
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for ARegularChooseMapper {
    type Src<'a> = ARegularChooseInner;

    type Dst<'a> = ARegularChoose;

    type SrcOwned = ARegularChooseOwnedInner;

    type DstOwned = ARegularChooseOwned;
}

pub enum ARegularChooseOwned {
    A(u8),
    B(u16),
    C(u32),
}

pub type ARegularChooseOwnedInner = Either<u8, Either<u16, u32>>;

impl View for ARegularChooseOwned {
    type V = SpecARegularChoose;

    open spec fn view(&self) -> Self::V {
        match self {
            ARegularChooseOwned::A(m) => SpecARegularChoose::A(m@),
            ARegularChooseOwned::B(m) => SpecARegularChoose::B(m@),
            ARegularChooseOwned::C(m) => SpecARegularChoose::C(m@),
        }
    }
}

impl From<ARegularChooseOwned> for ARegularChooseOwnedInner {
    fn ex_from(m: ARegularChooseOwned) -> ARegularChooseOwnedInner {
        match m {
            ARegularChooseOwned::A(m) => Either::Left(m),
            ARegularChooseOwned::B(m) => Either::Right(Either::Left(m)),
            ARegularChooseOwned::C(m) => Either::Right(Either::Right(m)),
        }
    }
}

impl From<ARegularChooseOwnedInner> for ARegularChooseOwned {
    fn ex_from(m: ARegularChooseOwnedInner) -> ARegularChooseOwned {
        match m {
            Either::Left(m) => ARegularChooseOwned::A(m),
            Either::Right(Either::Left(m)) => ARegularChooseOwned::B(m),
            Either::Right(Either::Right(m)) => ARegularChooseOwned::C(m),
        }
    }
}

pub struct SpecAChooseWithDefaultCombinator(
    Mapped<
        OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, OrdChoice<Cond<U32Le>, Cond<Tail>>>>,
        AChooseWithDefaultMapper,
    >,
);

impl SpecCombinator for SpecAChooseWithDefaultCombinator {
    type SpecResult = SpecAChooseWithDefault;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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
    AChooseWithDefaultMapper,
>;

pub struct AChooseWithDefaultCombinator(
    Mapped<
        OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, OrdChoice<Cond<U32Le>, Cond<Tail>>>>,
        AChooseWithDefaultMapper,
    >,
);

impl View for AChooseWithDefaultCombinator {
    type V = SpecAChooseWithDefaultCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecAChooseWithDefaultCombinator(self.0@)
    }
}

impl Combinator for AChooseWithDefaultCombinator {
    type Result<'a> = AChooseWithDefault<'a>;

    type Owned = AChooseWithDefaultOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type AChooseWithDefaultCombinatorAlias = Mapped<
    OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, OrdChoice<Cond<U32Le>, Cond<Tail>>>>,
    AChooseWithDefaultMapper,
>;

pub struct SpecAnOpenEnumCombinator(U8);

impl SpecCombinator for SpecAnOpenEnumCombinator {
    type SpecResult = SpecAnOpenEnum;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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

pub struct AnOpenEnumCombinator(U8);

impl View for AnOpenEnumCombinator {
    type V = SpecAnOpenEnumCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecAnOpenEnumCombinator(self.0@)
    }
}

impl Combinator for AnOpenEnumCombinator {
    type Result<'a> = AnOpenEnum;

    type Owned = AnOpenEnumOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type AnOpenEnumCombinatorAlias = U8;

pub struct SpecAClosedEnumCombinator(TryMap<U8, AClosedEnumMapper>);

impl SpecCombinator for SpecAClosedEnumCombinator {
    type SpecResult = SpecAClosedEnum;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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

pub struct AClosedEnumCombinator(TryMap<U8, AClosedEnumMapper>);

impl View for AClosedEnumCombinator {
    type V = SpecAClosedEnumCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecAClosedEnumCombinator(self.0@)
    }
}

impl Combinator for AClosedEnumCombinator {
    type Result<'a> = AClosedEnum;

    type Owned = AClosedEnumOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type AClosedEnumCombinatorAlias = TryMap<U8, AClosedEnumMapper>;

pub struct SpecARegularChooseCombinator(
    Mapped<OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, Cond<U32Le>>>, ARegularChooseMapper>,
);

impl SpecCombinator for SpecARegularChooseCombinator {
    type SpecResult = SpecARegularChoose;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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

pub struct ARegularChooseCombinator(
    Mapped<OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, Cond<U32Le>>>, ARegularChooseMapper>,
);

impl View for ARegularChooseCombinator {
    type V = SpecARegularChooseCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecARegularChooseCombinator(self.0@)
    }
}

impl Combinator for ARegularChooseCombinator {
    type Result<'a> = ARegularChoose;

    type Owned = ARegularChooseOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type ARegularChooseCombinatorAlias = Mapped<
    OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, Cond<U32Le>>>,
    ARegularChooseMapper,
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
            mapper: AChooseWithDefaultMapper,
        },
    )
}

pub fn a_choose_with_default<'a>(e: AnOpenEnum) -> (o: AChooseWithDefaultCombinator)
    ensures
        o@ == spec_a_choose_with_default(e@),
{
    AChooseWithDefaultCombinator(
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
            mapper: AChooseWithDefaultMapper,
        },
    )
}

pub closed spec fn spec_an_open_enum() -> SpecAnOpenEnumCombinator {
    SpecAnOpenEnumCombinator(U8)
}

pub fn an_open_enum() -> (o: AnOpenEnumCombinator)
    ensures
        o@ == spec_an_open_enum(),
{
    AnOpenEnumCombinator(U8)
}

pub closed spec fn spec_a_closed_enum() -> SpecAClosedEnumCombinator {
    SpecAClosedEnumCombinator(TryMap { inner: U8, mapper: AClosedEnumMapper })
}

pub fn a_closed_enum() -> (o: AClosedEnumCombinator)
    ensures
        o@ == spec_a_closed_enum(),
{
    AClosedEnumCombinator(TryMap { inner: U8, mapper: AClosedEnumMapper })
}

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
            mapper: ARegularChooseMapper,
        },
    )
}

pub fn a_regular_choose(e: AClosedEnum) -> (o: ARegularChooseCombinator)
    ensures
        o@ == spec_a_regular_choose(e@),
{
    ARegularChooseCombinator(
        Mapped {
            inner: OrdChoice(
                Cond { cond: e == AClosedEnum::A, inner: U8 },
                OrdChoice(
                    Cond { cond: e == AClosedEnum::B, inner: U16Le },
                    Cond { cond: e == AClosedEnum::C, inner: U32Le },
                ),
            ),
            mapper: ARegularChooseMapper,
        },
    )
}

} // verus!
