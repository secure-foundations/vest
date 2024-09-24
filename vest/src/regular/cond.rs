use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Combinator that checks if `cond` is true and then delegates to the `inner` combinator.
pub struct Cond<Inner> {
    pub cond: bool,
    pub inner: Inner,
}

impl<Inner: View> View for Cond<Inner> {
    type V = Cond<Inner::V>;

    open spec fn view(&self) -> Self::V {
        Cond { cond: self.cond, inner: self.inner@ }
    }
}

impl<Inner: SpecCombinator> SpecCombinator for Cond<Inner> {
    type SpecResult = Inner::SpecResult;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if self.cond {
            self.inner.spec_parse(s)
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        if self.cond {
            self.inner.spec_parse_wf(s);
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if self.cond {
            self.inner.spec_serialize(v)
        } else {
            Err(())
        }
    }
}

impl<Inner: SecureSpecCombinator> SecureSpecCombinator for Cond<Inner> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if self.cond {
            self.inner.theorem_serialize_parse_roundtrip(v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if self.cond {
            self.inner.theorem_parse_serialize_roundtrip(buf);
        }
    }

    open spec fn spec_is_prefix_secure() -> bool {
        Inner::spec_is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if self.cond {
            self.inner.lemma_prefix_secure(s1, s2);
        }
    }
}

impl<Inner: Combinator> Combinator for Cond<Inner> where
    Inner::V: SecureSpecCombinator<SpecResult = <Inner::Owned as View>::V>,
 {
    type Result<'a> = Inner::Result<'a>;

    type Owned = Inner::Owned;

    open spec fn spec_length(&self) -> Option<usize> {
        if self.cond@ {
            self.inner.spec_length()
        } else {
            None
        }
    }

    fn length(&self) -> Option<usize> {
        if self.cond {
            self.inner.length()
        } else {
            None
        }
    }

    fn exec_is_prefix_secure() -> bool {
        Inner::exec_is_prefix_secure()
    }

    open spec fn parse_requires(&self) -> bool {
        self.inner.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> Result<(usize, Self::Result<'a>), ParseError> {
        if self.cond {
            self.inner.parse(s)
        } else {
            Err(ParseError::CondFailed)
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.inner.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> Result<usize, SerializeError> {
        if self.cond {
            self.inner.serialize(v, data, pos)
        } else {
            Err(SerializeError::CondFailed)
        }
    }
}

#[cfg(test)]
mod test {
#![allow(unused_imports)]
use crate::properties::*;
use crate::regular::and_then::*;
use crate::regular::bytes::*;
use crate::regular::bytes_n::*;
use crate::regular::choice::*;
use crate::regular::cond::*;
use crate::regular::depend::*;
use crate::regular::map::*;
use crate::regular::refined::*;
use crate::regular::tail::*;
use crate::regular::uints::*;
use crate::utils::*;
use vstd::prelude::*;
verus! {

pub struct SpecMsgD {
    pub f1: Seq<u8>,
    pub f2: u16,
}

pub type SpecMsgDInner = (Seq<u8>, u16);

impl SpecFrom<SpecMsgD> for SpecMsgDInner {
    open spec fn spec_from(m: SpecMsgD) -> SpecMsgDInner {
        (m.f1, m.f2)
    }
}

impl SpecFrom<SpecMsgDInner> for SpecMsgD {
    open spec fn spec_from(m: SpecMsgDInner) -> SpecMsgD {
        let (f1, f2) = m;
        SpecMsgD { f1, f2 }
    }
}

pub struct MsgD<'a> {
    pub f1: &'a [u8],
    pub f2: u16,
}

pub type MsgDInner<'a> = (&'a [u8], u16);

impl View for MsgD<'_> {
    type V = SpecMsgD;

    open spec fn view(&self) -> Self::V {
        SpecMsgD { f1: self.f1@, f2: self.f2@ }
    }
}

impl<'a> From<MsgD<'a>> for MsgDInner<'a> {
    fn ex_from(m: MsgD<'a>) -> MsgDInner<'a> {
        (m.f1, m.f2)
    }
}

impl<'a> From<MsgDInner<'a>> for MsgD<'a> {
    fn ex_from(m: MsgDInner<'a>) -> MsgD<'a> {
        let (f1, f2) = m;
        MsgD { f1, f2 }
    }
}

pub struct MsgDMapper;

impl View for MsgDMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgDMapper {
    type Src = SpecMsgDInner;

    type Dst = SpecMsgD;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for MsgDMapper {
    type Src<'a> = MsgDInner<'a>;

    type Dst<'a> = MsgD<'a>;

    type SrcOwned = MsgDOwnedInner;

    type DstOwned = MsgDOwned;
}

pub struct MsgDOwned {
    pub f1: Vec<u8>,
    pub f2: u16,
}

pub type MsgDOwnedInner = (Vec<u8>, u16);

impl View for MsgDOwned {
    type V = SpecMsgD;

    open spec fn view(&self) -> Self::V {
        SpecMsgD { f1: self.f1@, f2: self.f2@ }
    }
}

impl From<MsgDOwned> for MsgDOwnedInner {
    fn ex_from(m: MsgDOwned) -> MsgDOwnedInner {
        (m.f1, m.f2)
    }
}

impl From<MsgDOwnedInner> for MsgDOwned {
    fn ex_from(m: MsgDOwnedInner) -> MsgDOwned {
        let (f1, f2) = m;
        MsgDOwned { f1, f2 }
    }
}

pub type SpecContentType = u8;

pub type ContentType = u8;

pub type ContentTypeOwned = u8;

pub type SpecContent0 = Seq<u8>;

pub type Content0<'a> = &'a [u8];

pub type Content0Owned = Vec<u8>;

pub enum SpecMsgCF4 {
    C0(SpecContent0),
    C1(u16),
    C2(u32),
    Unrecognized(Seq<u8>),
}

pub type SpecMsgCF4Inner = ord_choice_result!(SpecContent0, u16, u32, Seq<u8>);

impl SpecFrom<SpecMsgCF4> for SpecMsgCF4Inner {
    open spec fn spec_from(m: SpecMsgCF4) -> SpecMsgCF4Inner {
        match m {
            SpecMsgCF4::C0(m) => inj_ord_choice_result!(m, *, *, *),
            SpecMsgCF4::C1(m) => inj_ord_choice_result!(*, m, *, *),
            SpecMsgCF4::C2(m) => inj_ord_choice_result!(*, *, m, *),
            SpecMsgCF4::Unrecognized(m) => inj_ord_choice_result!(*, *, *, m),
        }
    }
}

impl SpecFrom<SpecMsgCF4Inner> for SpecMsgCF4 {
    open spec fn spec_from(m: SpecMsgCF4Inner) -> SpecMsgCF4 {
        match m {
            inj_ord_choice_pat!(m, *, *, *) => SpecMsgCF4::C0(m),
            inj_ord_choice_pat!(*, m, *, *) => SpecMsgCF4::C1(m),
            inj_ord_choice_pat!(*, *, m, *) => SpecMsgCF4::C2(m),
            inj_ord_choice_pat!(*, *, *, m) => SpecMsgCF4::Unrecognized(m),
        }
    }
}

pub enum MsgCF4<'a> {
    C0(Content0<'a>),
    C1(u16),
    C2(u32),
    Unrecognized(&'a [u8]),
}

pub type MsgCF4Inner<'a> = ord_choice_result!(Content0<'a>, u16, u32, &'a [u8]);

impl View for MsgCF4<'_> {
    type V = SpecMsgCF4;

    open spec fn view(&self) -> Self::V {
        match self {
            MsgCF4::C0(m) => SpecMsgCF4::C0(m@),
            MsgCF4::C1(m) => SpecMsgCF4::C1(m@),
            MsgCF4::C2(m) => SpecMsgCF4::C2(m@),
            MsgCF4::Unrecognized(m) => SpecMsgCF4::Unrecognized(m@),
        }
    }
}

impl<'a> From<MsgCF4<'a>> for MsgCF4Inner<'a> {
    fn ex_from(m: MsgCF4<'a>) -> MsgCF4Inner<'a> {
        match m {
            MsgCF4::C0(m) => inj_ord_choice_result!(m, *, *, *),
            MsgCF4::C1(m) => inj_ord_choice_result!(*, m, *, *),
            MsgCF4::C2(m) => inj_ord_choice_result!(*, *, m, *),
            MsgCF4::Unrecognized(m) => inj_ord_choice_result!(*, *, *, m),
        }
    }
}

impl<'a> From<MsgCF4Inner<'a>> for MsgCF4<'a> {
    fn ex_from(m: MsgCF4Inner<'a>) -> MsgCF4<'a> {
        match m {
            inj_ord_choice_pat!(m, *, *, *) => MsgCF4::C0(m),
            inj_ord_choice_pat!(*, m, *, *) => MsgCF4::C1(m),
            inj_ord_choice_pat!(*, *, m, *) => MsgCF4::C2(m),
            inj_ord_choice_pat!(*, *, *, m) => MsgCF4::Unrecognized(m),
        }
    }
}

pub struct MsgCF4Mapper;

impl View for MsgCF4Mapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgCF4Mapper {
    type Src = SpecMsgCF4Inner;

    type Dst = SpecMsgCF4;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for MsgCF4Mapper {
    type Src<'a> = MsgCF4Inner<'a>;

    type Dst<'a> = MsgCF4<'a>;

    type SrcOwned = MsgCF4OwnedInner;

    type DstOwned = MsgCF4Owned;
}

pub enum MsgCF4Owned {
    C0(Content0Owned),
    C1(u16),
    C2(u32),
    Unrecognized(Vec<u8>),
}

pub type MsgCF4OwnedInner = ord_choice_result!(Content0Owned, u16, u32, Vec<u8>);

impl View for MsgCF4Owned {
    type V = SpecMsgCF4;

    open spec fn view(&self) -> Self::V {
        match self {
            MsgCF4Owned::C0(m) => SpecMsgCF4::C0(m@),
            MsgCF4Owned::C1(m) => SpecMsgCF4::C1(m@),
            MsgCF4Owned::C2(m) => SpecMsgCF4::C2(m@),
            MsgCF4Owned::Unrecognized(m) => SpecMsgCF4::Unrecognized(m@),
        }
    }
}

impl From<MsgCF4Owned> for MsgCF4OwnedInner {
    fn ex_from(m: MsgCF4Owned) -> MsgCF4OwnedInner {
        match m {
            MsgCF4Owned::C0(m) => inj_ord_choice_result!(m, *, *, *),
            MsgCF4Owned::C1(m) => inj_ord_choice_result!(*, m, *, *),
            MsgCF4Owned::C2(m) => inj_ord_choice_result!(*, *, m, *),
            MsgCF4Owned::Unrecognized(m) => inj_ord_choice_result!(*, *, *, m),
        }
    }
}

impl From<MsgCF4OwnedInner> for MsgCF4Owned {
    fn ex_from(m: MsgCF4OwnedInner) -> MsgCF4Owned {
        match m {
            inj_ord_choice_pat!(m, *, *, *) => MsgCF4Owned::C0(m),
            inj_ord_choice_pat!(*, m, *, *) => MsgCF4Owned::C1(m),
            inj_ord_choice_pat!(*, *, m, *) => MsgCF4Owned::C2(m),
            inj_ord_choice_pat!(*, *, *, m) => MsgCF4Owned::Unrecognized(m),
        }
    }
}

pub struct SpecMsgB {
    pub f1: SpecMsgD,
}

pub type SpecMsgBInner = SpecMsgD;

impl SpecFrom<SpecMsgB> for SpecMsgBInner {
    open spec fn spec_from(m: SpecMsgB) -> SpecMsgBInner {
        m.f1
    }
}

impl SpecFrom<SpecMsgBInner> for SpecMsgB {
    open spec fn spec_from(m: SpecMsgBInner) -> SpecMsgB {
        let f1 = m;
        SpecMsgB { f1 }
    }
}

pub struct MsgB<'a> {
    pub f1: MsgD<'a>,
}

pub type MsgBInner<'a> = MsgD<'a>;

impl View for MsgB<'_> {
    type V = SpecMsgB;

    open spec fn view(&self) -> Self::V {
        SpecMsgB { f1: self.f1@ }
    }
}

impl<'a> From<MsgB<'a>> for MsgBInner<'a> {
    fn ex_from(m: MsgB<'a>) -> MsgBInner<'a> {
        m.f1
    }
}

impl<'a> From<MsgBInner<'a>> for MsgB<'a> {
    fn ex_from(m: MsgBInner<'a>) -> MsgB<'a> {
        let f1 = m;
        MsgB { f1 }
    }
}

pub struct MsgBMapper;

impl View for MsgBMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgBMapper {
    type Src = SpecMsgBInner;

    type Dst = SpecMsgB;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for MsgBMapper {
    type Src<'a> = MsgBInner<'a>;

    type Dst<'a> = MsgB<'a>;

    type SrcOwned = MsgBOwnedInner;

    type DstOwned = MsgBOwned;
}

pub struct MsgBOwned {
    pub f1: MsgDOwned,
}

pub type MsgBOwnedInner = MsgDOwned;

impl View for MsgBOwned {
    type V = SpecMsgB;

    open spec fn view(&self) -> Self::V {
        SpecMsgB { f1: self.f1@ }
    }
}

impl From<MsgBOwned> for MsgBOwnedInner {
    fn ex_from(m: MsgBOwned) -> MsgBOwnedInner {
        m.f1
    }
}

impl From<MsgBOwnedInner> for MsgBOwned {
    fn ex_from(m: MsgBOwnedInner) -> MsgBOwned {
        let f1 = m;
        MsgBOwned { f1 }
    }
}

pub struct SpecMsgA {
    pub f1: SpecMsgB,
    pub f2: Seq<u8>,
}

pub type SpecMsgAInner = (SpecMsgB, Seq<u8>);

impl SpecFrom<SpecMsgA> for SpecMsgAInner {
    open spec fn spec_from(m: SpecMsgA) -> SpecMsgAInner {
        (m.f1, m.f2)
    }
}

impl SpecFrom<SpecMsgAInner> for SpecMsgA {
    open spec fn spec_from(m: SpecMsgAInner) -> SpecMsgA {
        let (f1, f2) = m;
        SpecMsgA { f1, f2 }
    }
}

pub struct MsgA<'a> {
    pub f1: MsgB<'a>,
    pub f2: &'a [u8],
}

pub type MsgAInner<'a> = (MsgB<'a>, &'a [u8]);

impl View for MsgA<'_> {
    type V = SpecMsgA;

    open spec fn view(&self) -> Self::V {
        SpecMsgA { f1: self.f1@, f2: self.f2@ }
    }
}

impl<'a> From<MsgA<'a>> for MsgAInner<'a> {
    fn ex_from(m: MsgA<'a>) -> MsgAInner<'a> {
        (m.f1, m.f2)
    }
}

impl<'a> From<MsgAInner<'a>> for MsgA<'a> {
    fn ex_from(m: MsgAInner<'a>) -> MsgA<'a> {
        let (f1, f2) = m;
        MsgA { f1, f2 }
    }
}

pub struct MsgAMapper;

impl View for MsgAMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgAMapper {
    type Src = SpecMsgAInner;

    type Dst = SpecMsgA;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for MsgAMapper {
    type Src<'a> = MsgAInner<'a>;

    type Dst<'a> = MsgA<'a>;

    type SrcOwned = MsgAOwnedInner;

    type DstOwned = MsgAOwned;
}

pub struct MsgAOwned {
    pub f1: MsgBOwned,
    pub f2: Vec<u8>,
}

pub type MsgAOwnedInner = (MsgBOwned, Vec<u8>);

impl View for MsgAOwned {
    type V = SpecMsgA;

    open spec fn view(&self) -> Self::V {
        SpecMsgA { f1: self.f1@, f2: self.f2@ }
    }
}

impl From<MsgAOwned> for MsgAOwnedInner {
    fn ex_from(m: MsgAOwned) -> MsgAOwnedInner {
        (m.f1, m.f2)
    }
}

impl From<MsgAOwnedInner> for MsgAOwned {
    fn ex_from(m: MsgAOwnedInner) -> MsgAOwned {
        let (f1, f2) = m;
        MsgAOwned { f1, f2 }
    }
}

pub struct SpecMsgC {
    pub f2: SpecContentType,
    pub f3: u8,
    pub f4: SpecMsgCF4,
}

pub type SpecMsgCInner = ((SpecContentType, u8), SpecMsgCF4);

impl SpecFrom<SpecMsgC> for SpecMsgCInner {
    open spec fn spec_from(m: SpecMsgC) -> SpecMsgCInner {
        ((m.f2, m.f3), m.f4)
    }
}

impl SpecFrom<SpecMsgCInner> for SpecMsgC {
    open spec fn spec_from(m: SpecMsgCInner) -> SpecMsgC {
        let ((f2, f3), f4) = m;
        SpecMsgC { f2, f3, f4 }
    }
}

pub struct MsgC<'a> {
    pub f2: ContentType,
    pub f3: u8,
    pub f4: MsgCF4<'a>,
}

pub type MsgCInner<'a> = ((ContentType, u8), MsgCF4<'a>);

impl View for MsgC<'_> {
    type V = SpecMsgC;

    open spec fn view(&self) -> Self::V {
        SpecMsgC { f2: self.f2@, f3: self.f3@, f4: self.f4@ }
    }
}

impl<'a> From<MsgC<'a>> for MsgCInner<'a> {
    fn ex_from(m: MsgC<'a>) -> MsgCInner<'a> {
        ((m.f2, m.f3), m.f4)
    }
}

impl<'a> From<MsgCInner<'a>> for MsgC<'a> {
    fn ex_from(m: MsgCInner<'a>) -> MsgC<'a> {
        let ((f2, f3), f4) = m;
        MsgC { f2, f3, f4 }
    }
}

pub struct MsgCMapper;

impl View for MsgCMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgCMapper {
    type Src = SpecMsgCInner;

    type Dst = SpecMsgC;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for MsgCMapper {
    type Src<'a> = MsgCInner<'a>;

    type Dst<'a> = MsgC<'a>;

    type SrcOwned = MsgCOwnedInner;

    type DstOwned = MsgCOwned;
}

pub struct MsgCOwned {
    pub f2: ContentTypeOwned,
    pub f3: u8,
    pub f4: MsgCF4Owned,
}

pub type MsgCOwnedInner = ((ContentTypeOwned, u8), MsgCF4Owned);

impl View for MsgCOwned {
    type V = SpecMsgC;

    open spec fn view(&self) -> Self::V {
        SpecMsgC { f2: self.f2@, f3: self.f3@, f4: self.f4@ }
    }
}

impl From<MsgCOwned> for MsgCOwnedInner {
    fn ex_from(m: MsgCOwned) -> MsgCOwnedInner {
        ((m.f2, m.f3), m.f4)
    }
}

impl From<MsgCOwnedInner> for MsgCOwned {
    fn ex_from(m: MsgCOwnedInner) -> MsgCOwned {
        let ((f2, f3), f4) = m;
        MsgCOwned { f2, f3, f4 }
    }
}

pub spec const SPEC_MSGD_F1: Seq<u8> = seq![1; 4];

pub exec const MSGD_F1: [u8; 4]
    ensures
        MSGD_F1@ == SPEC_MSGD_F1,
{
    let arr: [u8; 4] = [1;4];
    assert(arr@ == SPEC_MSGD_F1);
    arr
}

pub struct BytesPredicate16235736133663645624;

impl View for BytesPredicate16235736133663645624 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPred for BytesPredicate16235736133663645624 {
    type Input = Seq<u8>;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        i == &SPEC_MSGD_F1
    }
}

impl Pred for BytesPredicate16235736133663645624 {
    type Input<'a> = &'a [u8];

    type InputOwned = Vec<u8>;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        compare_slice(i, MSGD_F1.as_slice())
    }
}

pub const MSGD_F2: u16 = 4660;

pub struct IntIs4660;

impl View for IntIs4660 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPred for IntIs4660 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        *i == 4660
    }
}

impl Pred for IntIs4660 {
    type Input<'a> = u16;

    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        *i == 4660
    }
}

pub type MsgDCombinator = Mapped<
    (Refined<BytesN<4>, BytesPredicate16235736133663645624>, Refined<U16, IntIs4660>),
    MsgDMapper,
>;

pub type ContentTypeCombinator = U8;

pub type Content0Combinator = Bytes;

pub type MsgCF4Combinator = AndThen<
    Bytes,
    Mapped<
        ord_choice_type!(Cond<Content0Combinator>, Cond<U16>, Cond<U32>, Cond<Tail>),
        MsgCF4Mapper,
    >,
>;

pub type MsgBCombinator = Mapped<MsgDCombinator, MsgBMapper>;

pub type MsgACombinator = Mapped<(MsgBCombinator, Tail), MsgAMapper>;

pub type MsgCCombinator = Mapped<
    SpecDepend<(ContentTypeCombinator, U8), MsgCF4Combinator>,
    MsgCMapper,
>;

pub open spec fn spec_msg_d() -> MsgDCombinator {
    Mapped {
        inner: (
            Refined { inner: BytesN::<4>, predicate: BytesPredicate16235736133663645624 },
            Refined { inner: U16, predicate: IntIs4660 },
        ),
        mapper: MsgDMapper,
    }
}

pub fn msg_d() -> (o: MsgDCombinator)
    ensures
        o@ == spec_msg_d(),
{
    Mapped {
        inner: (
            Refined { inner: BytesN::<4>, predicate: BytesPredicate16235736133663645624 },
            Refined { inner: U16, predicate: IntIs4660 },
        ),
        mapper: MsgDMapper,
    }
}

pub open spec fn spec_content_type() -> ContentTypeCombinator {
    U8
}

pub fn content_type() -> (o: ContentTypeCombinator)
    ensures
        o@ == spec_content_type(),
{
    U8
}

pub open spec fn spec_content_0(num: u8) -> Content0Combinator {
    Bytes(num as usize)
}

pub fn content_0<'a>(num: u8) -> (o: Content0Combinator)
    ensures
        o@ == spec_content_0(num@),
{
    Bytes(num as usize)
}

pub open spec fn spec_msg_c_f4(f3: u8, f2: SpecContentType) -> MsgCF4Combinator {
    AndThen(
        Bytes(f3 as usize),
        Mapped {
            inner: ord_choice!(
                Cond { cond: f2 == 0, inner: spec_content_0(f3) },
                Cond { cond: f2 == 1, inner: U16 },
                Cond { cond: f2 == 2, inner: U32 },
                Cond { cond: !(f2 == 0 || f2 == 1 || f2 == 2), inner: Tail },
            ),
            mapper: MsgCF4Mapper,
        },
    )
}

pub fn msg_c_f4<'a>(f3: u8, f2: ContentType) -> (o: MsgCF4Combinator)
    ensures
        o@ == spec_msg_c_f4(f3@, f2@),
{
    AndThen(
        Bytes(f3 as usize),
        Mapped {
            inner: ord_choice!(
                Cond { cond: f2 == 0, inner: content_0(f3) },
                Cond { cond: f2 == 1, inner: U16 },
                Cond { cond: f2 == 2, inner: U32 },
                Cond { cond: !(f2 == 0 || f2 == 1 || f2 == 2), inner: Tail },
            ),
            mapper: MsgCF4Mapper,
        },
    )
}

pub open spec fn spec_msg_b() -> MsgBCombinator {
    Mapped { inner: spec_msg_d(), mapper: MsgBMapper }
}

pub fn msg_b() -> (o: MsgBCombinator)
    ensures
        o@ == spec_msg_b(),
{
    Mapped { inner: msg_d(), mapper: MsgBMapper }
}

pub open spec fn spec_msg_a() -> MsgACombinator {
    Mapped { inner: (spec_msg_b(), Tail), mapper: MsgAMapper }
}

pub fn msg_a() -> (o: MsgACombinator)
    ensures
        o@ == spec_msg_a(),
{
    Mapped { inner: (msg_b(), Tail), mapper: MsgAMapper }
}

pub open spec fn parse_spec_msg_d(i: Seq<u8>) -> Result<(usize, SpecMsgD), ()> {
    spec_msg_d().spec_parse(i)
}

pub open spec fn serialize_spec_msg_d(msg: SpecMsgD) -> Result<Seq<u8>, ()> {
    spec_msg_d().spec_serialize(msg)
}

pub fn parse_msg_d(i: &[u8]) -> (o: Result<(usize, MsgD<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg_d(i@) matches Ok(r_) && r@ == r_,
{
    msg_d().parse(i)
}

pub fn serialize_msg_d(msg: MsgD<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg_d(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg_d().serialize(msg, data, pos)
}

pub open spec fn parse_spec_content_type(i: Seq<u8>) -> Result<(usize, SpecContentType), ()> {
    spec_content_type().spec_parse(i)
}

pub open spec fn serialize_spec_content_type(msg: SpecContentType) -> Result<Seq<u8>, ()> {
    spec_content_type().spec_serialize(msg)
}

pub fn parse_content_type(i: &[u8]) -> (o: Result<(usize, ContentType), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_content_type(i@) matches Ok(r_) && r@ == r_,
{
    content_type().parse(i)
}

pub fn serialize_content_type(msg: ContentType, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_content_type(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    content_type().serialize(msg, data, pos)
}

pub open spec fn parse_spec_content_0(i: Seq<u8>, num: u8) -> Result<(usize, SpecContent0), ()> {
    spec_content_0(num).spec_parse(i)
}

pub open spec fn serialize_spec_content_0(msg: SpecContent0, num: u8) -> Result<Seq<u8>, ()> {
    spec_content_0(num).spec_serialize(msg)
}

pub fn parse_content_0(i: &[u8], num: u8) -> (o: Result<(usize, Content0<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_content_0(i@, num@) matches Ok(r_) && r@ == r_,
{
    content_0(num).parse(i)
}

pub fn serialize_content_0(msg: Content0<'_>, data: &mut Vec<u8>, pos: usize, num: u8) -> (o:
    Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_content_0(msg@, num@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    content_0(num).serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg_c_f4(i: Seq<u8>, f3: u8, f2: SpecContentType) -> Result<
    (usize, SpecMsgCF4),
    (),
> {
    spec_msg_c_f4(f3, f2).spec_parse(i)
}

pub open spec fn serialize_spec_msg_c_f4(msg: SpecMsgCF4, f3: u8, f2: SpecContentType) -> Result<
    Seq<u8>,
    (),
> {
    spec_msg_c_f4(f3, f2).spec_serialize(msg)
}

pub fn parse_msg_c_f4(i: &[u8], f3: u8, f2: ContentType) -> (o: Result<(usize, MsgCF4<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg_c_f4(i@, f3@, f2@) matches Ok(r_) && r@ == r_,
{
    msg_c_f4(f3, f2).parse(i)
}

pub fn serialize_msg_c_f4(
    msg: MsgCF4<'_>,
    data: &mut Vec<u8>,
    pos: usize,
    f3: u8,
    f2: ContentType,
) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg_c_f4(msg@, f3@, f2@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg_c_f4(f3, f2).serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg_b(i: Seq<u8>) -> Result<(usize, SpecMsgB), ()> {
    spec_msg_b().spec_parse(i)
}

pub open spec fn serialize_spec_msg_b(msg: SpecMsgB) -> Result<Seq<u8>, ()> {
    spec_msg_b().spec_serialize(msg)
}

pub fn parse_msg_b(i: &[u8]) -> (o: Result<(usize, MsgB<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg_b(i@) matches Ok(r_) && r@ == r_,
{
    msg_b().parse(i)
}

pub fn serialize_msg_b(msg: MsgB<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg_b(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg_b().serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg_a(i: Seq<u8>) -> Result<(usize, SpecMsgA), ()> {
    spec_msg_a().spec_parse(i)
}

pub open spec fn serialize_spec_msg_a(msg: SpecMsgA) -> Result<Seq<u8>, ()> {
    spec_msg_a().spec_serialize(msg)
}

pub fn parse_msg_a(i: &[u8]) -> (o: Result<(usize, MsgA<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg_a(i@) matches Ok(r_) && r@ == r_,
{
    msg_a().parse(i)
}

pub fn serialize_msg_a(msg: MsgA<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg_a(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg_a().serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg_c(i: Seq<u8>) -> Result<(usize, SpecMsgC), ()> {
    let fst = (spec_content_type(), U8);
    let snd = |deps|
        {
            let (f2, f3) = deps;
            spec_msg_c_f4(f3, f2)
        };
    Mapped { inner: SpecDepend { fst, snd }, mapper: MsgCMapper }.spec_parse(i)
}

pub open spec fn serialize_spec_msg_c(msg: SpecMsgC) -> Result<Seq<u8>, ()> {
    let fst = (spec_content_type(), U8);
    let snd = |deps|
        {
            let (f2, f3) = deps;
            spec_msg_c_f4(f3, f2)
        };
    Mapped { inner: SpecDepend { fst, snd }, mapper: MsgCMapper }.spec_serialize(msg)
}

pub fn parse_msg_c(i: &[u8]) -> (o: Result<(usize, MsgC<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg_c(i@) matches Ok(r_) && r@ == r_,
{
    let ghost spec_snd = |deps|
        {
            let (f2, f3) = deps;
            spec_msg_c_f4(f3, f2)
        };
    let fst = (content_type(), U8);
    let snd = |deps: (ContentType, u8)| -> (o: MsgCF4Combinator)
        ensures
            o@ == spec_snd(deps@),
        {
            let (f2, f3) = deps;
            msg_c_f4(f3, f2)
        };
    Mapped { inner: Depend { fst, snd, spec_snd: Ghost(spec_snd) }, mapper: MsgCMapper }.parse(i)
}

pub fn serialize_msg_c(msg: MsgC<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg_c(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let ghost spec_snd = |deps|
        {
            let (f2, f3) = deps;
            spec_msg_c_f4(f3, f2)
        };
    let fst = (content_type(), U8);
    let snd = |deps: (ContentType, u8)| -> (o: MsgCF4Combinator)
        ensures
            o@ == spec_snd(deps@),
        {
            let (f2, f3) = deps;
            msg_c_f4(f3, f2)
        };
    Mapped { inner: Depend { fst, snd, spec_snd: Ghost(spec_snd) }, mapper: MsgCMapper }.serialize(
        msg,
        data,
        pos,
    )
}




} // verus!
    // use crate::regular::{
    //     choice::{OrdChoice, Either},
    //     bytes_n::BytesN,
    //     depend::{Depend, SpecDepend},
    //     bytes::Bytes,
    //     uints::{U8, U64},
    //     and_then::AndThen,
    // };
    // use super::*;
    //
    // spec fn spec_ord_conds(val: u8) -> OrdChoice<Cond<u8, u8, BytesN<2>>, Cond<u8, u8, BytesN<3>>> {
    //     OrdChoice(
    //         Cond { lhs: val, rhs: 0, inner: BytesN::<2> },
    //         Cond { lhs: val, rhs: 1, inner: BytesN::<3> },
    //     )
    // }
    //
    // fn ord_conds(val: u8) -> (o: OrdChoice<Cond<u8, u8, BytesN<2>>, Cond<u8, u8, BytesN<3>>>)
    //     ensures
    //         o@ == spec_ord_conds(val@),
    // {
    //     OrdChoice::new(
    //         Cond { lhs: val, rhs: 0, inner: BytesN::<2> },
    //         Cond { lhs: val, rhs: 1, inner: BytesN::<3> },
    //     )
    // }
    //
    // spec fn spec_parse_tlv(input: Seq<u8>) -> Result<
    //     (usize, ((u8, u8), Either<Seq<u8>, u64>)),
    //     (),
    // > {
    //     SpecDepend {
    //         fst: (U8, U8),
    //         snd: |deps: (u8, u8)|
    //             {
    //                 let (tag, len) = deps;
    //                 Bytes(len as usize).spec_and_then(
    //                     OrdChoice(
    //                         Cond { lhs: tag, rhs: 0, inner: BytesN::<2> },
    //                         Cond { lhs: tag, rhs: 1, inner: U64 },
    //                     ),
    //                 )
    //             },
    //     }.spec_parse(input)
    // }
    //
    // fn parse_tlv(input: &[u8]) -> (res: Result<(usize, ((u8, u8), Either<&[u8], u64>)), ()>)
    //     ensures
    //         res is Ok ==> res.unwrap()@ == spec_parse_tlv(input@).unwrap(),
    // {
    //     let ghost spec_snd = |deps: (u8, u8)|
    //         {
    //             let (tag, len) = deps;
    //             Bytes(len as usize).spec_and_then(
    //                 OrdChoice(
    //                     Cond { lhs: tag, rhs: 0, inner: BytesN::<2> },
    //                     Cond { lhs: tag, rhs: 1, inner: U64 },
    //                 ),
    //             )
    //         };
    //     Depend {
    //         fst: (U8, U8),
    //         snd: (|deps: (u8, u8)| -> (o: AndThen<
    //             Bytes,
    //             OrdChoice<Cond<u8, u8, BytesN<2>>, Cond<u8, u8, U64>>,
    //         >)
    //             ensures
    //                 o@ == spec_snd(deps@),
    //             {
    //                 let (tag, len) = deps;
    //                 Bytes(len as usize).and_then(
    //                     OrdChoice::new(
    //                         Cond { lhs: tag, rhs: 0, inner: BytesN::<2> },
    //                         Cond { lhs: tag, rhs: 1, inner: U64 },
    //                     ),
    //                 )
    //             }),
    //         spec_snd: Ghost(spec_snd),
    //     }.parse(input)
    // }
    //

}
} // verus!
