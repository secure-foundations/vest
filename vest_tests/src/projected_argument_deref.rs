#![allow(warnings)]
use vest_lib::combinators::mapped::spec::*;
use vest_lib::combinators::recursive::*;
use vest_lib::combinators::*;
use vest_lib::core::exec::bytes_eq;
use vest_lib::core::exec::input::{InputBuf, InputSlice};
use vest_lib::core::exec::output::OutputBuf;
use vest_lib::core::exec::parser::*;
use vest_lib::core::exec::serializer::*;
use vest_lib::core::exec::ParseError;
use vest_lib::core::{proof::*, spec::*};
use vest_lib::primitives::btcvarint::VarInt;
use vest_lib::primitives::leb128::ULeb128;
use vest_lib::Never;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `tag`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum Tag {
    A = 0,
    B = 1,
    Unknown(u8),
}

pub type TagSpec = Tag;

pub type TagInner = Sum<u8, u8>;

impl DeepView for Tag {
    type V = Self;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl Tag {
    pub proof fn lemma_deep_view(&self)
        ensures
            self.deep_view() == *self,
    {
        reveal(<Tag as DeepView>::deep_view);
    }

    pub open spec fn structural_valid(input: TagInner) -> bool {
        match input {
            L(x) => x == 0 || x == 1,
            R(x) => true,
        }
    }

    # [verifier::opaque]
    pub open spec fn from_structural(input: TagInner) -> Self {
        match input {
            L(x) => match x {
                0 => Self::A,
                1 => Self::B,
                _ => arbitrary(),
            },
            R(x) => Self::Unknown(x),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> TagInner {
        match self {
            Self::A => L(0),
            Self::B => L(1),
            Self::Unknown(x) => R(x),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Tag::from_structural);
        reveal(Tag::into_structural);
        match self {
            Self::A => {},
            Self::B => {},
            Self::Unknown(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: TagInner)
        requires
            Self::structural_valid(input),
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Tag::from_structural);
        reveal(Tag::into_structural);
        match input {
            L(x) => match x {
                0 => {},
                1 => {},
                _ => {
                    assert(false);
                },
            },
            R(_) => {},
        }
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TagForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TagReverse;

impl SpecMap for TagForward {
    type Input = TagInner;

    type Output = TagSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Tag::from_structural(input)
    }
}

impl SpecMap for TagReverse {
    type Input = TagSpec;

    type Output = TagInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [cfg (not (verus_keep_ghost))]
unsafe impl Structural for Tag {

}

# [doc = "data type for `header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Header {
    pub t: Tag,
}

# [verifier::ext_equal]
pub struct HeaderSpec<T0 = TagSpec> {
    pub t: T0,
}

pub type HeaderInner = TagSpec;

impl DeepView for Header {
    type V = HeaderSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        HeaderSpec { t: self.t.deep_view() }
    }
}

impl Header {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().t == self.t.deep_view(),
    {
        reveal(<Header as DeepView>::deep_view);
    }
}

impl<T0> HeaderSpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let t = input;
        Self { t }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { t } = self;
        t
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(HeaderSpec::from_structural);
        reveal(HeaderSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(HeaderSpec::from_structural);
        reveal(HeaderSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { t } => t,
            },
    {
        reveal(HeaderSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct HeaderForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct HeaderReverse;

impl SpecMap for HeaderForward {
    type Input = HeaderInner;

    type Output = HeaderSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        HeaderSpec::from_structural(input)
    }
}

impl SpecMap for HeaderReverse {
    type Input = HeaderSpec;

    type Output = HeaderInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `body`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum Body {
    A(u8),
    Default(u16),
}

# [verifier::ext_equal]
pub enum BodySpec<T0 = u8, T1 = u16> {
    A(T0),
    Default(T1),
}

pub type BodyInner = Sum<u8, u16>;

impl DeepView for Body {
    type V = BodySpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Body::A(v) => BodySpec::A(v.deep_view()),
            Body::Default(v) => BodySpec::Default(v.deep_view()),
        }
    }
}

impl Body {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                Body::A(v) => BodySpec::A(v.deep_view()),
                Body::Default(v) => BodySpec::Default(v.deep_view()),
            },
    {
        reveal(<Body as DeepView>::deep_view);
    }
}

impl<T0, T1> BodySpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, T1>) -> Self {
        match input {
            L(value) => Self::A(value),
            R(value) => Self::Default(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, T1> {
        match self {
            Self::A(value) => L(value),
            Self::Default(value) => R(value),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(BodySpec::from_structural);
        reveal(BodySpec::into_structural);
        match self {
            Self::A(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(BodySpec::from_structural);
        reveal(BodySpec::into_structural);
        match input {
            L(_) => {},
            R(_) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::A(value) => L(value),
                Self::Default(value) => R(value),
            },
    {
        reveal(BodySpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BodyForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct BodyReverse;

impl SpecMap for BodyForward {
    type Input = BodyInner;

    type Output = BodySpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        BodySpec::from_structural(input)
    }
}

impl SpecMap for BodyReverse {
    type Input = BodySpec;

    type Output = BodyInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `length_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct LengthHeader {
    pub len: u8,
}

# [verifier::ext_equal]
pub struct LengthHeaderSpec<T0 = u8> {
    pub len: T0,
}

pub type LengthHeaderInner = u8;

impl DeepView for LengthHeader {
    type V = LengthHeaderSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        LengthHeaderSpec { len: self.len.deep_view() }
    }
}

impl LengthHeader {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().len == self.len.deep_view(),
    {
        reveal(<LengthHeader as DeepView>::deep_view);
    }
}

impl<T0> LengthHeaderSpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let len = input;
        Self { len }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { len } = self;
        len
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(LengthHeaderSpec::from_structural);
        reveal(LengthHeaderSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(LengthHeaderSpec::from_structural);
        reveal(LengthHeaderSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { len } => len,
            },
    {
        reveal(LengthHeaderSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct LengthHeaderForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct LengthHeaderReverse;

impl SpecMap for LengthHeaderForward {
    type Input = LengthHeaderInner;

    type Output = LengthHeaderSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        LengthHeaderSpec::from_structural(input)
    }
}

impl SpecMap for LengthHeaderReverse {
    type Input = LengthHeaderSpec;

    type Output = LengthHeaderInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `sized_body`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct SizedBody<'i> {
    pub bytes: &'i [u8],
}

# [verifier::ext_equal]
pub struct SizedBodySpec<T0 = Seq<u8>> {
    pub bytes: T0,
}

pub type SizedBodyInner = Seq<u8>;

impl<'i> DeepView for SizedBody<'i> {
    type V = SizedBodySpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        SizedBodySpec { bytes: self.bytes.deep_view() }
    }
}

impl<'i> SizedBody<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().bytes == self.bytes.deep_view(),
    {
        reveal(<SizedBody as DeepView>::deep_view);
    }
}

impl<T0> SizedBodySpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let bytes = input;
        Self { bytes }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { bytes } = self;
        bytes
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(SizedBodySpec::from_structural);
        reveal(SizedBodySpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(SizedBodySpec::from_structural);
        reveal(SizedBodySpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { bytes } => bytes,
            },
    {
        reveal(SizedBodySpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct SizedBodyForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct SizedBodyReverse;

impl SpecMap for SizedBodyForward {
    type Input = SizedBodyInner;

    type Output = SizedBodySpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        SizedBodySpec::from_structural(input)
    }
}

impl SpecMap for SizedBodyReverse {
    type Input = SizedBodySpec;

    type Output = SizedBodyInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `dotted`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Dotted {
    pub h: Header,
    pub b: Body,
}

# [verifier::ext_equal]
pub struct DottedSpec<T0 = HeaderSpec, T1 = BodySpec> {
    pub h: T0,
    pub b: T1,
}

pub type DottedInner = (HeaderSpec, BodySpec);

impl DeepView for Dotted {
    type V = DottedSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DottedSpec { h: self.h.deep_view(), b: self.b.deep_view() }
    }
}

impl Dotted {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().h == self.h.deep_view(),
            self.deep_view().b == self.b.deep_view(),
    {
        reveal(<Dotted as DeepView>::deep_view);
    }
}

impl<T0, T1> DottedSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (h, b) = input;
        Self { h, b }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { h, b } = self;
        (h, b)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DottedSpec::from_structural);
        reveal(DottedSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DottedSpec::from_structural);
        reveal(DottedSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { h, b } => (h, b),
            },
    {
        reveal(DottedSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct DottedForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct DottedReverse;

impl SpecMap for DottedForward {
    type Input = DottedInner;

    type Output = DottedSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DottedSpec::from_structural(input)
    }
}

impl SpecMap for DottedReverse {
    type Input = DottedSpec;

    type Output = DottedInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `dotted_length`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct DottedLength<'i> {
    pub h: LengthHeader,
    pub b: SizedBody<'i>,
}

# [verifier::ext_equal]
pub struct DottedLengthSpec<T0 = LengthHeaderSpec, T1 = SizedBodySpec> {
    pub h: T0,
    pub b: T1,
}

pub type DottedLengthInner = (LengthHeaderSpec, SizedBodySpec);

impl<'i> DeepView for DottedLength<'i> {
    type V = DottedLengthSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DottedLengthSpec { h: self.h.deep_view(), b: self.b.deep_view() }
    }
}

impl<'i> DottedLength<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().h == self.h.deep_view(),
            self.deep_view().b == self.b.deep_view(),
    {
        reveal(<DottedLength as DeepView>::deep_view);
    }
}

impl<T0, T1> DottedLengthSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (h, b) = input;
        Self { h, b }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { h, b } = self;
        (h, b)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DottedLengthSpec::from_structural);
        reveal(DottedLengthSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DottedLengthSpec::from_structural);
        reveal(DottedLengthSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { h, b } => (h, b),
            },
    {
        reveal(DottedLengthSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct DottedLengthForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct DottedLengthReverse;

impl SpecMap for DottedLengthForward {
    type Input = DottedLengthInner;

    type Output = DottedLengthSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DottedLengthSpec::from_structural(input)
    }
}

impl SpecMap for DottedLengthReverse {
    type Input = DottedLengthSpec;

    type Output = DottedLengthInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `tag`."]
# [derive (Clone, Copy)]
pub struct TagFmt;

pub type TagFmtSpec = Named<
    Mapped<
        Choice<Refined<U8, PredFnSpec<u8>>, Refined<U8, PredFnSpec<u8>>>,
        BiMap<TagForward, TagReverse>,
    >,
>;

impl TagFmt {
    # [doc = "specification constructor for `tag`."]
    pub open spec fn spec_inner() -> TagFmtSpec {
        Named(
            "tag",
            Mapped {
                inner: Choice(
                    Refined(U8, |x: u8| (x == 0) || (x == 1)),
                    Refined(U8, |x: u8| (x != 0) && (x != 1)),
                ),
                mapper: BiMap(TagForward, TagReverse),
            },
        )
    }
}

# [doc = "named format combinator for `header`."]
# [derive (Clone, Copy)]
pub struct HeaderFmt;

pub type HeaderFmtSpec = Named<Mapped<TagFmt, BiMap<HeaderForward, HeaderReverse>>>;

impl HeaderFmt {
    # [doc = "specification constructor for `header`."]
    pub open spec fn spec_inner() -> HeaderFmtSpec {
        Named("header", Mapped { inner: TagFmt, mapper: BiMap(HeaderForward, HeaderReverse) })
    }
}

# [doc = "named format combinator for `body`."]
# [derive (Clone, Copy)]
pub struct BodyFmt {
    t: Tag,
}

impl BodyFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        TagFmt.consistent(self.t.deep_view())
    }

    pub closed spec fn t_spec(&self) -> TagSpec {
        self.t.deep_view()
    }

    pub closed spec fn spec(t: Tag) -> Self {
        BodyFmt { t }
    }
}

pub type BodyFmtSpec = Named<Mapped<Sum<U8, U16Le>, BiMap<BodyForward, BodyReverse>>>;

impl BodyFmt {
    # [doc = "specification constructor for `body`."]
    pub open spec fn spec_inner(t: TagSpec) -> BodyFmtSpec {
        Named(
            "body",
            Mapped {
                inner: match t {
                    TagSpec::A => L(U8),
                    _ => R(U16Le),
                },
                mapper: BiMap(BodyForward, BodyReverse),
            },
        )
    }
}

# [doc = "named format combinator for `length_header`."]
# [derive (Clone, Copy)]
pub struct LengthHeaderFmt;

pub type LengthHeaderFmtSpec = Named<Mapped<U8, BiMap<LengthHeaderForward, LengthHeaderReverse>>>;

impl LengthHeaderFmt {
    # [doc = "specification constructor for `length_header`."]
    pub open spec fn spec_inner() -> LengthHeaderFmtSpec {
        Named(
            "length_header",
            Mapped { inner: U8, mapper: BiMap(LengthHeaderForward, LengthHeaderReverse) },
        )
    }
}

# [doc = "named format combinator for `sized_body`."]
# [derive (Clone, Copy)]
pub struct SizedBodyFmt {
    len: u8,
}

impl SizedBodyFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn len_spec(&self) -> u8 {
        self.len.deep_view()
    }

    pub closed spec fn spec(len: u8) -> Self {
        SizedBodyFmt { len }
    }
}

pub type SizedBodyFmtSpec = Named<Mapped<Varied<u8>, BiMap<SizedBodyForward, SizedBodyReverse>>>;

impl SizedBodyFmt {
    # [doc = "specification constructor for `sized_body`."]
    pub open spec fn spec_inner(len: u8) -> SizedBodyFmtSpec {
        Named(
            "sized_body",
            Mapped { inner: Varied(len), mapper: BiMap(SizedBodyForward, SizedBodyReverse) },
        )
    }
}

# [doc = "named format combinator for `dotted`."]
# [derive (Clone, Copy)]
pub struct DottedFmt;

pub type DottedFmtSpec = Named<
    Mapped<Bind<HeaderFmt, spec_fn(HeaderSpec) -> BodyFmt>, BiMap<DottedForward, DottedReverse>>,
>;

impl DottedFmt {
    # [doc = "specification constructor for `dotted`."]
    pub open spec fn spec_inner() -> DottedFmtSpec {
        Named(
            "dotted",
            Mapped {
                inner: Bind(HeaderFmt, |h: HeaderSpec| BodyFmt::spec(h.t)),
                mapper: BiMap(DottedForward, DottedReverse),
            },
        )
    }
}

# [doc = "named format combinator for `dotted_length`."]
# [derive (Clone, Copy)]
pub struct DottedLengthFmt;

pub type DottedLengthFmtSpec = Named<
    Mapped<
        Bind<LengthHeaderFmt, spec_fn(LengthHeaderSpec) -> SizedBodyFmt>,
        BiMap<DottedLengthForward, DottedLengthReverse>,
    >,
>;

impl DottedLengthFmt {
    # [doc = "specification constructor for `dotted_length`."]
    pub open spec fn spec_inner() -> DottedLengthFmtSpec {
        Named(
            "dotted_length",
            Mapped {
                inner: Bind(LengthHeaderFmt, |h: LengthHeaderSpec| SizedBodyFmt::spec(h.len)),
                mapper: BiMap(DottedLengthForward, DottedLengthReverse),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for TagFmt {
        type PVal = TagSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for TagFmt {
        type Val = TagSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for TagFmt {
        type SValue = TagSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TagFmt {
        type SVal = TagSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TagFmt {
        type T = TagSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for HeaderFmt {
        type PVal = HeaderSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for HeaderFmt {
        type Val = HeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for HeaderFmt {
        type SValue = HeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for HeaderFmt {
        type SVal = HeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for HeaderFmt {
        type T = HeaderSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for BodyFmt {
        type PVal = BodySpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.t_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for BodyFmt {
        type Val = BodySpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.t_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for BodyFmt {
        type SValue = BodySpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.t_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for BodyFmt {
        type SVal = BodySpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.t_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for BodyFmt {
        type T = BodySpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.t_spec()).byte_len(v)
        }
    }

    impl SpecParser for LengthHeaderFmt {
        type PVal = LengthHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for LengthHeaderFmt {
        type Val = LengthHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for LengthHeaderFmt {
        type SValue = LengthHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for LengthHeaderFmt {
        type SVal = LengthHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for LengthHeaderFmt {
        type T = LengthHeaderSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for SizedBodyFmt {
        type PVal = SizedBodySpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.len_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for SizedBodyFmt {
        type Val = SizedBodySpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.len_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for SizedBodyFmt {
        type SValue = SizedBodySpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.len_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for SizedBodyFmt {
        type SVal = SizedBodySpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.len_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for SizedBodyFmt {
        type T = SizedBodySpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.len_spec()).byte_len(v)
        }
    }

    impl SpecParser for DottedFmt {
        type PVal = DottedSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DottedFmt {
        type Val = DottedSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for DottedFmt {
        type SValue = DottedSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DottedFmt {
        type SVal = DottedSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DottedFmt {
        type T = DottedSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for DottedLengthFmt {
        type PVal = DottedLengthSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DottedLengthFmt {
        type Val = DottedLengthSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for DottedLengthFmt {
        type SValue = DottedLengthSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DottedLengthFmt {
        type SVal = DottedLengthSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DottedLengthFmt {
        type T = DottedLengthSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use {
        vest_lib::combinators::disjoint::disjointness_lemmas,
        Tag::lemma_from_into,
        Tag::lemma_into_from,
        HeaderSpec::lemma_from_into,
        HeaderSpec::lemma_into_from,
        BodySpec::lemma_from_into,
        BodySpec::lemma_into_from,
        LengthHeaderSpec::lemma_from_into,
        LengthHeaderSpec::lemma_into_from,
        SizedBodySpec::lemma_from_into,
        SizedBodySpec::lemma_into_from,
        DottedSpec::lemma_from_into,
        DottedSpec::lemma_into_from,
        DottedLengthSpec::lemma_from_into,
        DottedLengthSpec::lemma_into_from,
    };

    impl SafeParser for TagFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TagFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TagFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TagFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TagFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TagFmt as SpecParser>::spec_parse);
            reveal(<TagFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: TagInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(Tag::structural_valid(input));
                Tag::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TagFmt as SpecParser>::spec_parse);
            reveal(<TagFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TagInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(Tag::structural_valid(input));
                Tag::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for TagFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TagFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<TagFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TagFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for TagFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TagFmt as SpecSerializer>::spec_serialize);
            reveal(<TagFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TagFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TagFmt as SpecParser>::spec_parse);
            reveal(<TagFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TagFmt as Consistency>::consistent);
            reveal(<TagFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: TagSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Tag::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TagFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TagFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: TagInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(Tag::structural_valid(input));
                Tag::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for TagFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<TagFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TagFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for TagFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TagFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TagFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for HeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<HeaderFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for HeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<HeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for HeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<HeaderFmt as SpecParser>::spec_parse);
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: HeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                HeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<HeaderFmt as SpecParser>::spec_parse);
            reveal(<HeaderFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: HeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                HeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for HeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<HeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<HeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for HeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<HeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for HeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<HeaderFmt as SpecParser>::spec_parse);
            reveal(<HeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HeaderFmt as Consistency>::consistent);
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: HeaderSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                HeaderSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for HeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<HeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: HeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                HeaderSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for HeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<HeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for HeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<HeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for BodyFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<BodyFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.t_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for BodyFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.t_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<BodyFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for BodyFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<BodyFmt as SpecParser>::spec_parse);
            reveal(<BodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.t_spec());
            assert forall|input: BodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BodySpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<BodyFmt as SpecParser>::spec_parse);
            reveal(<BodyFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.t_spec());
            assert forall|input: BodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BodySpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for BodyFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BodyFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for BodyFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<BodyFmt as SpecSerializer>::spec_serialize);
            reveal(<BodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for BodyFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<BodyFmt as SpecParser>::spec_parse);
            reveal(<BodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BodyFmt as Consistency>::consistent);
            reveal(<BodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.t_spec());
            assert forall|output: BodySpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                BodySpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for BodyFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<BodyFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.t_spec());
            assert forall|input: BodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                BodySpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for BodyFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<BodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BodyFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for BodyFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<BodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BodyFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.t_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for LengthHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<LengthHeaderFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for LengthHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<LengthHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for LengthHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<LengthHeaderFmt as SpecParser>::spec_parse);
            reveal(<LengthHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: LengthHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                LengthHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<LengthHeaderFmt as SpecParser>::spec_parse);
            reveal(<LengthHeaderFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: LengthHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                LengthHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for LengthHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<LengthHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<LengthHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LengthHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for LengthHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<LengthHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<LengthHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for LengthHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<LengthHeaderFmt as SpecParser>::spec_parse);
            reveal(<LengthHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LengthHeaderFmt as Consistency>::consistent);
            reveal(<LengthHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: LengthHeaderSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                LengthHeaderSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for LengthHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<LengthHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: LengthHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                LengthHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for LengthHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<LengthHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LengthHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for LengthHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<LengthHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<LengthHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for SizedBodyFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<SizedBodyFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.len_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for SizedBodyFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.len_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<SizedBodyFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for SizedBodyFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<SizedBodyFmt as SpecParser>::spec_parse);
            reveal(<SizedBodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert forall|input: SizedBodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                SizedBodySpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<SizedBodyFmt as SpecParser>::spec_parse);
            reveal(<SizedBodyFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.len_spec());
            assert forall|input: SizedBodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                SizedBodySpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for SizedBodyFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<SizedBodyFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<SizedBodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SizedBodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for SizedBodyFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<SizedBodyFmt as SpecSerializer>::spec_serialize);
            reveal(<SizedBodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for SizedBodyFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<SizedBodyFmt as SpecParser>::spec_parse);
            reveal(<SizedBodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SizedBodyFmt as Consistency>::consistent);
            reveal(<SizedBodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert forall|output: SizedBodySpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                SizedBodySpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for SizedBodyFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<SizedBodyFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.len_spec());
            assert forall|input: SizedBodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                SizedBodySpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for SizedBodyFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<SizedBodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SizedBodyFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for SizedBodyFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<SizedBodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SizedBodyFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DottedFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DottedFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DottedFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DottedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DottedFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<DottedFmt as SpecParser>::spec_parse);
            reveal(<DottedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DottedInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DottedSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<DottedFmt as SpecParser>::spec_parse);
            reveal(<DottedFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DottedInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DottedSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DottedFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DottedFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DottedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DottedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DottedFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<DottedFmt as SpecSerializer>::spec_serialize);
            reveal(<DottedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DottedFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<DottedFmt as SpecParser>::spec_parse);
            reveal(<DottedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DottedFmt as Consistency>::consistent);
            reveal(<DottedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DottedSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DottedSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DottedFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DottedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DottedInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DottedSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DottedFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DottedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DottedFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DottedFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DottedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DottedFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DottedLengthFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DottedLengthFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DottedLengthFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DottedLengthFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DottedLengthFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<DottedLengthFmt as SpecParser>::spec_parse);
            reveal(<DottedLengthFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DottedLengthInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DottedLengthSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<DottedLengthFmt as SpecParser>::spec_parse);
            reveal(<DottedLengthFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DottedLengthInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DottedLengthSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DottedLengthFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DottedLengthFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DottedLengthFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DottedLengthFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DottedLengthFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<DottedLengthFmt as SpecSerializer>::spec_serialize);
            reveal(<DottedLengthFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DottedLengthFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<DottedLengthFmt as SpecParser>::spec_parse);
            reveal(<DottedLengthFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DottedLengthFmt as Consistency>::consistent);
            reveal(<DottedLengthFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DottedLengthSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DottedLengthSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DottedLengthFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DottedLengthFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DottedLengthInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DottedLengthSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DottedLengthFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DottedLengthFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DottedLengthFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DottedLengthFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DottedLengthFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DottedLengthFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

}

// ============================================================
// Executable Implementations
// ============================================================
mod exec_impls {
    use super::*;

    impl<'i> Parser<&'i [u8]> for TagFmt {
        type PT = Tag;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<TagFmt as SpecParser>::spec_parse);
            reveal(<Tag as DeepView>::deep_view);
            reveal(Tag::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                0 => Tag::A,
                1 => Tag::B,
                x => Tag::Unknown(x),
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
            Ok((n, enum_val))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Tag> for TagFmt {
        fn serialize_into(&self, v: &Tag, obuf: &mut Output) {
            reveal(<TagFmt as SpecSerializer>::spec_serialize);
            reveal(<TagFmt as SpecByteLen>::byte_len);
            reveal(<Tag as DeepView>::deep_view);
            reveal(Tag::into_structural);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                Tag::A => 0,
                Tag::B => 1,
                Tag::Unknown(x) => x,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Tag> for TagFmt {
        fn prepare(&self, v: &Tag) -> Result<usize, PreSerializeError> {
            reveal(<TagFmt as SpecByteLen>::byte_len);
            reveal(<Tag as DeepView>::deep_view);
            reveal(Tag::into_structural);
            let tag = match *v {
                Tag::A => 0,
                Tag::B => 1,
                Tag::Unknown(x) if x != 0 && x != 1 => x,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for HeaderFmt {
        type PT = Header;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<HeaderFmt as SpecParser>::spec_parse);
            reveal(<Header as DeepView>::deep_view);
            reveal(HeaderSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, t) = (Named("tag", TagFmt)).parse(&rest)?;
            proof {
                t.lemma_deep_view();
            }
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Header { t };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Header> for HeaderFmt {
        fn serialize_into(&self, v: &Header, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<HeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            reveal(<Header as DeepView>::deep_view);
            reveal(HeaderSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Header { t } = v;
            proof {
                t.lemma_deep_view();
            }

            TagFmt.serialize_into(t, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Header> for HeaderFmt {
        fn prepare(&self, v: &Header) -> Result<usize, PreSerializeError> {
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            reveal(<Header as DeepView>::deep_view);
            reveal(HeaderSpec::into_structural);
            let Header { t } = v;
            proof {
                t.lemma_deep_view();
            }

            let l1 = (Named("tag", TagFmt)).prepare(t)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for BodyFmt {
        type PT = Body;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<BodyFmt as SpecParser>::spec_parse);
            reveal(<Body as DeepView>::deep_view);
            reveal(BodySpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.t.lemma_deep_view();
            }

            proof {
                self.t.lemma_deep_view();
            }

            let (n, v) = match self.t {
                Tag::A => {
                    let (n, v) = (U8).parse(&rest)?;
                    (n, Body::A(v))
                },
                _ => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, Body::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Body> for BodyFmt {
        fn serialize_into(&self, v: &Body, obuf: &mut Output) {
            reveal(<BodyFmt as SpecSerializer>::spec_serialize);
            reveal(<BodyFmt as SpecByteLen>::byte_len);
            reveal(<Body as DeepView>::deep_view);
            reveal(BodySpec::into_structural);
            proof {
                use_type_invariant(self);
                self.t.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            proof {
                self.t.lemma_deep_view();
            }

            match (self.t, v) {
                (Tag::A, Body::A(v)) => {
                    (U8).serialize_into(v, obuf);
                },
                (_, Body::Default(v)) => {
                    (U16Le).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Body> for BodyFmt {
        fn prepare(&self, v: &Body) -> Result<usize, PreSerializeError> {
            reveal(<BodyFmt as SpecByteLen>::byte_len);
            reveal(<Body as DeepView>::deep_view);
            reveal(BodySpec::into_structural);
            proof {
                use_type_invariant(self);
                self.t.lemma_deep_view();
            }

            proof {
                self.t.lemma_deep_view();
            }

            match (self.t, v) {
                (Tag::A, Body::A(v)) => (U8).prepare(v),
                (Tag::B, Body::Default(v)) => (U16Le).prepare(v),
                (Tag::Unknown(x), Body::Default(v)) if x != 0 && x != 1 => (U16Le).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for LengthHeaderFmt {
        type PT = LengthHeader;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<LengthHeaderFmt as SpecParser>::spec_parse);
            reveal(<LengthHeader as DeepView>::deep_view);
            reveal(LengthHeaderSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, len) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = LengthHeader { len };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, LengthHeader> for LengthHeaderFmt {
        fn serialize_into(&self, v: &LengthHeader, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<LengthHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<LengthHeaderFmt as SpecByteLen>::byte_len);
            reveal(<LengthHeader as DeepView>::deep_view);
            reveal(LengthHeaderSpec::into_structural);
            let ghost old_obuf = obuf@;

            let LengthHeader { len } = v;
            U8.serialize_into(len, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<LengthHeader> for LengthHeaderFmt {
        fn prepare(&self, v: &LengthHeader) -> Result<usize, PreSerializeError> {
            reveal(<LengthHeaderFmt as SpecByteLen>::byte_len);
            reveal(<LengthHeader as DeepView>::deep_view);
            reveal(LengthHeaderSpec::into_structural);
            let LengthHeader { len } = v;
            let l1 = (U8).prepare(len)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for SizedBodyFmt {
        type PT = SizedBody<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<SizedBodyFmt as SpecParser>::spec_parse);
            reveal(<SizedBody as DeepView>::deep_view);
            reveal(SizedBodySpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, bytes) = (Varied(self.len)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = SizedBody { bytes };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, SizedBody<'i>> for SizedBodyFmt {
        fn serialize_into(&self, v: &SizedBody<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<SizedBodyFmt as SpecSerializer>::spec_serialize);
            reveal(<SizedBodyFmt as SpecByteLen>::byte_len);
            reveal(<SizedBody as DeepView>::deep_view);
            reveal(SizedBodySpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let SizedBody { bytes } = v;
            Varied(self.len).serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<SizedBody<'i>> for SizedBodyFmt {
        fn prepare(&self, v: &SizedBody<'i>) -> Result<usize, PreSerializeError> {
            reveal(<SizedBodyFmt as SpecByteLen>::byte_len);
            reveal(<SizedBody as DeepView>::deep_view);
            reveal(SizedBodySpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let SizedBody { bytes } = v;
            let l1 = (Varied(self.len)).prepare(bytes)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DottedFmt {
        type PT = Dotted;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DottedFmt as SpecParser>::spec_parse);
            reveal(<Dotted as DeepView>::deep_view);
            reveal(DottedSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, h) = (Named("header", HeaderFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            proof {
                h.lemma_deep_view_fields();
                h.deep_view().lemma_into_structural_fields();
                h.t.lemma_deep_view();
            }

            let (n2, b) = (Named("body", BodyFmt { t: h.t })).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Dotted { h, b };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Dotted> for DottedFmt {
        fn serialize_into(&self, v: &Dotted, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<DottedFmt as SpecSerializer>::spec_serialize);
            reveal(<DottedFmt as SpecByteLen>::byte_len);
            reveal(<Dotted as DeepView>::deep_view);
            reveal(DottedSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Dotted { h, b } = v;
            proof {
                h.lemma_deep_view_fields();
                h.deep_view().lemma_into_structural_fields();
                h.t.lemma_deep_view();
            }

            HeaderFmt.serialize_into(h, obuf);
            BodyFmt { t: h.t }.serialize_into(b, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Dotted> for DottedFmt {
        fn prepare(&self, v: &Dotted) -> Result<usize, PreSerializeError> {
            reveal(<DottedFmt as SpecByteLen>::byte_len);
            reveal(<Dotted as DeepView>::deep_view);
            reveal(DottedSpec::into_structural);
            let Dotted { h, b } = v;
            proof {
                h.lemma_deep_view_fields();
                h.deep_view().lemma_into_structural_fields();
                h.t.lemma_deep_view();
            }

            let l1 = (Named("header", HeaderFmt)).prepare(h)?;
            let l2 = (Named("body", BodyFmt { t: h.t })).prepare(b)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DottedLengthFmt {
        type PT = DottedLength<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DottedLengthFmt as SpecParser>::spec_parse);
            reveal(<DottedLength as DeepView>::deep_view);
            reveal(DottedLengthSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, h) = (Named("length_header", LengthHeaderFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            proof {
                h.lemma_deep_view_fields();
                h.deep_view().lemma_into_structural_fields();
            }

            let (n2, b) = (Named("sized_body", SizedBodyFmt { len: h.len })).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = DottedLength { h, b };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DottedLength<'i>> for DottedLengthFmt {
        fn serialize_into(&self, v: &DottedLength<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;

            reveal(<DottedLengthFmt as SpecSerializer>::spec_serialize);
            reveal(<DottedLengthFmt as SpecByteLen>::byte_len);
            reveal(<DottedLength as DeepView>::deep_view);
            reveal(DottedLengthSpec::into_structural);
            let ghost old_obuf = obuf@;

            let DottedLength { h, b } = v;
            proof {
                h.lemma_deep_view_fields();
                h.deep_view().lemma_into_structural_fields();
            }

            LengthHeaderFmt.serialize_into(h, obuf);
            SizedBodyFmt { len: h.len }.serialize_into(b, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DottedLength<'i>> for DottedLengthFmt {
        fn prepare(&self, v: &DottedLength<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DottedLengthFmt as SpecByteLen>::byte_len);
            reveal(<DottedLength as DeepView>::deep_view);
            reveal(DottedLengthSpec::into_structural);
            let DottedLength { h, b } = v;
            proof {
                h.lemma_deep_view_fields();
                h.deep_view().lemma_into_structural_fields();
            }

            let l1 = (Named("length_header", LengthHeaderFmt)).prepare(h)?;
            let l2 = (Named("sized_body", SizedBodyFmt { len: h.len })).prepare(b)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

}

} // verus!
