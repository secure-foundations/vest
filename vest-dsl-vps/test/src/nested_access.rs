#![allow(warnings)]
use vps_lib::combinators::mapped::spec::*;
use vps_lib::combinators::recursive::*;
use vps_lib::combinators::*;
use vps_lib::core::exec::bytes_eq;
use vps_lib::core::exec::input::{InputBuf, InputSlice};
use vps_lib::core::exec::output::OutputBuf;
use vps_lib::core::exec::parser::*;
use vps_lib::core::exec::serializer::*;
use vps_lib::core::exec::ParseError;
use vps_lib::core::{proof::*, spec::*};
use vps_lib::primitives::btcvarint::VarInt;
use vps_lib::primitives::leb128::ULeb128;
use vps_lib::Never;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `generic_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct GenericHeader {
    pub next_type: u8,
    pub reserved: u8,
    pub payload_length: u32,
}

# [verifier::ext_equal]
pub struct GenericHeaderSpec<T0 = u8, T1 = u8, T2 = u32> {
    pub next_type: T0,
    pub reserved: T1,
    pub payload_length: T2,
}

pub type GenericHeaderInner = (u8, (u8, u32));

impl DeepView for GenericHeader {
    type V = GenericHeaderSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        GenericHeaderSpec {
            next_type: self.next_type.deep_view(),
            reserved: self.reserved.deep_view(),
            payload_length: self.payload_length.deep_view(),
        }
    }
}

impl GenericHeader {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().next_type == self.next_type.deep_view(),
            self.deep_view().reserved == self.reserved.deep_view(),
            self.deep_view().payload_length == self.payload_length.deep_view(),
    {
        reveal(<GenericHeader as DeepView>::deep_view);
    }
}

impl<T0, T1, T2> GenericHeaderSpec<T0, T1, T2> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, T2))) -> Self {
        let (next_type, (reserved, payload_length)) = input;
        Self { next_type, reserved, payload_length }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, T2)) {
        let Self { next_type, reserved, payload_length } = self;
        (next_type, (reserved, payload_length))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(GenericHeaderSpec::from_structural);
        reveal(GenericHeaderSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, T2)))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(GenericHeaderSpec::from_structural);
        reveal(GenericHeaderSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { next_type, reserved, payload_length } => (
                    next_type,
                    (reserved, payload_length),
                ),
            },
    {
        reveal(GenericHeaderSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct GenericHeaderForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct GenericHeaderReverse;

impl SpecMap for GenericHeaderForward {
    type Input = GenericHeaderInner;

    type Output = GenericHeaderSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        GenericHeaderSpec::from_structural(input)
    }
}

impl SpecMap for GenericHeaderReverse {
    type Input = GenericHeaderSpec;

    type Output = GenericHeaderInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `payload_with_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct PayloadWithHeader<'i> {
    pub hdr: GenericHeader,
    pub body: &'i [u8],
}

# [verifier::ext_equal]
pub struct PayloadWithHeaderSpec<T0 = GenericHeaderSpec, T1 = Seq<u8>> {
    pub hdr: T0,
    pub body: T1,
}

pub type PayloadWithHeaderInner = (GenericHeaderSpec, Seq<u8>);

impl<'i> DeepView for PayloadWithHeader<'i> {
    type V = PayloadWithHeaderSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        PayloadWithHeaderSpec { hdr: self.hdr.deep_view(), body: self.body.deep_view() }
    }
}

impl<'i> PayloadWithHeader<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().hdr == self.hdr.deep_view(),
            self.deep_view().body == self.body.deep_view(),
    {
        reveal(<PayloadWithHeader as DeepView>::deep_view);
    }
}

impl<T0, T1> PayloadWithHeaderSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (hdr, body) = input;
        Self { hdr, body }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { hdr, body } = self;
        (hdr, body)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(PayloadWithHeaderSpec::from_structural);
        reveal(PayloadWithHeaderSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(PayloadWithHeaderSpec::from_structural);
        reveal(PayloadWithHeaderSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { hdr, body } => (hdr, body),
            },
    {
        reveal(PayloadWithHeaderSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct PayloadWithHeaderForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct PayloadWithHeaderReverse;

impl SpecMap for PayloadWithHeaderForward {
    type Input = PayloadWithHeaderInner;

    type Output = PayloadWithHeaderSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        PayloadWithHeaderSpec::from_structural(input)
    }
}

impl SpecMap for PayloadWithHeaderReverse {
    type Input = PayloadWithHeaderSpec;

    type Output = PayloadWithHeaderInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `outer_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct OuterHeader {
    pub magic: u32,
    pub inner: GenericHeader,
}

# [verifier::ext_equal]
pub struct OuterHeaderSpec<T0 = u32, T1 = GenericHeaderSpec> {
    pub magic: T0,
    pub inner: T1,
}

pub type OuterHeaderInner = (u32, GenericHeaderSpec);

impl DeepView for OuterHeader {
    type V = OuterHeaderSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        OuterHeaderSpec { magic: self.magic.deep_view(), inner: self.inner.deep_view() }
    }
}

impl OuterHeader {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().magic == self.magic.deep_view(),
            self.deep_view().inner == self.inner.deep_view(),
    {
        reveal(<OuterHeader as DeepView>::deep_view);
    }
}

impl<T0, T1> OuterHeaderSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (magic, inner) = input;
        Self { magic, inner }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { magic, inner } = self;
        (magic, inner)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(OuterHeaderSpec::from_structural);
        reveal(OuterHeaderSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(OuterHeaderSpec::from_structural);
        reveal(OuterHeaderSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { magic, inner } => (magic, inner),
            },
    {
        reveal(OuterHeaderSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct OuterHeaderForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct OuterHeaderReverse;

impl SpecMap for OuterHeaderForward {
    type Input = OuterHeaderInner;

    type Output = OuterHeaderSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        OuterHeaderSpec::from_structural(input)
    }
}

impl SpecMap for OuterHeaderReverse {
    type Input = OuterHeaderSpec;

    type Output = OuterHeaderInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `deep_nested`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct DeepNested<'i> {
    pub outer: OuterHeader,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct DeepNestedSpec<T0 = OuterHeaderSpec, T1 = Seq<u8>> {
    pub outer: T0,
    pub data: T1,
}

pub type DeepNestedInner = (OuterHeaderSpec, Seq<u8>);

impl<'i> DeepView for DeepNested<'i> {
    type V = DeepNestedSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DeepNestedSpec { outer: self.outer.deep_view(), data: self.data.deep_view() }
    }
}

impl<'i> DeepNested<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().outer == self.outer.deep_view(),
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<DeepNested as DeepView>::deep_view);
    }
}

impl<T0, T1> DeepNestedSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (outer, data) = input;
        Self { outer, data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { outer, data } = self;
        (outer, data)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DeepNestedSpec::from_structural);
        reveal(DeepNestedSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DeepNestedSpec::from_structural);
        reveal(DeepNestedSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { outer, data } => (outer, data),
            },
    {
        reveal(DeepNestedSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct DeepNestedForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct DeepNestedReverse;

impl SpecMap for DeepNestedForward {
    type Input = DeepNestedInner;

    type Output = DeepNestedSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DeepNestedSpec::from_structural(input)
    }
}

impl SpecMap for DeepNestedReverse {
    type Input = DeepNestedSpec;

    type Output = DeepNestedInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nested_complex`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct NestedComplex<'i> {
    pub flag: u32,
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct NestedComplexSpec<T0 = u32, T1 = Seq<u8>> {
    pub flag: T0,
    pub data: T1,
}

pub type NestedComplexInner = (u32, Seq<u8>);

impl<'i> DeepView for NestedComplex<'i> {
    type V = NestedComplexSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        NestedComplexSpec { flag: self.flag.deep_view(), data: self.data.deep_view() }
    }
}

impl<'i> NestedComplex<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().flag == self.flag.deep_view(),
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<NestedComplex as DeepView>::deep_view);
    }
}

impl<T0, T1> NestedComplexSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (flag, data) = input;
        Self { flag, data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { flag, data } = self;
        (flag, data)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(NestedComplexSpec::from_structural);
        reveal(NestedComplexSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(NestedComplexSpec::from_structural);
        reveal(NestedComplexSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { flag, data } => (flag, data),
            },
    {
        reveal(NestedComplexSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedComplexForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedComplexReverse;

impl SpecMap for NestedComplexForward {
    type Input = NestedComplexInner;

    type Output = NestedComplexSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        NestedComplexSpec::from_structural(input)
    }
}

impl SpecMap for NestedComplexReverse {
    type Input = NestedComplexSpec;

    type Output = NestedComplexInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `combined_example`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CombinedExample<'i> {
    pub header: GenericHeader,
    pub body: &'i [u8],
}

# [verifier::ext_equal]
pub struct CombinedExampleSpec<T0 = GenericHeaderSpec, T1 = Seq<u8>> {
    pub header: T0,
    pub body: T1,
}

pub type CombinedExampleInner = (GenericHeaderSpec, Seq<u8>);

impl<'i> DeepView for CombinedExample<'i> {
    type V = CombinedExampleSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CombinedExampleSpec { header: self.header.deep_view(), body: self.body.deep_view() }
    }
}

impl<'i> CombinedExample<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().header == self.header.deep_view(),
            self.deep_view().body == self.body.deep_view(),
    {
        reveal(<CombinedExample as DeepView>::deep_view);
    }
}

impl<T0, T1> CombinedExampleSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (header, body) = input;
        Self { header, body }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { header, body } = self;
        (header, body)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CombinedExampleSpec::from_structural);
        reveal(CombinedExampleSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CombinedExampleSpec::from_structural);
        reveal(CombinedExampleSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { header, body } => (header, body),
            },
    {
        reveal(CombinedExampleSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CombinedExampleForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CombinedExampleReverse;

impl SpecMap for CombinedExampleForward {
    type Input = CombinedExampleInner;

    type Output = CombinedExampleSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CombinedExampleSpec::from_structural(input)
    }
}

impl SpecMap for CombinedExampleReverse {
    type Input = CombinedExampleSpec;

    type Output = CombinedExampleInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `final_msg`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct FinalMsg<'i> {
    pub total_len: u32,
    pub body: CombinedExample<'i>,
    pub hdr_payload: PayloadWithHeader<'i>,
    pub nested: NestedComplex<'i>,
}

# [verifier::ext_equal]
pub struct FinalMsgSpec<
    T0 = u32,
    T1 = CombinedExampleSpec,
    T2 = PayloadWithHeaderSpec,
    T3 = NestedComplexSpec,
> {
    pub total_len: T0,
    pub body: T1,
    pub hdr_payload: T2,
    pub nested: T3,
}

pub type FinalMsgInner = (u32, (CombinedExampleSpec, (PayloadWithHeaderSpec, NestedComplexSpec)));

impl<'i> DeepView for FinalMsg<'i> {
    type V = FinalMsgSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        FinalMsgSpec {
            total_len: self.total_len.deep_view(),
            body: self.body.deep_view(),
            hdr_payload: self.hdr_payload.deep_view(),
            nested: self.nested.deep_view(),
        }
    }
}

impl<'i> FinalMsg<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().total_len == self.total_len.deep_view(),
            self.deep_view().body == self.body.deep_view(),
            self.deep_view().hdr_payload == self.hdr_payload.deep_view(),
            self.deep_view().nested == self.nested.deep_view(),
    {
        reveal(<FinalMsg as DeepView>::deep_view);
    }
}

impl<T0, T1, T2, T3> FinalMsgSpec<T0, T1, T2, T3> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, (T2, T3)))) -> Self {
        let (total_len, (body, (hdr_payload, nested))) = input;
        Self { total_len, body, hdr_payload, nested }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, T3))) {
        let Self { total_len, body, hdr_payload, nested } = self;
        (total_len, (body, (hdr_payload, nested)))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(FinalMsgSpec::from_structural);
        reveal(FinalMsgSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, (T2, T3))))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(FinalMsgSpec::from_structural);
        reveal(FinalMsgSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { total_len, body, hdr_payload, nested } => (
                    total_len,
                    (body, (hdr_payload, nested)),
                ),
            },
    {
        reveal(FinalMsgSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct FinalMsgForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct FinalMsgReverse;

impl SpecMap for FinalMsgForward {
    type Input = FinalMsgInner;

    type Output = FinalMsgSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        FinalMsgSpec::from_structural(input)
    }
}

impl SpecMap for FinalMsgReverse {
    type Input = FinalMsgSpec;

    type Output = FinalMsgInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `generic_header`."]
# [derive (Clone, Copy)]
pub struct GenericHeaderFmt;

pub type GenericHeaderFmtSpec = Named<
    Mapped<
        Pair<U8, Pair<U8, Refined<U32Le, PredFnSpec<u32>>>>,
        BiMap<GenericHeaderForward, GenericHeaderReverse>,
    >,
>;

impl GenericHeaderFmt {
    # [doc = "specification constructor for `generic_header`."]
    pub open spec fn spec_inner() -> GenericHeaderFmtSpec {
        Named(
            "generic_header",
            Mapped {
                inner: Pair(U8, Pair(U8, Refined(U32Le, |x: u32| x >= 8 && x <= 65535))),
                mapper: BiMap(GenericHeaderForward, GenericHeaderReverse),
            },
        )
    }
}

# [doc = "named format combinator for `payload_with_header`."]
# [derive (Clone, Copy)]
pub struct PayloadWithHeaderFmt;

pub type PayloadWithHeaderFmtSpec = Named<
    Mapped<
        Bind<GenericHeaderFmt, spec_fn(GenericHeaderSpec) -> Varied<u32>>,
        BiMap<PayloadWithHeaderForward, PayloadWithHeaderReverse>,
    >,
>;

impl PayloadWithHeaderFmt {
    # [doc = "specification constructor for `payload_with_header`."]
    pub open spec fn spec_inner() -> PayloadWithHeaderFmtSpec {
        Named(
            "payload_with_header",
            Mapped {
                inner: Bind(
                    GenericHeaderFmt,
                    |hdr: GenericHeaderSpec| Varied(((hdr.payload_length - 4) as u32)),
                ),
                mapper: BiMap(PayloadWithHeaderForward, PayloadWithHeaderReverse),
            },
        )
    }
}

# [doc = "named format combinator for `outer_header`."]
# [derive (Clone, Copy)]
pub struct OuterHeaderFmt;

pub type OuterHeaderFmtSpec = Named<
    Mapped<Pair<U32Le, GenericHeaderFmt>, BiMap<OuterHeaderForward, OuterHeaderReverse>>,
>;

impl OuterHeaderFmt {
    # [doc = "specification constructor for `outer_header`."]
    pub open spec fn spec_inner() -> OuterHeaderFmtSpec {
        Named(
            "outer_header",
            Mapped {
                inner: Pair(U32Le, GenericHeaderFmt),
                mapper: BiMap(OuterHeaderForward, OuterHeaderReverse),
            },
        )
    }
}

# [doc = "named format combinator for `deep_nested`."]
# [derive (Clone, Copy)]
pub struct DeepNestedFmt;

pub type DeepNestedFmtSpec = Named<
    Mapped<
        Bind<OuterHeaderFmt, spec_fn(OuterHeaderSpec) -> Varied<u32>>,
        BiMap<DeepNestedForward, DeepNestedReverse>,
    >,
>;

impl DeepNestedFmt {
    # [doc = "specification constructor for `deep_nested`."]
    pub open spec fn spec_inner() -> DeepNestedFmtSpec {
        Named(
            "deep_nested",
            Mapped {
                inner: Bind(
                    OuterHeaderFmt,
                    |outer: OuterHeaderSpec| Varied(((outer.inner.payload_length - 8) as u32)),
                ),
                mapper: BiMap(DeepNestedForward, DeepNestedReverse),
            },
        )
    }
}

# [doc = "named format combinator for `nested_complex`."]
# [derive (Clone, Copy)]
pub struct NestedComplexFmt<'i> {
    hdr_payload: PayloadWithHeader<'i>,
}

impl<'i> NestedComplexFmt<'i> {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        PayloadWithHeaderFmt.consistent(self.hdr_payload.deep_view())
    }

    pub closed spec fn hdr_payload_spec(&self) -> PayloadWithHeaderSpec {
        self.hdr_payload.deep_view()
    }

    pub closed spec fn spec(hdr_payload: PayloadWithHeader<'i>) -> Self {
        NestedComplexFmt { hdr_payload }
    }
}

pub type NestedComplexFmtSpec = Named<
    Mapped<Pair<Const<U32Le, u32>, Varied<u32>>, BiMap<NestedComplexForward, NestedComplexReverse>>,
>;

impl<'i> NestedComplexFmt<'i> {
    # [doc = "specification constructor for `nested_complex`."]
    pub open spec fn spec_inner(hdr_payload: PayloadWithHeaderSpec) -> NestedComplexFmtSpec {
        Named(
            "nested_complex",
            Mapped {
                inner: Pair(Const(U32Le, 0), Varied(((hdr_payload.hdr.payload_length - 8) as u32))),
                mapper: BiMap(NestedComplexForward, NestedComplexReverse),
            },
        )
    }
}

# [doc = "named format combinator for `combined_example`."]
# [derive (Clone, Copy)]
pub struct CombinedExampleFmt {
    total_len: u32,
}

impl CombinedExampleFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.total_len >= 65535 && self.total_len <= 4294967295
    }

    pub closed spec fn total_len_spec(&self) -> u32 {
        self.total_len.deep_view()
    }

    pub closed spec fn spec(total_len: u32) -> Self {
        CombinedExampleFmt { total_len }
    }
}

pub type CombinedExampleFmtSpec = Named<
    Mapped<
        Bind<GenericHeaderFmt, spec_fn(GenericHeaderSpec) -> Varied<u32>>,
        BiMap<CombinedExampleForward, CombinedExampleReverse>,
    >,
>;

impl CombinedExampleFmt {
    # [doc = "specification constructor for `combined_example`."]
    pub open spec fn spec_inner(total_len: u32) -> CombinedExampleFmtSpec {
        Named(
            "combined_example",
            Mapped {
                inner: Bind(
                    GenericHeaderFmt,
                    |header: GenericHeaderSpec|
                        Varied(((total_len - header.payload_length) as u32)),
                ),
                mapper: BiMap(CombinedExampleForward, CombinedExampleReverse),
            },
        )
    }
}

# [doc = "named format combinator for `final_msg`."]
# [derive (Clone, Copy)]
pub struct FinalMsgFmt;

pub type FinalMsgFmtSpec = Named<
    Mapped<
        Bind<
            Refined<U32Le, PredFnSpec<u32>>,
            spec_fn(u32) -> Pair<
                CombinedExampleFmt,
                Bind<PayloadWithHeaderFmt, spec_fn(PayloadWithHeaderSpec) -> NestedComplexFmtSpec>,
            >,
        >,
        BiMap<FinalMsgForward, FinalMsgReverse>,
    >,
>;

impl FinalMsgFmt {
    # [doc = "specification constructor for `final_msg`."]
    pub open spec fn spec_inner() -> FinalMsgFmtSpec {
        Named(
            "final_msg",
            Mapped {
                inner: Bind(
                    Refined(U32Le, |x: u32| x >= 16777215 && x <= 4294967295),
                    |total_len: u32|
                        Pair(
                            CombinedExampleFmt::spec(total_len),
                            Bind(
                                PayloadWithHeaderFmt,
                                |hdr_payload: PayloadWithHeaderSpec|
                                    NestedComplexFmt::spec_inner(hdr_payload),
                            ),
                        ),
                ),
                mapper: BiMap(FinalMsgForward, FinalMsgReverse),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for GenericHeaderFmt {
        type PVal = GenericHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for GenericHeaderFmt {
        type Val = GenericHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for GenericHeaderFmt {
        type SValue = GenericHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for GenericHeaderFmt {
        type SVal = GenericHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for GenericHeaderFmt {
        type T = GenericHeaderSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for PayloadWithHeaderFmt {
        type PVal = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for PayloadWithHeaderFmt {
        type Val = PayloadWithHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for PayloadWithHeaderFmt {
        type SValue = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for PayloadWithHeaderFmt {
        type SVal = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for PayloadWithHeaderFmt {
        type T = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for OuterHeaderFmt {
        type PVal = OuterHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for OuterHeaderFmt {
        type Val = OuterHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for OuterHeaderFmt {
        type SValue = OuterHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for OuterHeaderFmt {
        type SVal = OuterHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for OuterHeaderFmt {
        type T = OuterHeaderSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for DeepNestedFmt {
        type PVal = DeepNestedSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DeepNestedFmt {
        type Val = DeepNestedSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for DeepNestedFmt {
        type SValue = DeepNestedSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DeepNestedFmt {
        type SVal = DeepNestedSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DeepNestedFmt {
        type T = DeepNestedSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<'i> SpecParser for NestedComplexFmt<'i> {
        type PVal = NestedComplexSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.hdr_payload_spec()).spec_parse(ibuf)
        }
    }

    impl<'i> Consistency for NestedComplexFmt<'i> {
        type Val = NestedComplexSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.hdr_payload_spec()).consistent(v)
        }
    }

    impl<'i> SpecSerializerDps for NestedComplexFmt<'i> {
        type SValue = NestedComplexSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.hdr_payload_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl<'i> SpecSerializer for NestedComplexFmt<'i> {
        type SVal = NestedComplexSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.hdr_payload_spec()).spec_serialize(v)
        }
    }

    impl<'i> SpecByteLen for NestedComplexFmt<'i> {
        type T = NestedComplexSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.hdr_payload_spec()).byte_len(v)
        }
    }

    impl SpecParser for CombinedExampleFmt {
        type PVal = CombinedExampleSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.total_len_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CombinedExampleFmt {
        type Val = CombinedExampleSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.total_len_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CombinedExampleFmt {
        type SValue = CombinedExampleSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.total_len_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CombinedExampleFmt {
        type SVal = CombinedExampleSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.total_len_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CombinedExampleFmt {
        type T = CombinedExampleSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.total_len_spec()).byte_len(v)
        }
    }

    impl SpecParser for FinalMsgFmt {
        type PVal = FinalMsgSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for FinalMsgFmt {
        type Val = FinalMsgSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for FinalMsgFmt {
        type SValue = FinalMsgSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for FinalMsgFmt {
        type SVal = FinalMsgSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for FinalMsgFmt {
        type T = FinalMsgSpec;

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
        vps_lib::combinators::disjoint::disjointness_lemmas,
        GenericHeaderSpec::lemma_from_into,
        GenericHeaderSpec::lemma_into_from,
        PayloadWithHeaderSpec::lemma_from_into,
        PayloadWithHeaderSpec::lemma_into_from,
        OuterHeaderSpec::lemma_from_into,
        OuterHeaderSpec::lemma_into_from,
        DeepNestedSpec::lemma_from_into,
        DeepNestedSpec::lemma_into_from,
        NestedComplexSpec::lemma_from_into,
        NestedComplexSpec::lemma_into_from,
        CombinedExampleSpec::lemma_from_into,
        CombinedExampleSpec::lemma_into_from,
        FinalMsgSpec::lemma_from_into,
        FinalMsgSpec::lemma_into_from,
    };

    impl SafeParser for GenericHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for GenericHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for GenericHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: GenericHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                GenericHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            reveal(<GenericHeaderFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: GenericHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                GenericHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for GenericHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for GenericHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for GenericHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as Consistency>::consistent);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: GenericHeaderSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                GenericHeaderSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for GenericHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: GenericHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                GenericHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for GenericHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for GenericHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<GenericHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for PayloadWithHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for PayloadWithHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for PayloadWithHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: PayloadWithHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                PayloadWithHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeaderFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: PayloadWithHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                PayloadWithHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for PayloadWithHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for PayloadWithHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for PayloadWithHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as Consistency>::consistent);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: PayloadWithHeaderSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                PayloadWithHeaderSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for PayloadWithHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: PayloadWithHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                PayloadWithHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for PayloadWithHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for PayloadWithHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for OuterHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for OuterHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for OuterHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: OuterHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                OuterHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            reveal(<OuterHeaderFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: OuterHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                OuterHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for OuterHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for OuterHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for OuterHeaderFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as Consistency>::consistent);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: OuterHeaderSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                OuterHeaderSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for OuterHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: OuterHeaderInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                OuterHeaderSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for OuterHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for OuterHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<OuterHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DeepNestedFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DeepNestedFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DeepNestedFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DeepNestedInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DeepNestedSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            reveal(<DeepNestedFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DeepNestedInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DeepNestedSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DeepNestedFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DeepNestedFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DeepNestedFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as Consistency>::consistent);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DeepNestedSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DeepNestedSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DeepNestedFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DeepNestedInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DeepNestedSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DeepNestedFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DeepNestedFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DeepNestedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<'i> SafeParser for NestedComplexFmt<'i> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner(self.hdr_payload_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl<'i> Productive for NestedComplexFmt<'i> {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.hdr_payload_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            let fmt = Self::spec_inner(self.hdr_payload_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl<'i> SoundParser for NestedComplexFmt<'i> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.hdr_payload_spec());
            assert forall|input: NestedComplexInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedComplexSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.hdr_payload_spec());
            assert forall|input: NestedComplexInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedComplexSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<'i> NonTailFmt for NestedComplexFmt<'i> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.hdr_payload_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.hdr_payload_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<'i> GoodSerializer for NestedComplexFmt<'i> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.hdr_payload_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<'i> SPRoundTripDps for NestedComplexFmt<'i> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.hdr_payload_spec());
            assert forall|output: NestedComplexSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                NestedComplexSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<'i> NonMalleable for NestedComplexFmt<'i> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.hdr_payload_spec());
            assert forall|input: NestedComplexInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedComplexSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<'i> EquivSerializersGeneral for NestedComplexFmt<'i> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.hdr_payload_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<'i> EquivSerializers for NestedComplexFmt<'i> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.hdr_payload_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CombinedExampleFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.total_len_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CombinedExampleFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.total_len_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.total_len_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CombinedExampleFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.total_len_spec());
            assert forall|input: CombinedExampleInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CombinedExampleSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            reveal(<CombinedExampleFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.total_len_spec());
            assert forall|input: CombinedExampleInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CombinedExampleSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CombinedExampleFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.total_len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.total_len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CombinedExampleFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.total_len_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CombinedExampleFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as Consistency>::consistent);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.total_len_spec());
            assert forall|output: CombinedExampleSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CombinedExampleSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CombinedExampleFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.total_len_spec());
            assert forall|input: CombinedExampleInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CombinedExampleSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CombinedExampleFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.total_len_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CombinedExampleFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CombinedExampleFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.total_len_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for FinalMsgFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for FinalMsgFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for FinalMsgFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            reveal(<FinalMsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: FinalMsgInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                FinalMsgSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            reveal(<FinalMsgFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: FinalMsgInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                FinalMsgSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for FinalMsgFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FinalMsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for FinalMsgFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<FinalMsgFmt as SpecSerializer>::spec_serialize);
            reveal(<FinalMsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for FinalMsgFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            reveal(<FinalMsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FinalMsgFmt as Consistency>::consistent);
            reveal(<FinalMsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: FinalMsgSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                FinalMsgSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for FinalMsgFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: FinalMsgInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                FinalMsgSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for FinalMsgFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<FinalMsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FinalMsgFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for FinalMsgFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<FinalMsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FinalMsgFmt as SpecSerializer>::spec_serialize);
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

    impl<'i> Parser<&'i [u8]> for GenericHeaderFmt {
        type PT = GenericHeader;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<GenericHeaderFmt as SpecParser>::spec_parse);
            reveal(<GenericHeader as DeepView>::deep_view);
            reveal(GenericHeaderSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, next_type) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, reserved) = (U8).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, payload_length) = (U32Le).parse(&rest)?;
            if !(payload_length >= 8 && payload_length <= 65535) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = GenericHeader { next_type, reserved, payload_length };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, GenericHeader> for GenericHeaderFmt {
        fn serialize_into(&self, v: &GenericHeader, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<GenericHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            reveal(<GenericHeader as DeepView>::deep_view);
            reveal(GenericHeaderSpec::into_structural);
            let ghost old_obuf = obuf@;

            let GenericHeader { next_type, reserved, payload_length } = v;
            U8.serialize_into(next_type, obuf);
            U8.serialize_into(reserved, obuf);
            U32Le.serialize_into(payload_length, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<GenericHeader> for GenericHeaderFmt {
        fn prepare(&self, v: &GenericHeader) -> Result<usize, PreSerializeError> {
            reveal(<GenericHeaderFmt as SpecByteLen>::byte_len);
            reveal(<GenericHeader as DeepView>::deep_view);
            reveal(GenericHeaderSpec::into_structural);
            let GenericHeader { next_type, reserved, payload_length } = v;
            let l1 = (U8).prepare(next_type)?;
            let l2 = (U8).prepare(reserved)?;
            let l3 = {
                if !(*payload_length >= 8 && *payload_length <= 65535) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (U32Le).prepare(payload_length)
                }
            }?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for PayloadWithHeaderFmt {
        type PT = PayloadWithHeader<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeader as DeepView>::deep_view);
            reveal(PayloadWithHeaderSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = (Named("generic_header", GenericHeaderFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            proof {
                hdr.lemma_deep_view_fields();
                hdr.deep_view().lemma_into_structural_fields();
            }

            let (n2, body) = (Varied((hdr.payload_length - 4))).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = PayloadWithHeader { hdr, body };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, PayloadWithHeader<'i>> for PayloadWithHeaderFmt {
        fn serialize_into(&self, v: &PayloadWithHeader<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            reveal(<PayloadWithHeader as DeepView>::deep_view);
            reveal(PayloadWithHeaderSpec::into_structural);
            let ghost old_obuf = obuf@;

            let PayloadWithHeader { hdr, body } = v;
            proof {
                hdr.lemma_deep_view_fields();
                hdr.deep_view().lemma_into_structural_fields();
            }

            GenericHeaderFmt.serialize_into(hdr, obuf);
            Varied((hdr.payload_length - 4)).serialize_into(*body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<PayloadWithHeader<'i>> for PayloadWithHeaderFmt {
        fn prepare(&self, v: &PayloadWithHeader<'i>) -> Result<usize, PreSerializeError> {
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            reveal(<PayloadWithHeader as DeepView>::deep_view);
            reveal(PayloadWithHeaderSpec::into_structural);
            let PayloadWithHeader { hdr, body } = v;
            proof {
                hdr.lemma_deep_view_fields();
                hdr.deep_view().lemma_into_structural_fields();
            }

            let l1 = (Named("generic_header", GenericHeaderFmt)).prepare(hdr)?;
            let l2 = (Varied((hdr.payload_length - 4))).prepare(body)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for OuterHeaderFmt {
        type PT = OuterHeader;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<OuterHeaderFmt as SpecParser>::spec_parse);
            reveal(<OuterHeader as DeepView>::deep_view);
            reveal(OuterHeaderSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, magic) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, inner) = (Named("generic_header", GenericHeaderFmt)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = OuterHeader { magic, inner };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, OuterHeader> for OuterHeaderFmt {
        fn serialize_into(&self, v: &OuterHeader, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<OuterHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            reveal(<OuterHeader as DeepView>::deep_view);
            reveal(OuterHeaderSpec::into_structural);
            let ghost old_obuf = obuf@;

            let OuterHeader { magic, inner } = v;
            U32Le.serialize_into(magic, obuf);
            GenericHeaderFmt.serialize_into(inner, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<OuterHeader> for OuterHeaderFmt {
        fn prepare(&self, v: &OuterHeader) -> Result<usize, PreSerializeError> {
            reveal(<OuterHeaderFmt as SpecByteLen>::byte_len);
            reveal(<OuterHeader as DeepView>::deep_view);
            reveal(OuterHeaderSpec::into_structural);
            let OuterHeader { magic, inner } = v;
            let l1 = (U32Le).prepare(magic)?;
            let l2 = (Named("generic_header", GenericHeaderFmt)).prepare(inner)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DeepNestedFmt {
        type PT = DeepNested<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DeepNestedFmt as SpecParser>::spec_parse);
            reveal(<DeepNested as DeepView>::deep_view);
            reveal(DeepNestedSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, outer) = (Named("outer_header", OuterHeaderFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            proof {
                outer.lemma_deep_view_fields();
                outer.deep_view().lemma_into_structural_fields();
                outer.inner.lemma_deep_view_fields();
                outer.inner.deep_view().lemma_into_structural_fields();
            }

            let (n2, data) = (Varied((outer.inner.payload_length - 8))).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = DeepNested { outer, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DeepNested<'i>> for DeepNestedFmt {
        fn serialize_into(&self, v: &DeepNested<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<DeepNestedFmt as SpecSerializer>::spec_serialize);
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            reveal(<DeepNested as DeepView>::deep_view);
            reveal(DeepNestedSpec::into_structural);
            let ghost old_obuf = obuf@;

            let DeepNested { outer, data } = v;
            proof {
                outer.lemma_deep_view_fields();
                outer.deep_view().lemma_into_structural_fields();
                outer.inner.lemma_deep_view_fields();
                outer.inner.deep_view().lemma_into_structural_fields();
            }

            OuterHeaderFmt.serialize_into(outer, obuf);
            Varied((outer.inner.payload_length - 8)).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DeepNested<'i>> for DeepNestedFmt {
        fn prepare(&self, v: &DeepNested<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DeepNestedFmt as SpecByteLen>::byte_len);
            reveal(<DeepNested as DeepView>::deep_view);
            reveal(DeepNestedSpec::into_structural);
            let DeepNested { outer, data } = v;
            proof {
                outer.lemma_deep_view_fields();
                outer.deep_view().lemma_into_structural_fields();
                outer.inner.lemma_deep_view_fields();
                outer.inner.deep_view().lemma_into_structural_fields();
            }

            let l1 = (Named("outer_header", OuterHeaderFmt)).prepare(outer)?;
            let l2 = (Varied((outer.inner.payload_length - 8))).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for NestedComplexFmt<'i> {
        type PT = NestedComplex<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NestedComplexFmt as SpecParser>::spec_parse);
            reveal(<NestedComplex as DeepView>::deep_view);
            reveal(NestedComplexSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, flag) = Const(U32Le, 0).parse(&rest)?;
            let rest = rest.skip(n1);
            proof {
                self.hdr_payload.lemma_deep_view_fields();
                self.hdr_payload.deep_view().lemma_into_structural_fields();
                self.hdr_payload.hdr.lemma_deep_view_fields();
                self.hdr_payload.hdr.deep_view().lemma_into_structural_fields();
            }

            let (n2, data) = (Varied((self.hdr_payload.hdr.payload_length - 8))).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = NestedComplex { flag, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, NestedComplex<'i>> for NestedComplexFmt<'i> {
        fn serialize_into(&self, v: &NestedComplex<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<NestedComplexFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedComplexFmt as SpecByteLen>::byte_len);
            reveal(<NestedComplex as DeepView>::deep_view);
            reveal(NestedComplexSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let NestedComplex { flag, data } = v;
            proof {
                self.hdr_payload.lemma_deep_view_fields();
                self.hdr_payload.deep_view().lemma_into_structural_fields();
                self.hdr_payload.hdr.lemma_deep_view_fields();
                self.hdr_payload.hdr.deep_view().lemma_into_structural_fields();
            }

            U32Le.serialize_into(flag, obuf);
            Varied((self.hdr_payload.hdr.payload_length - 8)).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedComplex<'i>> for NestedComplexFmt<'i> {
        fn prepare(&self, v: &NestedComplex<'i>) -> Result<usize, PreSerializeError> {
            reveal(<NestedComplexFmt as SpecByteLen>::byte_len);
            reveal(<NestedComplex as DeepView>::deep_view);
            reveal(NestedComplexSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let NestedComplex { flag, data } = v;
            proof {
                self.hdr_payload.lemma_deep_view_fields();
                self.hdr_payload.deep_view().lemma_into_structural_fields();
                self.hdr_payload.hdr.lemma_deep_view_fields();
                self.hdr_payload.hdr.deep_view().lemma_into_structural_fields();
            }

            let l1 = (Const(U32Le, 0)).prepare(flag)?;
            let l2 = (Varied((self.hdr_payload.hdr.payload_length - 8))).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CombinedExampleFmt {
        type PT = CombinedExample<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CombinedExampleFmt as SpecParser>::spec_parse);
            reveal(<CombinedExample as DeepView>::deep_view);
            reveal(CombinedExampleSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, header) = (Named("generic_header", GenericHeaderFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            proof {
                header.lemma_deep_view_fields();
                header.deep_view().lemma_into_structural_fields();
            }

            let (n2, body) = (Varied((self.total_len - header.payload_length))).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = CombinedExample { header, body };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, CombinedExample<'i>> for CombinedExampleFmt {
        fn serialize_into(&self, v: &CombinedExample<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<CombinedExampleFmt as SpecSerializer>::spec_serialize);
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            reveal(<CombinedExample as DeepView>::deep_view);
            reveal(CombinedExampleSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let CombinedExample { header, body } = v;
            proof {
                header.lemma_deep_view_fields();
                header.deep_view().lemma_into_structural_fields();
            }

            GenericHeaderFmt.serialize_into(header, obuf);
            Varied((self.total_len - header.payload_length)).serialize_into(*body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CombinedExample<'i>> for CombinedExampleFmt {
        fn prepare(&self, v: &CombinedExample<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CombinedExampleFmt as SpecByteLen>::byte_len);
            reveal(<CombinedExample as DeepView>::deep_view);
            reveal(CombinedExampleSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let CombinedExample { header, body } = v;
            proof {
                header.lemma_deep_view_fields();
                header.deep_view().lemma_into_structural_fields();
            }

            let l1 = (Named("generic_header", GenericHeaderFmt)).prepare(header)?;
            let l2 = (Varied((self.total_len - header.payload_length))).prepare(body)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for FinalMsgFmt {
        type PT = FinalMsg<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<FinalMsgFmt as SpecParser>::spec_parse);
            reveal(<FinalMsg as DeepView>::deep_view);
            reveal(FinalMsgSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, total_len) = (U32Le).parse(&rest)?;
            if !(total_len >= 16777215 && total_len <= 4294967295) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, body) = (Named(
                "combined_example",
                CombinedExampleFmt { total_len: total_len },
            )).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, hdr_payload) = (Named("payload_with_header", PayloadWithHeaderFmt)).parse(
                &rest,
            )?;
            let rest = rest.skip(n3);
            proof {
                hdr_payload.lemma_deep_view_fields();
                hdr_payload.deep_view().lemma_into_structural_fields();
            }

            let (n4, nested) = (Named(
                "nested_complex",
                NestedComplexFmt { hdr_payload: hdr_payload },
            )).parse(&rest)?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = FinalMsg { total_len, body, hdr_payload, nested };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, FinalMsg<'i>> for FinalMsgFmt {
        fn serialize_into(&self, v: &FinalMsg<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<FinalMsgFmt as SpecSerializer>::spec_serialize);
            reveal(<FinalMsgFmt as SpecByteLen>::byte_len);
            reveal(<FinalMsg as DeepView>::deep_view);
            reveal(FinalMsgSpec::into_structural);
            let ghost old_obuf = obuf@;

            let FinalMsg { total_len, body, hdr_payload, nested } = v;
            proof {
                hdr_payload.lemma_deep_view_fields();
                hdr_payload.deep_view().lemma_into_structural_fields();
            }

            U32Le.serialize_into(total_len, obuf);
            CombinedExampleFmt { total_len: *total_len }.serialize_into(body, obuf);
            PayloadWithHeaderFmt.serialize_into(hdr_payload, obuf);
            NestedComplexFmt { hdr_payload: *hdr_payload }.serialize_into(nested, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<FinalMsg<'i>> for FinalMsgFmt {
        fn prepare(&self, v: &FinalMsg<'i>) -> Result<usize, PreSerializeError> {
            reveal(<FinalMsgFmt as SpecByteLen>::byte_len);
            reveal(<FinalMsg as DeepView>::deep_view);
            reveal(FinalMsgSpec::into_structural);
            let FinalMsg { total_len, body, hdr_payload, nested } = v;
            proof {
                hdr_payload.lemma_deep_view_fields();
                hdr_payload.deep_view().lemma_into_structural_fields();
            }

            let l1 = {
                if !(*total_len >= 16777215 && *total_len <= 4294967295) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (U32Le).prepare(total_len)
                }
            }?;
            let l2 = (Named(
                "combined_example",
                CombinedExampleFmt { total_len: *total_len },
            )).prepare(body)?;
            let l3 = (Named("payload_with_header", PayloadWithHeaderFmt)).prepare(hdr_payload)?;
            let l4 = (Named(
                "nested_complex",
                NestedComplexFmt { hdr_payload: *hdr_payload },
            )).prepare(nested)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?.checked_add(l4).ok_or(
                PreSerializeError::length_too_large(),
            )?;
            Ok(total_len)
        }
    }

}

} // verus!
