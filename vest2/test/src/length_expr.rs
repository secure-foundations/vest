#![allow(warnings)]
use vest_lib2::combinators::mapped::spec::*;
use vest_lib2::combinators::recursive::*;
use vest_lib2::combinators::*;
use vest_lib2::core::exec::bytes_eq;
use vest_lib2::core::exec::input::{InputBuf, InputSlice};
use vest_lib2::core::exec::output::OutputBuf;
use vest_lib2::core::exec::parser::*;
use vest_lib2::core::exec::serializer::*;
use vest_lib2::core::exec::ParseError;
use vest_lib2::core::{proof::*, spec::*};
use vest_lib2::primitives::btcvarint::VarInt;
use vest_lib2::primitives::leb128::ULeb128;
use vest_lib2::Never;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct Header {
    pub len: u16,
    pub flags: u8,
}

pub type HeaderSpec = Header;

pub type HeaderInner = (u16, u8);

impl DeepView for Header {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `primitive_sizes`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct PrimitiveSizes<'i> {
    pub byte: &'i [u8],
    pub word: &'i [u8],
}

# [verifier::ext_equal]
pub struct PrimitiveSizesSpec {
    pub byte: Seq<u8>,
    pub word: Seq<u8>,
}

pub type PrimitiveSizesInner = (Seq<u8>, Seq<u8>);

impl<'i> DeepView for PrimitiveSizes<'i> {
    type V = PrimitiveSizesSpec;

    open spec fn deep_view(&self) -> Self::V {
        PrimitiveSizesSpec { byte: self.byte.deep_view(), word: self.word.deep_view() }
    }
}

# [doc = "data type for `named_size`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct NamedSize<'i> {
    pub bytes: &'i [u8],
}

# [verifier::ext_equal]
pub struct NamedSizeSpec {
    pub bytes: Seq<u8>,
}

pub type NamedSizeInner = Seq<u8>;

impl<'i> DeepView for NamedSize<'i> {
    type V = NamedSizeSpec;

    open spec fn deep_view(&self) -> Self::V {
        NamedSizeSpec { bytes: self.bytes.deep_view() }
    }
}

# [doc = "data type for `header_alias`."]
pub type HeaderAlias = Header;

pub type HeaderAliasSpec = HeaderSpec;

# [doc = "data type for `alias_size`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct AliasSize<'i> {
    pub bytes: &'i [u8],
}

# [verifier::ext_equal]
pub struct AliasSizeSpec {
    pub bytes: Seq<u8>,
}

pub type AliasSizeInner = Seq<u8>;

impl<'i> DeepView for AliasSize<'i> {
    type V = AliasSizeSpec;

    open spec fn deep_view(&self) -> Self::V {
        AliasSizeSpec { bytes: self.bytes.deep_view() }
    }
}

# [doc = "data type for `fixed_choice`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub enum FixedChoice {
    Variant1(u16),
    Default(u16),
}

pub type FixedChoiceSpec = FixedChoice;

pub type FixedChoiceInner = Sum<u16, u16>;

impl DeepView for FixedChoice {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `choice_format_size`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct ChoiceFormatSize<'i> {
    pub bytes: &'i [u8],
}

# [verifier::ext_equal]
pub struct ChoiceFormatSizeSpec {
    pub bytes: Seq<u8>,
}

pub type ChoiceFormatSizeInner = Seq<u8>;

impl<'i> DeepView for ChoiceFormatSize<'i> {
    type V = ChoiceFormatSizeSpec;

    open spec fn deep_view(&self) -> Self::V {
        ChoiceFormatSizeSpec { bytes: self.bytes.deep_view() }
    }
}

# [doc = "data type for `choice_tag`."]
pub type ChoiceTag<'i> = &'i [u8];

pub type ChoiceTagSpec = Seq<u8>;

# [doc = "data type for `choice_arrays_folded`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct ChoiceArraysFolded<'i> {
    pub tag: ChoiceTag<'i>,
    pub body: ChoiceArraysFoldedBody,
}

# [verifier::ext_equal]
pub struct ChoiceArraysFoldedSpec {
    pub tag: ChoiceTagSpec,
    pub body: ChoiceArraysFoldedBodySpec,
}

pub type ChoiceArraysFoldedInner = (ChoiceTagSpec, ChoiceArraysFoldedBodySpec);

impl<'i> DeepView for ChoiceArraysFolded<'i> {
    type V = ChoiceArraysFoldedSpec;

    open spec fn deep_view(&self) -> Self::V {
        ChoiceArraysFoldedSpec { tag: self.tag.deep_view(), body: self.body.deep_view() }
    }
}

# [doc = "data type for `size_arith`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct SizeArith<'i> {
    pub bytes: &'i [u8],
}

# [verifier::ext_equal]
pub struct SizeArithSpec {
    pub bytes: Seq<u8>,
}

pub type SizeArithInner = Seq<u8>;

impl<'i> DeepView for SizeArith<'i> {
    type V = SizeArithSpec;

    open spec fn deep_view(&self) -> Self::V {
        SizeArithSpec { bytes: self.bytes.deep_view() }
    }
}

# [doc = "data type for `simple_sub`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct SimpleSub<'i> {
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct SimpleSubSpec {
    pub data: Seq<u8>,
}

pub type SimpleSubInner = Seq<u8>;

impl<'i> DeepView for SimpleSub<'i> {
    type V = SimpleSubSpec;

    open spec fn deep_view(&self) -> Self::V {
        SimpleSubSpec { data: self.data.deep_view() }
    }
}

# [doc = "data type for `multi_arith`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct MultiArith<'i> {
    pub body: &'i [u8],
}

# [verifier::ext_equal]
pub struct MultiArithSpec {
    pub body: Seq<u8>,
}

pub type MultiArithInner = Seq<u8>;

impl<'i> DeepView for MultiArith<'i> {
    type V = MultiArithSpec;

    open spec fn deep_view(&self) -> Self::V {
        MultiArithSpec { body: self.body.deep_view() }
    }
}

# [doc = "data type for `paren_expr`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct ParenExpr<'i> {
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct ParenExprSpec {
    pub data: Seq<u8>,
}

pub type ParenExprInner = Seq<u8>;

impl<'i> DeepView for ParenExpr<'i> {
    type V = ParenExprSpec;

    open spec fn deep_view(&self) -> Self::V {
        ParenExprSpec { data: self.data.deep_view() }
    }
}

# [doc = "data type for `mixed_const`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct MixedConst<'i> {
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct MixedConstSpec {
    pub data: Seq<u8>,
}

pub type MixedConstInner = Seq<u8>;

impl<'i> DeepView for MixedConst<'i> {
    type V = MixedConstSpec;

    open spec fn deep_view(&self) -> Self::V {
        MixedConstSpec { data: self.data.deep_view() }
    }
}

# [doc = "data type for `payload_with_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct PayloadWithHeader<'i> {
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct PayloadWithHeaderSpec {
    pub data: Seq<u8>,
}

pub type PayloadWithHeaderInner = Seq<u8>;

impl<'i> DeepView for PayloadWithHeader<'i> {
    type V = PayloadWithHeaderSpec;

    open spec fn deep_view(&self) -> Self::V {
        PayloadWithHeaderSpec { data: self.data.deep_view() }
    }
}

# [doc = "data type for `choice_arrays_folded_body`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub enum ChoiceArraysFoldedBody {
    Variant1(u8),
    Variant2(u16),
    Default(u16),
}

pub type ChoiceArraysFoldedBodySpec = ChoiceArraysFoldedBody;

pub type ChoiceArraysFoldedBodyInner = Sum<u8, Sum<u16, u16>>;

impl DeepView for ChoiceArraysFoldedBody {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `header`."]
# [derive (Clone, Copy)]
pub struct HeaderFmt;

pub type HeaderFmtSpec = Named<
    Mapped<
        Bind<Refined<U16Le, PredFnSpec<u16>>, spec_fn(u16) -> U8>,
        FnSpecMapper<HeaderInner, HeaderSpec>,
    >,
>;

impl HeaderFmt {
    # [doc = "specification constructor for `header`."]
    pub open spec fn spec_inner() -> HeaderFmtSpec {
        Named(
            "header",
            Mapped {
                inner: Bind(Refined(U16Le, |x: u16| x >= 3 && x <= 65535), |len: u16| U8),
                mapper: (
                    |parsed: HeaderInner| -> HeaderSpec
                        {
                            let (len, flags) = parsed;
                            HeaderSpec { len, flags }
                        },
                    |value: HeaderSpec| -> HeaderInner
                        {
                            let HeaderSpec { len, flags } = value;
                            (len, flags)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `primitive_sizes`."]
# [derive (Clone, Copy)]
pub struct PrimitiveSizesFmt;

pub type PrimitiveSizesFmtSpec = Named<
    Mapped<Pair<Fixed<1>, Fixed<2>>, FnSpecMapper<PrimitiveSizesInner, PrimitiveSizesSpec>>,
>;

impl PrimitiveSizesFmt {
    # [doc = "specification constructor for `primitive_sizes`."]
    pub open spec fn spec_inner() -> PrimitiveSizesFmtSpec {
        Named(
            "primitive_sizes",
            Mapped {
                inner: Pair(Fixed::<1>, Fixed::<2>),
                mapper: (
                    |parsed: PrimitiveSizesInner| -> PrimitiveSizesSpec
                        {
                            let (byte, word) = parsed;
                            PrimitiveSizesSpec { byte, word }
                        },
                    |value: PrimitiveSizesSpec| -> PrimitiveSizesInner
                        {
                            let PrimitiveSizesSpec { byte, word } = value;
                            (byte, word)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `named_size`."]
# [derive (Clone, Copy)]
pub struct NamedSizeFmt;

pub type NamedSizeFmtSpec = Named<Mapped<Fixed<3>, FnSpecMapper<NamedSizeInner, NamedSizeSpec>>>;

impl NamedSizeFmt {
    # [doc = "specification constructor for `named_size`."]
    pub open spec fn spec_inner() -> NamedSizeFmtSpec {
        Named(
            "named_size",
            Mapped {
                inner: Fixed::<3>,
                mapper: (
                    |parsed: NamedSizeInner| -> NamedSizeSpec
                        {
                            let bytes = parsed;
                            NamedSizeSpec { bytes }
                        },
                    |value: NamedSizeSpec| -> NamedSizeInner
                        {
                            let NamedSizeSpec { bytes } = value;
                            bytes
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `header_alias`."]
# [derive (Clone, Copy)]
pub struct HeaderAliasFmt;

pub type HeaderAliasFmtSpec = Named<HeaderFmt>;

impl HeaderAliasFmt {
    # [doc = "specification constructor for `header_alias`."]
    pub open spec fn spec_inner() -> HeaderAliasFmtSpec {
        Named("header_alias", HeaderFmt)
    }
}

# [doc = "named format combinator for `alias_size`."]
# [derive (Clone, Copy)]
pub struct AliasSizeFmt;

pub type AliasSizeFmtSpec = Named<Mapped<Fixed<3>, FnSpecMapper<AliasSizeInner, AliasSizeSpec>>>;

impl AliasSizeFmt {
    # [doc = "specification constructor for `alias_size`."]
    pub open spec fn spec_inner() -> AliasSizeFmtSpec {
        Named(
            "alias_size",
            Mapped {
                inner: Fixed::<3>,
                mapper: (
                    |parsed: AliasSizeInner| -> AliasSizeSpec
                        {
                            let bytes = parsed;
                            AliasSizeSpec { bytes }
                        },
                    |value: AliasSizeSpec| -> AliasSizeInner
                        {
                            let AliasSizeSpec { bytes } = value;
                            bytes
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `fixed_choice`."]
# [derive (Clone, Copy)]
pub struct FixedChoiceFmt {
    tag: u8,
}

impl FixedChoiceFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn tag_spec(&self) -> u8 {
        self.tag.deep_view()
    }

    pub closed spec fn spec(tag: u8) -> Self {
        FixedChoiceFmt { tag }
    }
}

pub type FixedChoiceFmtSpec = Named<
    Mapped<Sum<U16Le, U16Le>, FnSpecMapper<FixedChoiceInner, FixedChoiceSpec>>,
>;

impl FixedChoiceFmt {
    # [doc = "specification constructor for `fixed_choice`."]
    pub open spec fn spec_inner(tag: u8) -> FixedChoiceFmtSpec {
        Named(
            "fixed_choice",
            Mapped {
                inner: match tag {
                    0 => L(U16Le),
                    _ => R(U16Le),
                },
                mapper: (
                    |parsed: FixedChoiceInner| -> FixedChoiceSpec
                        {
                            match parsed {
                                L(v) => FixedChoiceSpec::Variant1(v),
                                R(v) => FixedChoiceSpec::Default(v),
                            }
                        },
                    |value: FixedChoiceSpec| -> FixedChoiceInner
                        {
                            match value {
                                FixedChoiceSpec::Variant1(v) => L(v),
                                FixedChoiceSpec::Default(v) => R(v),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `choice_format_size`."]
# [derive (Clone, Copy)]
pub struct ChoiceFormatSizeFmt;

pub type ChoiceFormatSizeFmtSpec = Named<
    Mapped<Fixed<2>, FnSpecMapper<ChoiceFormatSizeInner, ChoiceFormatSizeSpec>>,
>;

impl ChoiceFormatSizeFmt {
    # [doc = "specification constructor for `choice_format_size`."]
    pub open spec fn spec_inner() -> ChoiceFormatSizeFmtSpec {
        Named(
            "choice_format_size",
            Mapped {
                inner: Fixed::<2>,
                mapper: (
                    |parsed: ChoiceFormatSizeInner| -> ChoiceFormatSizeSpec
                        {
                            let bytes = parsed;
                            ChoiceFormatSizeSpec { bytes }
                        },
                    |value: ChoiceFormatSizeSpec| -> ChoiceFormatSizeInner
                        {
                            let ChoiceFormatSizeSpec { bytes } = value;
                            bytes
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `choice_tag`."]
# [derive (Clone, Copy)]
pub struct ChoiceTagFmt;

pub type ChoiceTagFmtSpec = Named<Fixed<2>>;

impl ChoiceTagFmt {
    # [doc = "specification constructor for `choice_tag`."]
    pub open spec fn spec_inner() -> ChoiceTagFmtSpec {
        Named("choice_tag", Fixed::<2>)
    }
}

# [doc = "named format combinator for `choice_arrays_folded`."]
# [derive (Clone, Copy)]
pub struct ChoiceArraysFoldedFmt;

pub type ChoiceArraysFoldedFmtSpec = Named<
    Mapped<
        Bind<ChoiceTagFmt, spec_fn(ChoiceTagSpec) -> ChoiceArraysFoldedBodyFmtSpec>,
        FnSpecMapper<ChoiceArraysFoldedInner, ChoiceArraysFoldedSpec>,
    >,
>;

impl ChoiceArraysFoldedFmt {
    # [doc = "specification constructor for `choice_arrays_folded`."]
    pub open spec fn spec_inner() -> ChoiceArraysFoldedFmtSpec {
        Named(
            "choice_arrays_folded",
            Mapped {
                inner: Bind(
                    ChoiceTagFmt,
                    |tag: ChoiceTagSpec| ChoiceArraysFoldedBodyFmt::spec_inner(tag),
                ),
                mapper: (
                    |parsed: ChoiceArraysFoldedInner| -> ChoiceArraysFoldedSpec
                        {
                            let (tag, body) = parsed;
                            ChoiceArraysFoldedSpec { tag, body }
                        },
                    |value: ChoiceArraysFoldedSpec| -> ChoiceArraysFoldedInner
                        {
                            let ChoiceArraysFoldedSpec { tag, body } = value;
                            (tag, body)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `size_arith`."]
# [derive (Clone, Copy)]
pub struct SizeArithFmt;

pub type SizeArithFmtSpec = Named<Mapped<Fixed<4>, FnSpecMapper<SizeArithInner, SizeArithSpec>>>;

impl SizeArithFmt {
    # [doc = "specification constructor for `size_arith`."]
    pub open spec fn spec_inner() -> SizeArithFmtSpec {
        Named(
            "size_arith",
            Mapped {
                inner: Fixed::<4>,
                mapper: (
                    |parsed: SizeArithInner| -> SizeArithSpec
                        {
                            let bytes = parsed;
                            SizeArithSpec { bytes }
                        },
                    |value: SizeArithSpec| -> SizeArithInner
                        {
                            let SizeArithSpec { bytes } = value;
                            bytes
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `simple_sub`."]
# [derive (Clone, Copy)]
pub struct SimpleSubFmt {
    len: u16,
}

impl SimpleSubFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.len >= 4 && self.len <= 65535
    }

    pub closed spec fn len_spec(&self) -> u16 {
        self.len.deep_view()
    }

    pub closed spec fn spec(len: u16) -> Self {
        SimpleSubFmt { len }
    }
}

pub type SimpleSubFmtSpec = Named<Mapped<Varied<u16>, FnSpecMapper<SimpleSubInner, SimpleSubSpec>>>;

impl SimpleSubFmt {
    # [doc = "specification constructor for `simple_sub`."]
    pub open spec fn spec_inner(len: u16) -> SimpleSubFmtSpec {
        Named(
            "simple_sub",
            Mapped {
                inner: Varied(((((len - 3) as u16) - 1) as u16)),
                mapper: (
                    |parsed: SimpleSubInner| -> SimpleSubSpec
                        {
                            let data = parsed;
                            SimpleSubSpec { data }
                        },
                    |value: SimpleSubSpec| -> SimpleSubInner
                        {
                            let SimpleSubSpec { data } = value;
                            data
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `multi_arith`."]
# [derive (Clone, Copy)]
pub struct MultiArithFmt {
    total: u16,
    hdr_len: u16,
}

impl MultiArithFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.total >= 263 && self.hdr_len >= 0 && self.hdr_len <= 255
    }

    pub closed spec fn total_spec(&self) -> u16 {
        self.total.deep_view()
    }

    pub closed spec fn hdr_len_spec(&self) -> u16 {
        self.hdr_len.deep_view()
    }

    pub closed spec fn spec(total: u16, hdr_len: u16) -> Self {
        MultiArithFmt { total, hdr_len }
    }
}

pub type MultiArithFmtSpec = Named<
    Mapped<Varied<u16>, FnSpecMapper<MultiArithInner, MultiArithSpec>>,
>;

impl MultiArithFmt {
    # [doc = "specification constructor for `multi_arith`."]
    pub open spec fn spec_inner(total: u16, hdr_len: u16) -> MultiArithFmtSpec {
        Named(
            "multi_arith",
            Mapped {
                inner: Varied(((((total - hdr_len) as u16) - 8) as u16)),
                mapper: (
                    |parsed: MultiArithInner| -> MultiArithSpec
                        {
                            let body = parsed;
                            MultiArithSpec { body }
                        },
                    |value: MultiArithSpec| -> MultiArithInner
                        {
                            let MultiArithSpec { body } = value;
                            body
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `paren_expr`."]
# [derive (Clone, Copy)]
pub struct ParenExprFmt {
    a: u16,
    b: u16,
    c: u16,
}

impl ParenExprFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.a >= 255 && self.a <= 65530 && self.b >= 0 && self.b <= 255 && self.c == 1
    }

    pub closed spec fn a_spec(&self) -> u16 {
        self.a.deep_view()
    }

    pub closed spec fn b_spec(&self) -> u16 {
        self.b.deep_view()
    }

    pub closed spec fn c_spec(&self) -> u16 {
        self.c.deep_view()
    }

    pub closed spec fn spec(a: u16, b: u16, c: u16) -> Self {
        ParenExprFmt { a, b, c }
    }
}

pub type ParenExprFmtSpec = Named<Mapped<Varied<u16>, FnSpecMapper<ParenExprInner, ParenExprSpec>>>;

impl ParenExprFmt {
    # [doc = "specification constructor for `paren_expr`."]
    pub open spec fn spec_inner(a: u16, b: u16, c: u16) -> ParenExprFmtSpec {
        Named(
            "paren_expr",
            Mapped {
                inner: Varied(((((a - b) as u16) + c) as u16)),
                mapper: (
                    |parsed: ParenExprInner| -> ParenExprSpec
                        {
                            let data = parsed;
                            ParenExprSpec { data }
                        },
                    |value: ParenExprSpec| -> ParenExprInner
                        {
                            let ParenExprSpec { data } = value;
                            data
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `mixed_const`."]
# [derive (Clone, Copy)]
pub struct MixedConstFmt {
    len: u16,
}

impl MixedConstFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.len >= 4 && self.len <= 65535
    }

    pub closed spec fn len_spec(&self) -> u16 {
        self.len.deep_view()
    }

    pub closed spec fn spec(len: u16) -> Self {
        MixedConstFmt { len }
    }
}

pub type MixedConstFmtSpec = Named<
    Mapped<Varied<u16>, FnSpecMapper<MixedConstInner, MixedConstSpec>>,
>;

impl MixedConstFmt {
    # [doc = "specification constructor for `mixed_const`."]
    pub open spec fn spec_inner(len: u16) -> MixedConstFmtSpec {
        Named(
            "mixed_const",
            Mapped {
                inner: Varied(((((len - 4) as u16) + 2) as u16)),
                mapper: (
                    |parsed: MixedConstInner| -> MixedConstSpec
                        {
                            let data = parsed;
                            MixedConstSpec { data }
                        },
                    |value: MixedConstSpec| -> MixedConstInner
                        {
                            let MixedConstSpec { data } = value;
                            data
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `payload_with_header`."]
# [derive (Clone, Copy)]
pub struct PayloadWithHeaderFmt {
    hdr: Header,
}

impl PayloadWithHeaderFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        HeaderFmt.consistent(self.hdr.deep_view())
    }

    pub closed spec fn hdr_spec(&self) -> HeaderSpec {
        self.hdr.deep_view()
    }

    pub closed spec fn spec(hdr: Header) -> Self {
        PayloadWithHeaderFmt { hdr }
    }
}

pub type PayloadWithHeaderFmtSpec = Named<
    Mapped<Varied<u16>, FnSpecMapper<PayloadWithHeaderInner, PayloadWithHeaderSpec>>,
>;

impl PayloadWithHeaderFmt {
    # [doc = "specification constructor for `payload_with_header`."]
    pub open spec fn spec_inner(hdr: HeaderSpec) -> PayloadWithHeaderFmtSpec {
        Named(
            "payload_with_header",
            Mapped {
                inner: Varied(((hdr.len - 3) as u16)),
                mapper: (
                    |parsed: PayloadWithHeaderInner| -> PayloadWithHeaderSpec
                        {
                            let data = parsed;
                            PayloadWithHeaderSpec { data }
                        },
                    |value: PayloadWithHeaderSpec| -> PayloadWithHeaderInner
                        {
                            let PayloadWithHeaderSpec { data } = value;
                            data
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `choice_arrays_folded_body`."]
# [derive (Clone, Copy)]
pub struct ChoiceArraysFoldedBodyFmt<'i> {
    tag: ChoiceTag<'i>,
}

impl<'i> ChoiceArraysFoldedBodyFmt<'i> {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn tag_spec(&self) -> ChoiceTagSpec {
        self.tag.deep_view()
    }

    pub closed spec fn spec(tag: ChoiceTag<'i>) -> Self {
        ChoiceArraysFoldedBodyFmt { tag }
    }
}

pub type ChoiceArraysFoldedBodyFmtSpec = Named<
    Mapped<
        Sum<U8, Sum<U16Le, U16Le>>,
        FnSpecMapper<ChoiceArraysFoldedBodyInner, ChoiceArraysFoldedBodySpec>,
    >,
>;

impl<'i> ChoiceArraysFoldedBodyFmt<'i> {
    # [doc = "specification constructor for `choice_arrays_folded_body`."]
    pub open spec fn spec_inner(tag: ChoiceTagSpec) -> ChoiceArraysFoldedBodyFmtSpec {
        Named(
            "choice_arrays_folded_body",
            Mapped {
                inner: match tag {
                    x if x == [0x00u8, 0x00u8].deep_view() => L(U8),
                    x if x == [0x01u8, 0x01u8].deep_view() => R(L(U16Le)),
                    _ => R(R(U16Le)),
                },
                mapper: (
                    |parsed: ChoiceArraysFoldedBodyInner| -> ChoiceArraysFoldedBodySpec
                        {
                            match parsed {
                                L(v) => ChoiceArraysFoldedBodySpec::Variant1(v),
                                R(L(v)) => ChoiceArraysFoldedBodySpec::Variant2(v),
                                R(R(v)) => ChoiceArraysFoldedBodySpec::Default(v),
                            }
                        },
                    |value: ChoiceArraysFoldedBodySpec| -> ChoiceArraysFoldedBodyInner
                        {
                            match value {
                                ChoiceArraysFoldedBodySpec::Variant1(v) => L(v),
                                ChoiceArraysFoldedBodySpec::Variant2(v) => R(L(v)),
                                ChoiceArraysFoldedBodySpec::Default(v) => R(R(v)),
                            }
                        },
                ),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

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

    impl SpecParser for PrimitiveSizesFmt {
        type PVal = PrimitiveSizesSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for PrimitiveSizesFmt {
        type Val = PrimitiveSizesSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for PrimitiveSizesFmt {
        type SValue = PrimitiveSizesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for PrimitiveSizesFmt {
        type SVal = PrimitiveSizesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for PrimitiveSizesFmt {
        type T = PrimitiveSizesSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for NamedSizeFmt {
        type PVal = NamedSizeSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for NamedSizeFmt {
        type Val = NamedSizeSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for NamedSizeFmt {
        type SValue = NamedSizeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for NamedSizeFmt {
        type SVal = NamedSizeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for NamedSizeFmt {
        type T = NamedSizeSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for HeaderAliasFmt {
        type PVal = HeaderAliasSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for HeaderAliasFmt {
        type Val = HeaderAliasSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for HeaderAliasFmt {
        type SValue = HeaderAliasSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for HeaderAliasFmt {
        type SVal = HeaderAliasSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for HeaderAliasFmt {
        type T = HeaderAliasSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for AliasSizeFmt {
        type PVal = AliasSizeSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for AliasSizeFmt {
        type Val = AliasSizeSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for AliasSizeFmt {
        type SValue = AliasSizeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AliasSizeFmt {
        type SVal = AliasSizeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for AliasSizeFmt {
        type T = AliasSizeSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for FixedChoiceFmt {
        type PVal = FixedChoiceSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.tag_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for FixedChoiceFmt {
        type Val = FixedChoiceSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.tag_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for FixedChoiceFmt {
        type SValue = FixedChoiceSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for FixedChoiceFmt {
        type SVal = FixedChoiceSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for FixedChoiceFmt {
        type T = FixedChoiceSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.tag_spec()).byte_len(v)
        }
    }

    impl SpecParser for ChoiceFormatSizeFmt {
        type PVal = ChoiceFormatSizeSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ChoiceFormatSizeFmt {
        type Val = ChoiceFormatSizeSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ChoiceFormatSizeFmt {
        type SValue = ChoiceFormatSizeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ChoiceFormatSizeFmt {
        type SVal = ChoiceFormatSizeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ChoiceFormatSizeFmt {
        type T = ChoiceFormatSizeSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ChoiceTagFmt {
        type PVal = ChoiceTagSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ChoiceTagFmt {
        type Val = ChoiceTagSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ChoiceTagFmt {
        type SValue = ChoiceTagSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ChoiceTagFmt {
        type SVal = ChoiceTagSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ChoiceTagFmt {
        type T = ChoiceTagSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ChoiceArraysFoldedFmt {
        type PVal = ChoiceArraysFoldedSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ChoiceArraysFoldedFmt {
        type Val = ChoiceArraysFoldedSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ChoiceArraysFoldedFmt {
        type SValue = ChoiceArraysFoldedSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ChoiceArraysFoldedFmt {
        type SVal = ChoiceArraysFoldedSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ChoiceArraysFoldedFmt {
        type T = ChoiceArraysFoldedSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for SizeArithFmt {
        type PVal = SizeArithSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for SizeArithFmt {
        type Val = SizeArithSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for SizeArithFmt {
        type SValue = SizeArithSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for SizeArithFmt {
        type SVal = SizeArithSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for SizeArithFmt {
        type T = SizeArithSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for SimpleSubFmt {
        type PVal = SimpleSubSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.len_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for SimpleSubFmt {
        type Val = SimpleSubSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.len_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for SimpleSubFmt {
        type SValue = SimpleSubSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.len_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for SimpleSubFmt {
        type SVal = SimpleSubSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.len_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for SimpleSubFmt {
        type T = SimpleSubSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.len_spec()).byte_len(v)
        }
    }

    impl SpecParser for MultiArithFmt {
        type PVal = MultiArithSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.total_spec(), self.hdr_len_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for MultiArithFmt {
        type Val = MultiArithSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.total_spec(), self.hdr_len_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for MultiArithFmt {
        type SValue = MultiArithSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.total_spec(), self.hdr_len_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MultiArithFmt {
        type SVal = MultiArithSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.total_spec(), self.hdr_len_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for MultiArithFmt {
        type T = MultiArithSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.total_spec(), self.hdr_len_spec()).byte_len(v)
        }
    }

    impl SpecParser for ParenExprFmt {
        type PVal = ParenExprSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for ParenExprFmt {
        type Val = ParenExprSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for ParenExprFmt {
        type SValue = ParenExprSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec()).spec_serialize_dps(
                v,
                obuf,
            )
        }
    }

    impl SpecSerializer for ParenExprFmt {
        type SVal = ParenExprSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for ParenExprFmt {
        type T = ParenExprSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec()).byte_len(v)
        }
    }

    impl SpecParser for MixedConstFmt {
        type PVal = MixedConstSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.len_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for MixedConstFmt {
        type Val = MixedConstSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.len_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for MixedConstFmt {
        type SValue = MixedConstSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.len_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MixedConstFmt {
        type SVal = MixedConstSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.len_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for MixedConstFmt {
        type T = MixedConstSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.len_spec()).byte_len(v)
        }
    }

    impl SpecParser for PayloadWithHeaderFmt {
        type PVal = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.hdr_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for PayloadWithHeaderFmt {
        type Val = PayloadWithHeaderSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.hdr_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for PayloadWithHeaderFmt {
        type SValue = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.hdr_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for PayloadWithHeaderFmt {
        type SVal = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.hdr_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for PayloadWithHeaderFmt {
        type T = PayloadWithHeaderSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.hdr_spec()).byte_len(v)
        }
    }

    impl<'i> SpecParser for ChoiceArraysFoldedBodyFmt<'i> {
        type PVal = ChoiceArraysFoldedBodySpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.tag_spec()).spec_parse(ibuf)
        }
    }

    impl<'i> Consistency for ChoiceArraysFoldedBodyFmt<'i> {
        type Val = ChoiceArraysFoldedBodySpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.tag_spec()).consistent(v)
        }
    }

    impl<'i> SpecSerializerDps for ChoiceArraysFoldedBodyFmt<'i> {
        type SValue = ChoiceArraysFoldedBodySpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl<'i> SpecSerializer for ChoiceArraysFoldedBodyFmt<'i> {
        type SVal = ChoiceArraysFoldedBodySpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize(v)
        }
    }

    impl<'i> SpecByteLen for ChoiceArraysFoldedBodyFmt<'i> {
        type T = ChoiceArraysFoldedBodySpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.tag_spec()).byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

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
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<HeaderFmt as SpecParser>::spec_parse);
            reveal(<HeaderFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
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
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for HeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<HeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
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

    impl SafeParser for PrimitiveSizesFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for PrimitiveSizesFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for PrimitiveSizesFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecParser>::spec_parse);
            reveal(<PrimitiveSizesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecParser>::spec_parse);
            reveal(<PrimitiveSizesFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for PrimitiveSizesFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PrimitiveSizesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for PrimitiveSizesFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<PrimitiveSizesFmt as SpecSerializer>::spec_serialize);
            reveal(<PrimitiveSizesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for PrimitiveSizesFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecParser>::spec_parse);
            reveal(<PrimitiveSizesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PrimitiveSizesFmt as Consistency>::consistent);
            reveal(<PrimitiveSizesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for PrimitiveSizesFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for PrimitiveSizesFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PrimitiveSizesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for PrimitiveSizesFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<PrimitiveSizesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PrimitiveSizesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for NamedSizeFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for NamedSizeFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for NamedSizeFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecParser>::spec_parse);
            reveal(<NamedSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecParser>::spec_parse);
            reveal(<NamedSizeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for NamedSizeFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NamedSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for NamedSizeFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<NamedSizeFmt as SpecSerializer>::spec_serialize);
            reveal(<NamedSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for NamedSizeFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecParser>::spec_parse);
            reveal(<NamedSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NamedSizeFmt as Consistency>::consistent);
            reveal(<NamedSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NamedSizeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for NamedSizeFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NamedSizeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for NamedSizeFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<NamedSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NamedSizeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for HeaderAliasFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<HeaderAliasFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for HeaderAliasFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<HeaderAliasFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for HeaderAliasFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<HeaderAliasFmt as SpecParser>::spec_parse);
            reveal(<HeaderAliasFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<HeaderAliasFmt as SpecParser>::spec_parse);
            reveal(<HeaderAliasFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for HeaderAliasFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<HeaderAliasFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<HeaderAliasFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HeaderAliasFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for HeaderAliasFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<HeaderAliasFmt as SpecSerializer>::spec_serialize);
            reveal(<HeaderAliasFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for HeaderAliasFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<HeaderAliasFmt as SpecParser>::spec_parse);
            reveal(<HeaderAliasFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HeaderAliasFmt as Consistency>::consistent);
            reveal(<HeaderAliasFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for HeaderAliasFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<HeaderAliasFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for HeaderAliasFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<HeaderAliasFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HeaderAliasFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for HeaderAliasFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<HeaderAliasFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HeaderAliasFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for AliasSizeFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AliasSizeFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AliasSizeFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecParser>::spec_parse);
            reveal(<AliasSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecParser>::spec_parse);
            reveal(<AliasSizeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for AliasSizeFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AliasSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for AliasSizeFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AliasSizeFmt as SpecSerializer>::spec_serialize);
            reveal(<AliasSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for AliasSizeFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecParser>::spec_parse);
            reveal(<AliasSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AliasSizeFmt as Consistency>::consistent);
            reveal(<AliasSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AliasSizeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for AliasSizeFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AliasSizeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for AliasSizeFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AliasSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AliasSizeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for FixedChoiceFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.tag_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for FixedChoiceFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.tag_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for FixedChoiceFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecParser>::spec_parse);
            reveal(<FixedChoiceFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecParser>::spec_parse);
            reveal(<FixedChoiceFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for FixedChoiceFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FixedChoiceFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for FixedChoiceFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<FixedChoiceFmt as SpecSerializer>::spec_serialize);
            reveal(<FixedChoiceFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for FixedChoiceFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecParser>::spec_parse);
            reveal(<FixedChoiceFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FixedChoiceFmt as Consistency>::consistent);
            reveal(<FixedChoiceFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for FixedChoiceFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for FixedChoiceFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FixedChoiceFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for FixedChoiceFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<FixedChoiceFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FixedChoiceFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ChoiceFormatSizeFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ChoiceFormatSizeFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ChoiceFormatSizeFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecParser>::spec_parse);
            reveal(<ChoiceFormatSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecParser>::spec_parse);
            reveal(<ChoiceFormatSizeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ChoiceFormatSizeFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceFormatSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ChoiceFormatSizeFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ChoiceFormatSizeFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceFormatSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ChoiceFormatSizeFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecParser>::spec_parse);
            reveal(<ChoiceFormatSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceFormatSizeFmt as Consistency>::consistent);
            reveal(<ChoiceFormatSizeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ChoiceFormatSizeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ChoiceFormatSizeFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceFormatSizeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ChoiceFormatSizeFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ChoiceFormatSizeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceFormatSizeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ChoiceTagFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceTagFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ChoiceTagFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ChoiceTagFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ChoiceTagFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceTagFmt as SpecParser>::spec_parse);
            reveal(<ChoiceTagFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceTagFmt as SpecParser>::spec_parse);
            reveal(<ChoiceTagFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ChoiceTagFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ChoiceTagFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ChoiceTagFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceTagFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ChoiceTagFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ChoiceTagFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceTagFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ChoiceTagFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ChoiceTagFmt as SpecParser>::spec_parse);
            reveal(<ChoiceTagFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceTagFmt as Consistency>::consistent);
            reveal(<ChoiceTagFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ChoiceTagFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ChoiceTagFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ChoiceTagFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ChoiceTagFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceTagFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ChoiceTagFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ChoiceTagFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceTagFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ChoiceArraysFoldedFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ChoiceArraysFoldedFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ChoiceArraysFoldedFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecParser>::spec_parse);
            reveal(<ChoiceArraysFoldedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecParser>::spec_parse);
            reveal(<ChoiceArraysFoldedFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ChoiceArraysFoldedFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceArraysFoldedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ChoiceArraysFoldedFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ChoiceArraysFoldedFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceArraysFoldedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ChoiceArraysFoldedFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecParser>::spec_parse);
            reveal(<ChoiceArraysFoldedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceArraysFoldedFmt as Consistency>::consistent);
            reveal(<ChoiceArraysFoldedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ChoiceArraysFoldedFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ChoiceArraysFoldedFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceArraysFoldedFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ChoiceArraysFoldedFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ChoiceArraysFoldedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ChoiceArraysFoldedFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for SizeArithFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<SizeArithFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for SizeArithFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<SizeArithFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for SizeArithFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<SizeArithFmt as SpecParser>::spec_parse);
            reveal(<SizeArithFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<SizeArithFmt as SpecParser>::spec_parse);
            reveal(<SizeArithFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for SizeArithFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<SizeArithFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<SizeArithFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SizeArithFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for SizeArithFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<SizeArithFmt as SpecSerializer>::spec_serialize);
            reveal(<SizeArithFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for SizeArithFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<SizeArithFmt as SpecParser>::spec_parse);
            reveal(<SizeArithFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SizeArithFmt as Consistency>::consistent);
            reveal(<SizeArithFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for SizeArithFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<SizeArithFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for SizeArithFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<SizeArithFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SizeArithFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for SizeArithFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<SizeArithFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SizeArithFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for SimpleSubFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.len_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for SimpleSubFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.len_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for SimpleSubFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecParser>::spec_parse);
            reveal(<SimpleSubFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecParser>::spec_parse);
            reveal(<SimpleSubFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for SimpleSubFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SimpleSubFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for SimpleSubFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<SimpleSubFmt as SpecSerializer>::spec_serialize);
            reveal(<SimpleSubFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for SimpleSubFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecParser>::spec_parse);
            reveal(<SimpleSubFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SimpleSubFmt as Consistency>::consistent);
            reveal(<SimpleSubFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for SimpleSubFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for SimpleSubFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SimpleSubFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for SimpleSubFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<SimpleSubFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<SimpleSubFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MultiArithFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MultiArithFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.total_spec(), self.hdr_len_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MultiArithFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.total_spec(), self.hdr_len_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MultiArithFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MultiArithFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MultiArithFmt as SpecParser>::spec_parse);
            reveal(<MultiArithFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MultiArithFmt as SpecParser>::spec_parse);
            reveal(<MultiArithFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MultiArithFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MultiArithFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MultiArithFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MultiArithFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MultiArithFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MultiArithFmt as SpecSerializer>::spec_serialize);
            reveal(<MultiArithFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MultiArithFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MultiArithFmt as SpecParser>::spec_parse);
            reveal(<MultiArithFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MultiArithFmt as Consistency>::consistent);
            reveal(<MultiArithFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MultiArithFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MultiArithFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MultiArithFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MultiArithFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MultiArithFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MultiArithFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MultiArithFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MultiArithFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ParenExprFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ParenExprFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ParenExprFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ParenExprFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ParenExprFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ParenExprFmt as SpecParser>::spec_parse);
            reveal(<ParenExprFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ParenExprFmt as SpecParser>::spec_parse);
            reveal(<ParenExprFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ParenExprFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ParenExprFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ParenExprFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ParenExprFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ParenExprFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ParenExprFmt as SpecSerializer>::spec_serialize);
            reveal(<ParenExprFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ParenExprFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ParenExprFmt as SpecParser>::spec_parse);
            reveal(<ParenExprFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ParenExprFmt as Consistency>::consistent);
            reveal(<ParenExprFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ParenExprFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ParenExprFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ParenExprFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ParenExprFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ParenExprFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ParenExprFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ParenExprFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ParenExprFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MixedConstFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MixedConstFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.len_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MixedConstFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.len_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MixedConstFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MixedConstFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MixedConstFmt as SpecParser>::spec_parse);
            reveal(<MixedConstFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MixedConstFmt as SpecParser>::spec_parse);
            reveal(<MixedConstFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MixedConstFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MixedConstFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MixedConstFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MixedConstFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MixedConstFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MixedConstFmt as SpecSerializer>::spec_serialize);
            reveal(<MixedConstFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MixedConstFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MixedConstFmt as SpecParser>::spec_parse);
            reveal(<MixedConstFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MixedConstFmt as Consistency>::consistent);
            reveal(<MixedConstFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MixedConstFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MixedConstFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MixedConstFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MixedConstFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MixedConstFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MixedConstFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MixedConstFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MixedConstFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.len_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for PayloadWithHeaderFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.hdr_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for PayloadWithHeaderFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.hdr_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.hdr_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for PayloadWithHeaderFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.hdr_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeaderFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.hdr_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for PayloadWithHeaderFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.hdr_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.hdr_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for PayloadWithHeaderFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.hdr_spec());
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
            let fmt = Self::spec_inner(self.hdr_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for PayloadWithHeaderFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.hdr_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for PayloadWithHeaderFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.hdr_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for PayloadWithHeaderFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<PayloadWithHeaderFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.hdr_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<'i> SafeParser for ChoiceArraysFoldedBodyFmt<'i> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner(self.tag_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl<'i> Productive for ChoiceArraysFoldedBodyFmt<'i> {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.tag_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl<'i> SoundParser for ChoiceArraysFoldedBodyFmt<'i> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<'i> NonTailFmt for ChoiceArraysFoldedBodyFmt<'i> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<'i> GoodSerializer for ChoiceArraysFoldedBodyFmt<'i> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<'i> SPRoundTripDps for ChoiceArraysFoldedBodyFmt<'i> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<'i> NonMalleable for ChoiceArraysFoldedBodyFmt<'i> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<'i> EquivSerializersGeneral for ChoiceArraysFoldedBodyFmt<'i> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<'i> EquivSerializers for ChoiceArraysFoldedBodyFmt<'i> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.tag_spec());
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

    impl<'i> Parser<&'i [u8]> for HeaderFmt {
        type PT = Header;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<HeaderFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, len) = (U16Le).parse(&rest)?;
            if !(len >= 3 && len <= 65535) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, flags) = (U8).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Header { len, flags };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Header> for HeaderFmt {
        fn serialize_into(&self, v: &Header, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<HeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let Header { len, flags } = v;
            U16Le.serialize_into(len, obuf);
            U8.serialize_into(flags, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Header> for HeaderFmt {
        fn prepare(&self, v: &Header) -> Result<usize, PreSerializeError> {
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            let Header { len, flags } = v;
            let l1 = {
                if !(*len >= 3 && *len <= 65535) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (U16Le).prepare(len)
                }
            }?;
            let l2 = (U8).prepare(flags)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for PrimitiveSizesFmt {
        type PT = PrimitiveSizes<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<PrimitiveSizesFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, byte) = (Fixed::<1>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, word) = (Fixed::<2>).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = PrimitiveSizes { byte, word };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, PrimitiveSizes<'i>> for PrimitiveSizesFmt {
        fn serialize_into(&self, v: &PrimitiveSizes<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<PrimitiveSizesFmt as SpecSerializer>::spec_serialize);
            reveal(<PrimitiveSizesFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let PrimitiveSizes { byte, word } = v;
            Fixed::<1>.serialize_into(*byte, obuf);
            Fixed::<2>.serialize_into(*word, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<PrimitiveSizes<'i>> for PrimitiveSizesFmt {
        fn prepare(&self, v: &PrimitiveSizes<'i>) -> Result<usize, PreSerializeError> {
            reveal(<PrimitiveSizesFmt as SpecByteLen>::byte_len);
            let PrimitiveSizes { byte, word } = v;
            let l1 = (Fixed::<1>).prepare(byte)?;
            let l2 = (Fixed::<2>).prepare(word)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for NamedSizeFmt {
        type PT = NamedSize<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NamedSizeFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, bytes) = (Fixed::<3>).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = NamedSize { bytes };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, NamedSize<'i>> for NamedSizeFmt {
        fn serialize_into(&self, v: &NamedSize<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<NamedSizeFmt as SpecSerializer>::spec_serialize);
            reveal(<NamedSizeFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let NamedSize { bytes } = v;
            Fixed::<3>.serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NamedSize<'i>> for NamedSizeFmt {
        fn prepare(&self, v: &NamedSize<'i>) -> Result<usize, PreSerializeError> {
            reveal(<NamedSizeFmt as SpecByteLen>::byte_len);
            let NamedSize { bytes } = v;
            let l1 = (Fixed::<3>).prepare(bytes)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for HeaderAliasFmt {
        type PT = HeaderAlias;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<HeaderAliasFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Named("header", HeaderFmt).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, HeaderAlias> for HeaderAliasFmt {
        fn serialize_into(&self, v: &HeaderAlias, obuf: &mut Output) {
            reveal(<HeaderAliasFmt as SpecSerializer>::spec_serialize);
            reveal(<HeaderAliasFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            HeaderFmt.serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<HeaderAlias> for HeaderAliasFmt {
        fn prepare(&self, v: &HeaderAlias) -> Result<usize, PreSerializeError> {
            reveal(<HeaderAliasFmt as SpecByteLen>::byte_len);
            Named("header", HeaderFmt).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for AliasSizeFmt {
        type PT = AliasSize<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<AliasSizeFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, bytes) = (Fixed::<3>).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = AliasSize { bytes };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, AliasSize<'i>> for AliasSizeFmt {
        fn serialize_into(&self, v: &AliasSize<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<AliasSizeFmt as SpecSerializer>::spec_serialize);
            reveal(<AliasSizeFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let AliasSize { bytes } = v;
            Fixed::<3>.serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<AliasSize<'i>> for AliasSizeFmt {
        fn prepare(&self, v: &AliasSize<'i>) -> Result<usize, PreSerializeError> {
            reveal(<AliasSizeFmt as SpecByteLen>::byte_len);
            let AliasSize { bytes } = v;
            let l1 = (Fixed::<3>).prepare(bytes)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for FixedChoiceFmt {
        type PT = FixedChoice;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<FixedChoiceFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.tag {
                0 => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, FixedChoice::Variant1(v))
                },
                _ => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, FixedChoice::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, FixedChoice> for FixedChoiceFmt {
        fn serialize_into(&self, v: &FixedChoice, obuf: &mut Output) {
            reveal(<FixedChoiceFmt as SpecSerializer>::spec_serialize);
            reveal(<FixedChoiceFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (0, FixedChoice::Variant1(v)) => {
                    (U16Le).serialize_into(v, obuf);
                },
                (_, FixedChoice::Default(v)) => {
                    (U16Le).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<FixedChoice> for FixedChoiceFmt {
        fn prepare(&self, v: &FixedChoice) -> Result<usize, PreSerializeError> {
            reveal(<FixedChoiceFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.tag, v) {
                (0, FixedChoice::Variant1(v)) => (U16Le).prepare(v),
                (x, FixedChoice::Default(v)) if !(x == 0) => (U16Le).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for ChoiceFormatSizeFmt {
        type PT = ChoiceFormatSize<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ChoiceFormatSizeFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, bytes) = (Fixed::<2>).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = ChoiceFormatSize { bytes };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ChoiceFormatSize<'i>> for ChoiceFormatSizeFmt {
        fn serialize_into(&self, v: &ChoiceFormatSize<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<ChoiceFormatSizeFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceFormatSizeFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let ChoiceFormatSize { bytes } = v;
            Fixed::<2>.serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceFormatSize<'i>> for ChoiceFormatSizeFmt {
        fn prepare(&self, v: &ChoiceFormatSize<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceFormatSizeFmt as SpecByteLen>::byte_len);
            let ChoiceFormatSize { bytes } = v;
            let l1 = (Fixed::<2>).prepare(bytes)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for ChoiceTagFmt {
        type PT = ChoiceTag<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ChoiceTagFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Fixed::<2>.parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ChoiceTag<'i>> for ChoiceTagFmt {
        fn serialize_into(&self, v: &ChoiceTag<'i>, obuf: &mut Output) {
            reveal(<ChoiceTagFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceTagFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            Fixed::<2>.serialize_into(*v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceTag<'i>> for ChoiceTagFmt {
        fn prepare(&self, v: &ChoiceTag<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceTagFmt as SpecByteLen>::byte_len);
            (Fixed::<2>).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for ChoiceArraysFoldedFmt {
        type PT = ChoiceArraysFolded<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ChoiceArraysFoldedFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, tag) = (Named("choice_tag", ChoiceTagFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, body) = (Named(
                "choice_arrays_folded_body",
                ChoiceArraysFoldedBodyFmt { tag: tag },
            )).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = ChoiceArraysFolded { tag, body };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        ChoiceArraysFolded<'i>,
    > for ChoiceArraysFoldedFmt {
        fn serialize_into(&self, v: &ChoiceArraysFolded<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<ChoiceArraysFoldedFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceArraysFoldedFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let ChoiceArraysFolded { tag, body } = v;
            ChoiceTagFmt.serialize_into(tag, obuf);
            ChoiceArraysFoldedBodyFmt { tag: *tag }.serialize_into(body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceArraysFolded<'i>> for ChoiceArraysFoldedFmt {
        fn prepare(&self, v: &ChoiceArraysFolded<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceArraysFoldedFmt as SpecByteLen>::byte_len);
            let ChoiceArraysFolded { tag, body } = v;
            let l1 = (Named("choice_tag", ChoiceTagFmt)).prepare(tag)?;
            let l2 = (Named(
                "choice_arrays_folded_body",
                ChoiceArraysFoldedBodyFmt { tag: *tag },
            )).prepare(body)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for SizeArithFmt {
        type PT = SizeArith<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<SizeArithFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, bytes) = (Fixed::<4>).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = SizeArith { bytes };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, SizeArith<'i>> for SizeArithFmt {
        fn serialize_into(&self, v: &SizeArith<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<SizeArithFmt as SpecSerializer>::spec_serialize);
            reveal(<SizeArithFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let SizeArith { bytes } = v;
            Fixed::<4>.serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<SizeArith<'i>> for SizeArithFmt {
        fn prepare(&self, v: &SizeArith<'i>) -> Result<usize, PreSerializeError> {
            reveal(<SizeArithFmt as SpecByteLen>::byte_len);
            let SizeArith { bytes } = v;
            let l1 = (Fixed::<4>).prepare(bytes)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for SimpleSubFmt {
        type PT = SimpleSub<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<SimpleSubFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, data) = (Varied(((self.len - 3) - 1))).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = SimpleSub { data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, SimpleSub<'i>> for SimpleSubFmt {
        fn serialize_into(&self, v: &SimpleSub<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<SimpleSubFmt as SpecSerializer>::spec_serialize);
            reveal(<SimpleSubFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let SimpleSub { data } = v;
            Varied(((self.len - 3) - 1)).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<SimpleSub<'i>> for SimpleSubFmt {
        fn prepare(&self, v: &SimpleSub<'i>) -> Result<usize, PreSerializeError> {
            reveal(<SimpleSubFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let SimpleSub { data } = v;
            let l1 = (Varied(((self.len - 3) - 1))).prepare(data)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for MultiArithFmt {
        type PT = MultiArith<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MultiArithFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, body) = (Varied(((self.total - self.hdr_len) - 8))).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = MultiArith { body };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, MultiArith<'i>> for MultiArithFmt {
        fn serialize_into(&self, v: &MultiArith<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<MultiArithFmt as SpecSerializer>::spec_serialize);
            reveal(<MultiArithFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let MultiArith { body } = v;
            Varied(((self.total - self.hdr_len) - 8)).serialize_into(*body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MultiArith<'i>> for MultiArithFmt {
        fn prepare(&self, v: &MultiArith<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MultiArithFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let MultiArith { body } = v;
            let l1 = (Varied(((self.total - self.hdr_len) - 8))).prepare(body)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for ParenExprFmt {
        type PT = ParenExpr<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ParenExprFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, data) = (Varied(((self.a - self.b) + self.c))).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = ParenExpr { data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ParenExpr<'i>> for ParenExprFmt {
        fn serialize_into(&self, v: &ParenExpr<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<ParenExprFmt as SpecSerializer>::spec_serialize);
            reveal(<ParenExprFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let ParenExpr { data } = v;
            Varied(((self.a - self.b) + self.c)).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ParenExpr<'i>> for ParenExprFmt {
        fn prepare(&self, v: &ParenExpr<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ParenExprFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ParenExpr { data } = v;
            let l1 = (Varied(((self.a - self.b) + self.c))).prepare(data)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for MixedConstFmt {
        type PT = MixedConst<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MixedConstFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, data) = (Varied(((self.len - 4) + 2))).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = MixedConst { data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, MixedConst<'i>> for MixedConstFmt {
        fn serialize_into(&self, v: &MixedConst<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<MixedConstFmt as SpecSerializer>::spec_serialize);
            reveal(<MixedConstFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let MixedConst { data } = v;
            Varied(((self.len - 4) + 2)).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MixedConst<'i>> for MixedConstFmt {
        fn prepare(&self, v: &MixedConst<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MixedConstFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let MixedConst { data } = v;
            let l1 = (Varied(((self.len - 4) + 2))).prepare(data)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for PayloadWithHeaderFmt {
        type PT = PayloadWithHeader<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, data) = (Varied((self.hdr.len - 3))).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = PayloadWithHeader { data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, PayloadWithHeader<'i>> for PayloadWithHeaderFmt {
        fn serialize_into(&self, v: &PayloadWithHeader<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let PayloadWithHeader { data } = v;
            Varied((self.hdr.len - 3)).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<PayloadWithHeader<'i>> for PayloadWithHeaderFmt {
        fn prepare(&self, v: &PayloadWithHeader<'i>) -> Result<usize, PreSerializeError> {
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let PayloadWithHeader { data } = v;
            let l1 = (Varied((self.hdr.len - 3))).prepare(data)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for ChoiceArraysFoldedBodyFmt<'i> {
        type PT = ChoiceArraysFoldedBody;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ChoiceArraysFoldedBodyFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.tag {
                x if bytes_eq(x, &[0x00, 0x00]) => {
                    let (n, v) = (U8).parse(&rest)?;
                    (n, ChoiceArraysFoldedBody::Variant1(v))
                },
                x if bytes_eq(x, &[0x01, 0x01]) => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, ChoiceArraysFoldedBody::Variant2(v))
                },
                _ => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, ChoiceArraysFoldedBody::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        ChoiceArraysFoldedBody,
    > for ChoiceArraysFoldedBodyFmt<'i> {
        fn serialize_into(&self, v: &ChoiceArraysFoldedBody, obuf: &mut Output) {
            reveal(<ChoiceArraysFoldedBodyFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceArraysFoldedBodyFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (x, ChoiceArraysFoldedBody::Variant1(v)) if bytes_eq(x, &[0x00, 0x00]) => {
                    (U8).serialize_into(v, obuf);
                },
                (x, ChoiceArraysFoldedBody::Variant2(v)) if bytes_eq(x, &[0x01, 0x01]) => {
                    (U16Le).serialize_into(v, obuf);
                },
                (_, ChoiceArraysFoldedBody::Default(v)) => {
                    (U16Le).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceArraysFoldedBody> for ChoiceArraysFoldedBodyFmt<'i> {
        fn prepare(&self, v: &ChoiceArraysFoldedBody) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceArraysFoldedBodyFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            proof {
                let ghost arr0 = [0x00u8, 0x00u8].deep_view();
                let ghost arr1 = [0x01u8, 0x01u8].deep_view();
                assert(arr0 != arr1) by {
                    assert(arr0[0] != arr1[0]);
                };
            }

            match (self.tag, v) {
                (x, ChoiceArraysFoldedBody::Variant1(v)) if bytes_eq(x, &[0x00, 0x00]) => (
                U8).prepare(v),
                (x, ChoiceArraysFoldedBody::Variant2(v)) if bytes_eq(x, &[0x01, 0x01]) => (
                U16Le).prepare(v),
                (x, ChoiceArraysFoldedBody::Default(v)) if !bytes_eq(x, &[0x00, 0x00]) && !bytes_eq(
                    x,
                    &[0x01, 0x01],
                ) => (U16Le).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}

} // verus!
