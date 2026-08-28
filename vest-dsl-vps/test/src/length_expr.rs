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
# [doc = "data type for `header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Header {
    pub len: u16,
    pub flags: u8,
}

# [verifier::ext_equal]
pub struct HeaderSpec<T0 = u16, T1 = u8> {
    pub len: T0,
    pub flags: T1,
}

pub type HeaderInner = (u16, u8);

impl DeepView for Header {
    type V = HeaderSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        HeaderSpec { len: self.len.deep_view(), flags: self.flags.deep_view() }
    }
}

impl Header {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().len == self.len.deep_view(),
            self.deep_view().flags == self.flags.deep_view(),
    {
        reveal(<Header as DeepView>::deep_view);
    }
}

impl<T0, T1> HeaderSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (len, flags) = input;
        Self { len, flags }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { len, flags } = self;
        (len, flags)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(HeaderSpec::from_structural);
        reveal(HeaderSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(HeaderSpec::from_structural);
        reveal(HeaderSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { len, flags } => (len, flags),
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

# [doc = "data type for `primitive_sizes`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct PrimitiveSizes<'i> {
    pub byte: &'i [u8],
    pub word: &'i [u8],
}

# [verifier::ext_equal]
pub struct PrimitiveSizesSpec<T0 = Seq<u8>, T1 = Seq<u8>> {
    pub byte: T0,
    pub word: T1,
}

pub type PrimitiveSizesInner = (Seq<u8>, Seq<u8>);

impl<'i> DeepView for PrimitiveSizes<'i> {
    type V = PrimitiveSizesSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        PrimitiveSizesSpec { byte: self.byte.deep_view(), word: self.word.deep_view() }
    }
}

impl<'i> PrimitiveSizes<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().byte == self.byte.deep_view(),
            self.deep_view().word == self.word.deep_view(),
    {
        reveal(<PrimitiveSizes as DeepView>::deep_view);
    }
}

impl<T0, T1> PrimitiveSizesSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (byte, word) = input;
        Self { byte, word }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { byte, word } = self;
        (byte, word)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(PrimitiveSizesSpec::from_structural);
        reveal(PrimitiveSizesSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(PrimitiveSizesSpec::from_structural);
        reveal(PrimitiveSizesSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { byte, word } => (byte, word),
            },
    {
        reveal(PrimitiveSizesSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct PrimitiveSizesForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct PrimitiveSizesReverse;

impl SpecMap for PrimitiveSizesForward {
    type Input = PrimitiveSizesInner;

    type Output = PrimitiveSizesSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        PrimitiveSizesSpec::from_structural(input)
    }
}

impl SpecMap for PrimitiveSizesReverse {
    type Input = PrimitiveSizesSpec;

    type Output = PrimitiveSizesInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `named_size`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct NamedSize<'i> {
    pub bytes: &'i [u8],
}

# [verifier::ext_equal]
pub struct NamedSizeSpec<T0 = Seq<u8>> {
    pub bytes: T0,
}

pub type NamedSizeInner = Seq<u8>;

impl<'i> DeepView for NamedSize<'i> {
    type V = NamedSizeSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        NamedSizeSpec { bytes: self.bytes.deep_view() }
    }
}

impl<'i> NamedSize<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().bytes == self.bytes.deep_view(),
    {
        reveal(<NamedSize as DeepView>::deep_view);
    }
}

impl<T0> NamedSizeSpec<T0> {
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
        reveal(NamedSizeSpec::from_structural);
        reveal(NamedSizeSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(NamedSizeSpec::from_structural);
        reveal(NamedSizeSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { bytes } => bytes,
            },
    {
        reveal(NamedSizeSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NamedSizeForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NamedSizeReverse;

impl SpecMap for NamedSizeForward {
    type Input = NamedSizeInner;

    type Output = NamedSizeSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        NamedSizeSpec::from_structural(input)
    }
}

impl SpecMap for NamedSizeReverse {
    type Input = NamedSizeSpec;

    type Output = NamedSizeInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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
pub struct AliasSizeSpec<T0 = Seq<u8>> {
    pub bytes: T0,
}

pub type AliasSizeInner = Seq<u8>;

impl<'i> DeepView for AliasSize<'i> {
    type V = AliasSizeSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        AliasSizeSpec { bytes: self.bytes.deep_view() }
    }
}

impl<'i> AliasSize<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().bytes == self.bytes.deep_view(),
    {
        reveal(<AliasSize as DeepView>::deep_view);
    }
}

impl<T0> AliasSizeSpec<T0> {
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
        reveal(AliasSizeSpec::from_structural);
        reveal(AliasSizeSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(AliasSizeSpec::from_structural);
        reveal(AliasSizeSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { bytes } => bytes,
            },
    {
        reveal(AliasSizeSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct AliasSizeForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct AliasSizeReverse;

impl SpecMap for AliasSizeForward {
    type Input = AliasSizeInner;

    type Output = AliasSizeSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        AliasSizeSpec::from_structural(input)
    }
}

impl SpecMap for AliasSizeReverse {
    type Input = AliasSizeSpec;

    type Output = AliasSizeInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `fixed_choice`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum FixedChoice {
    Variant1(u16),
    Default(u16),
}

# [verifier::ext_equal]
pub enum FixedChoiceSpec<T0 = u16, T1 = u16> {
    Variant1(T0),
    Default(T1),
}

pub type FixedChoiceInner = Sum<u16, u16>;

impl DeepView for FixedChoice {
    type V = FixedChoiceSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            FixedChoice::Variant1(v) => FixedChoiceSpec::Variant1(v.deep_view()),
            FixedChoice::Default(v) => FixedChoiceSpec::Default(v.deep_view()),
        }
    }
}

impl FixedChoice {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                FixedChoice::Variant1(v) => FixedChoiceSpec::Variant1(v.deep_view()),
                FixedChoice::Default(v) => FixedChoiceSpec::Default(v.deep_view()),
            },
    {
        reveal(<FixedChoice as DeepView>::deep_view);
    }
}

impl<T0, T1> FixedChoiceSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, T1>) -> Self {
        match input {
            L(value) => Self::Variant1(value),
            R(value) => Self::Default(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, T1> {
        match self {
            Self::Variant1(value) => L(value),
            Self::Default(value) => R(value),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(FixedChoiceSpec::from_structural);
        reveal(FixedChoiceSpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(FixedChoiceSpec::from_structural);
        reveal(FixedChoiceSpec::into_structural);
        match input {
            L(_) => {},
            R(_) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::Variant1(value) => L(value),
                Self::Default(value) => R(value),
            },
    {
        reveal(FixedChoiceSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct FixedChoiceForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct FixedChoiceReverse;

impl SpecMap for FixedChoiceForward {
    type Input = FixedChoiceInner;

    type Output = FixedChoiceSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        FixedChoiceSpec::from_structural(input)
    }
}

impl SpecMap for FixedChoiceReverse {
    type Input = FixedChoiceSpec;

    type Output = FixedChoiceInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `choice_format_size`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct ChoiceFormatSize<'i> {
    pub bytes: &'i [u8],
}

# [verifier::ext_equal]
pub struct ChoiceFormatSizeSpec<T0 = Seq<u8>> {
    pub bytes: T0,
}

pub type ChoiceFormatSizeInner = Seq<u8>;

impl<'i> DeepView for ChoiceFormatSize<'i> {
    type V = ChoiceFormatSizeSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        ChoiceFormatSizeSpec { bytes: self.bytes.deep_view() }
    }
}

impl<'i> ChoiceFormatSize<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().bytes == self.bytes.deep_view(),
    {
        reveal(<ChoiceFormatSize as DeepView>::deep_view);
    }
}

impl<T0> ChoiceFormatSizeSpec<T0> {
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
        reveal(ChoiceFormatSizeSpec::from_structural);
        reveal(ChoiceFormatSizeSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(ChoiceFormatSizeSpec::from_structural);
        reveal(ChoiceFormatSizeSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { bytes } => bytes,
            },
    {
        reveal(ChoiceFormatSizeSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceFormatSizeForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceFormatSizeReverse;

impl SpecMap for ChoiceFormatSizeForward {
    type Input = ChoiceFormatSizeInner;

    type Output = ChoiceFormatSizeSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        ChoiceFormatSizeSpec::from_structural(input)
    }
}

impl SpecMap for ChoiceFormatSizeReverse {
    type Input = ChoiceFormatSizeSpec;

    type Output = ChoiceFormatSizeInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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
pub struct ChoiceArraysFoldedSpec<T0 = ChoiceTagSpec, T1 = ChoiceArraysFoldedBodySpec> {
    pub tag: T0,
    pub body: T1,
}

pub type ChoiceArraysFoldedInner = (ChoiceTagSpec, ChoiceArraysFoldedBodySpec);

impl<'i> DeepView for ChoiceArraysFolded<'i> {
    type V = ChoiceArraysFoldedSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        ChoiceArraysFoldedSpec { tag: self.tag.deep_view(), body: self.body.deep_view() }
    }
}

impl<'i> ChoiceArraysFolded<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().tag == self.tag.deep_view(),
            self.deep_view().body == self.body.deep_view(),
    {
        reveal(<ChoiceArraysFolded as DeepView>::deep_view);
    }
}

impl<T0, T1> ChoiceArraysFoldedSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (tag, body) = input;
        Self { tag, body }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { tag, body } = self;
        (tag, body)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(ChoiceArraysFoldedSpec::from_structural);
        reveal(ChoiceArraysFoldedSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(ChoiceArraysFoldedSpec::from_structural);
        reveal(ChoiceArraysFoldedSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { tag, body } => (tag, body),
            },
    {
        reveal(ChoiceArraysFoldedSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceArraysFoldedForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceArraysFoldedReverse;

impl SpecMap for ChoiceArraysFoldedForward {
    type Input = ChoiceArraysFoldedInner;

    type Output = ChoiceArraysFoldedSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        ChoiceArraysFoldedSpec::from_structural(input)
    }
}

impl SpecMap for ChoiceArraysFoldedReverse {
    type Input = ChoiceArraysFoldedSpec;

    type Output = ChoiceArraysFoldedInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `size_arith`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct SizeArith<'i> {
    pub bytes: &'i [u8],
}

# [verifier::ext_equal]
pub struct SizeArithSpec<T0 = Seq<u8>> {
    pub bytes: T0,
}

pub type SizeArithInner = Seq<u8>;

impl<'i> DeepView for SizeArith<'i> {
    type V = SizeArithSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        SizeArithSpec { bytes: self.bytes.deep_view() }
    }
}

impl<'i> SizeArith<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().bytes == self.bytes.deep_view(),
    {
        reveal(<SizeArith as DeepView>::deep_view);
    }
}

impl<T0> SizeArithSpec<T0> {
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
        reveal(SizeArithSpec::from_structural);
        reveal(SizeArithSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(SizeArithSpec::from_structural);
        reveal(SizeArithSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { bytes } => bytes,
            },
    {
        reveal(SizeArithSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct SizeArithForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct SizeArithReverse;

impl SpecMap for SizeArithForward {
    type Input = SizeArithInner;

    type Output = SizeArithSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        SizeArithSpec::from_structural(input)
    }
}

impl SpecMap for SizeArithReverse {
    type Input = SizeArithSpec;

    type Output = SizeArithInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `simple_sub`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct SimpleSub<'i> {
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct SimpleSubSpec<T0 = Seq<u8>> {
    pub data: T0,
}

pub type SimpleSubInner = Seq<u8>;

impl<'i> DeepView for SimpleSub<'i> {
    type V = SimpleSubSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        SimpleSubSpec { data: self.data.deep_view() }
    }
}

impl<'i> SimpleSub<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<SimpleSub as DeepView>::deep_view);
    }
}

impl<T0> SimpleSubSpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let data = input;
        Self { data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { data } = self;
        data
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(SimpleSubSpec::from_structural);
        reveal(SimpleSubSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(SimpleSubSpec::from_structural);
        reveal(SimpleSubSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { data } => data,
            },
    {
        reveal(SimpleSubSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct SimpleSubForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct SimpleSubReverse;

impl SpecMap for SimpleSubForward {
    type Input = SimpleSubInner;

    type Output = SimpleSubSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        SimpleSubSpec::from_structural(input)
    }
}

impl SpecMap for SimpleSubReverse {
    type Input = SimpleSubSpec;

    type Output = SimpleSubInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `multi_arith`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct MultiArith<'i> {
    pub body: &'i [u8],
}

# [verifier::ext_equal]
pub struct MultiArithSpec<T0 = Seq<u8>> {
    pub body: T0,
}

pub type MultiArithInner = Seq<u8>;

impl<'i> DeepView for MultiArith<'i> {
    type V = MultiArithSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        MultiArithSpec { body: self.body.deep_view() }
    }
}

impl<'i> MultiArith<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().body == self.body.deep_view(),
    {
        reveal(<MultiArith as DeepView>::deep_view);
    }
}

impl<T0> MultiArithSpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let body = input;
        Self { body }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { body } = self;
        body
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(MultiArithSpec::from_structural);
        reveal(MultiArithSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(MultiArithSpec::from_structural);
        reveal(MultiArithSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { body } => body,
            },
    {
        reveal(MultiArithSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MultiArithForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MultiArithReverse;

impl SpecMap for MultiArithForward {
    type Input = MultiArithInner;

    type Output = MultiArithSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        MultiArithSpec::from_structural(input)
    }
}

impl SpecMap for MultiArithReverse {
    type Input = MultiArithSpec;

    type Output = MultiArithInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `paren_expr`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct ParenExpr<'i> {
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct ParenExprSpec<T0 = Seq<u8>> {
    pub data: T0,
}

pub type ParenExprInner = Seq<u8>;

impl<'i> DeepView for ParenExpr<'i> {
    type V = ParenExprSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        ParenExprSpec { data: self.data.deep_view() }
    }
}

impl<'i> ParenExpr<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<ParenExpr as DeepView>::deep_view);
    }
}

impl<T0> ParenExprSpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let data = input;
        Self { data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { data } = self;
        data
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(ParenExprSpec::from_structural);
        reveal(ParenExprSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(ParenExprSpec::from_structural);
        reveal(ParenExprSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { data } => data,
            },
    {
        reveal(ParenExprSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ParenExprForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ParenExprReverse;

impl SpecMap for ParenExprForward {
    type Input = ParenExprInner;

    type Output = ParenExprSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        ParenExprSpec::from_structural(input)
    }
}

impl SpecMap for ParenExprReverse {
    type Input = ParenExprSpec;

    type Output = ParenExprInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `mixed_const`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct MixedConst<'i> {
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct MixedConstSpec<T0 = Seq<u8>> {
    pub data: T0,
}

pub type MixedConstInner = Seq<u8>;

impl<'i> DeepView for MixedConst<'i> {
    type V = MixedConstSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        MixedConstSpec { data: self.data.deep_view() }
    }
}

impl<'i> MixedConst<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<MixedConst as DeepView>::deep_view);
    }
}

impl<T0> MixedConstSpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let data = input;
        Self { data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { data } = self;
        data
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(MixedConstSpec::from_structural);
        reveal(MixedConstSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(MixedConstSpec::from_structural);
        reveal(MixedConstSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { data } => data,
            },
    {
        reveal(MixedConstSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MixedConstForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MixedConstReverse;

impl SpecMap for MixedConstForward {
    type Input = MixedConstInner;

    type Output = MixedConstSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        MixedConstSpec::from_structural(input)
    }
}

impl SpecMap for MixedConstReverse {
    type Input = MixedConstSpec;

    type Output = MixedConstInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `payload_with_header`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct PayloadWithHeader<'i> {
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct PayloadWithHeaderSpec<T0 = Seq<u8>> {
    pub data: T0,
}

pub type PayloadWithHeaderInner = Seq<u8>;

impl<'i> DeepView for PayloadWithHeader<'i> {
    type V = PayloadWithHeaderSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        PayloadWithHeaderSpec { data: self.data.deep_view() }
    }
}

impl<'i> PayloadWithHeader<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().data == self.data.deep_view(),
    {
        reveal(<PayloadWithHeader as DeepView>::deep_view);
    }
}

impl<T0> PayloadWithHeaderSpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let data = input;
        Self { data }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { data } = self;
        data
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(PayloadWithHeaderSpec::from_structural);
        reveal(PayloadWithHeaderSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(PayloadWithHeaderSpec::from_structural);
        reveal(PayloadWithHeaderSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { data } => data,
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

# [doc = "data type for `choice_arrays_folded_body`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum ChoiceArraysFoldedBody {
    Variant1(u8),
    Variant2(u16),
    Default(u16),
}

# [verifier::ext_equal]
pub enum ChoiceArraysFoldedBodySpec<T0 = u8, T1 = u16, T2 = u16> {
    Variant1(T0),
    Variant2(T1),
    Default(T2),
}

pub type ChoiceArraysFoldedBodyInner = Sum<u8, Sum<u16, u16>>;

impl DeepView for ChoiceArraysFoldedBody {
    type V = ChoiceArraysFoldedBodySpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            ChoiceArraysFoldedBody::Variant1(v) => ChoiceArraysFoldedBodySpec::Variant1(
                v.deep_view(),
            ),
            ChoiceArraysFoldedBody::Variant2(v) => ChoiceArraysFoldedBodySpec::Variant2(
                v.deep_view(),
            ),
            ChoiceArraysFoldedBody::Default(v) => ChoiceArraysFoldedBodySpec::Default(
                v.deep_view(),
            ),
        }
    }
}

impl ChoiceArraysFoldedBody {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                ChoiceArraysFoldedBody::Variant1(v) => ChoiceArraysFoldedBodySpec::Variant1(
                    v.deep_view(),
                ),
                ChoiceArraysFoldedBody::Variant2(v) => ChoiceArraysFoldedBodySpec::Variant2(
                    v.deep_view(),
                ),
                ChoiceArraysFoldedBody::Default(v) => ChoiceArraysFoldedBodySpec::Default(
                    v.deep_view(),
                ),
            },
    {
        reveal(<ChoiceArraysFoldedBody as DeepView>::deep_view);
    }
}

impl<T0, T1, T2> ChoiceArraysFoldedBodySpec<T0, T1, T2> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, Sum<T1, T2>>) -> Self {
        match input {
            L(value) => Self::Variant1(value),
            R(L(value)) => Self::Variant2(value),
            R(R(value)) => Self::Default(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, Sum<T1, T2>> {
        match self {
            Self::Variant1(value) => L(value),
            Self::Variant2(value) => R(L(value)),
            Self::Default(value) => R(R(value)),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(ChoiceArraysFoldedBodySpec::from_structural);
        reveal(ChoiceArraysFoldedBodySpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Variant2(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, Sum<T1, T2>>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(ChoiceArraysFoldedBodySpec::from_structural);
        reveal(ChoiceArraysFoldedBodySpec::into_structural);
        match input {
            L(_) => {},
            R(L(_)) => {},
            R(R(_)) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::Variant1(value) => L(value),
                Self::Variant2(value) => R(L(value)),
                Self::Default(value) => R(R(value)),
            },
    {
        reveal(ChoiceArraysFoldedBodySpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceArraysFoldedBodyForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceArraysFoldedBodyReverse;

impl SpecMap for ChoiceArraysFoldedBodyForward {
    type Input = ChoiceArraysFoldedBodyInner;

    type Output = ChoiceArraysFoldedBodySpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        ChoiceArraysFoldedBodySpec::from_structural(input)
    }
}

impl SpecMap for ChoiceArraysFoldedBodyReverse {
    type Input = ChoiceArraysFoldedBodySpec;

    type Output = ChoiceArraysFoldedBodyInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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
        BiMap<HeaderForward, HeaderReverse>,
    >,
>;

impl HeaderFmt {
    # [doc = "specification constructor for `header`."]
    pub open spec fn spec_inner() -> HeaderFmtSpec {
        Named(
            "header",
            Mapped {
                inner: Bind(Refined(U16Le, |x: u16| x >= 3 && x <= 65535), |len: u16| U8),
                mapper: BiMap(HeaderForward, HeaderReverse),
            },
        )
    }
}

# [doc = "named format combinator for `primitive_sizes`."]
# [derive (Clone, Copy)]
pub struct PrimitiveSizesFmt;

pub type PrimitiveSizesFmtSpec = Named<
    Mapped<Pair<Fixed<1>, Fixed<2>>, BiMap<PrimitiveSizesForward, PrimitiveSizesReverse>>,
>;

impl PrimitiveSizesFmt {
    # [doc = "specification constructor for `primitive_sizes`."]
    pub open spec fn spec_inner() -> PrimitiveSizesFmtSpec {
        Named(
            "primitive_sizes",
            Mapped {
                inner: Pair(Fixed::<1>, Fixed::<2>),
                mapper: BiMap(PrimitiveSizesForward, PrimitiveSizesReverse),
            },
        )
    }
}

# [doc = "named format combinator for `named_size`."]
# [derive (Clone, Copy)]
pub struct NamedSizeFmt;

pub type NamedSizeFmtSpec = Named<Mapped<Fixed<3>, BiMap<NamedSizeForward, NamedSizeReverse>>>;

impl NamedSizeFmt {
    # [doc = "specification constructor for `named_size`."]
    pub open spec fn spec_inner() -> NamedSizeFmtSpec {
        Named(
            "named_size",
            Mapped { inner: Fixed::<3>, mapper: BiMap(NamedSizeForward, NamedSizeReverse) },
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

pub type AliasSizeFmtSpec = Named<Mapped<Fixed<3>, BiMap<AliasSizeForward, AliasSizeReverse>>>;

impl AliasSizeFmt {
    # [doc = "specification constructor for `alias_size`."]
    pub open spec fn spec_inner() -> AliasSizeFmtSpec {
        Named(
            "alias_size",
            Mapped { inner: Fixed::<3>, mapper: BiMap(AliasSizeForward, AliasSizeReverse) },
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
    Mapped<Sum<U16Le, U16Le>, BiMap<FixedChoiceForward, FixedChoiceReverse>>,
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
                mapper: BiMap(FixedChoiceForward, FixedChoiceReverse),
            },
        )
    }
}

# [doc = "named format combinator for `choice_format_size`."]
# [derive (Clone, Copy)]
pub struct ChoiceFormatSizeFmt;

pub type ChoiceFormatSizeFmtSpec = Named<
    Mapped<Fixed<2>, BiMap<ChoiceFormatSizeForward, ChoiceFormatSizeReverse>>,
>;

impl ChoiceFormatSizeFmt {
    # [doc = "specification constructor for `choice_format_size`."]
    pub open spec fn spec_inner() -> ChoiceFormatSizeFmtSpec {
        Named(
            "choice_format_size",
            Mapped {
                inner: Fixed::<2>,
                mapper: BiMap(ChoiceFormatSizeForward, ChoiceFormatSizeReverse),
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
        BiMap<ChoiceArraysFoldedForward, ChoiceArraysFoldedReverse>,
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
                mapper: BiMap(ChoiceArraysFoldedForward, ChoiceArraysFoldedReverse),
            },
        )
    }
}

# [doc = "named format combinator for `size_arith`."]
# [derive (Clone, Copy)]
pub struct SizeArithFmt;

pub type SizeArithFmtSpec = Named<Mapped<Fixed<4>, BiMap<SizeArithForward, SizeArithReverse>>>;

impl SizeArithFmt {
    # [doc = "specification constructor for `size_arith`."]
    pub open spec fn spec_inner() -> SizeArithFmtSpec {
        Named(
            "size_arith",
            Mapped { inner: Fixed::<4>, mapper: BiMap(SizeArithForward, SizeArithReverse) },
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

pub type SimpleSubFmtSpec = Named<Mapped<Varied<u16>, BiMap<SimpleSubForward, SimpleSubReverse>>>;

impl SimpleSubFmt {
    # [doc = "specification constructor for `simple_sub`."]
    pub open spec fn spec_inner(len: u16) -> SimpleSubFmtSpec {
        Named(
            "simple_sub",
            Mapped {
                inner: Varied(((((len - 3) as u16) - 1) as u16)),
                mapper: BiMap(SimpleSubForward, SimpleSubReverse),
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
    Mapped<Varied<u16>, BiMap<MultiArithForward, MultiArithReverse>>,
>;

impl MultiArithFmt {
    # [doc = "specification constructor for `multi_arith`."]
    pub open spec fn spec_inner(total: u16, hdr_len: u16) -> MultiArithFmtSpec {
        Named(
            "multi_arith",
            Mapped {
                inner: Varied(((((total - hdr_len) as u16) - 8) as u16)),
                mapper: BiMap(MultiArithForward, MultiArithReverse),
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

pub type ParenExprFmtSpec = Named<Mapped<Varied<u16>, BiMap<ParenExprForward, ParenExprReverse>>>;

impl ParenExprFmt {
    # [doc = "specification constructor for `paren_expr`."]
    pub open spec fn spec_inner(a: u16, b: u16, c: u16) -> ParenExprFmtSpec {
        Named(
            "paren_expr",
            Mapped {
                inner: Varied(((((a - b) as u16) + c) as u16)),
                mapper: BiMap(ParenExprForward, ParenExprReverse),
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
    Mapped<Varied<u16>, BiMap<MixedConstForward, MixedConstReverse>>,
>;

impl MixedConstFmt {
    # [doc = "specification constructor for `mixed_const`."]
    pub open spec fn spec_inner(len: u16) -> MixedConstFmtSpec {
        Named(
            "mixed_const",
            Mapped {
                inner: Varied(((((len - 4) as u16) + 2) as u16)),
                mapper: BiMap(MixedConstForward, MixedConstReverse),
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
    Mapped<Varied<u16>, BiMap<PayloadWithHeaderForward, PayloadWithHeaderReverse>>,
>;

impl PayloadWithHeaderFmt {
    # [doc = "specification constructor for `payload_with_header`."]
    pub open spec fn spec_inner(hdr: HeaderSpec) -> PayloadWithHeaderFmtSpec {
        Named(
            "payload_with_header",
            Mapped {
                inner: Varied(((hdr.len - 3) as u16)),
                mapper: BiMap(PayloadWithHeaderForward, PayloadWithHeaderReverse),
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
        BiMap<ChoiceArraysFoldedBodyForward, ChoiceArraysFoldedBodyReverse>,
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
                mapper: BiMap(ChoiceArraysFoldedBodyForward, ChoiceArraysFoldedBodyReverse),
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

    broadcast use {
        vps_lib::combinators::disjoint::disjointness_lemmas,
        HeaderSpec::lemma_from_into,
        HeaderSpec::lemma_into_from,
        PrimitiveSizesSpec::lemma_from_into,
        PrimitiveSizesSpec::lemma_into_from,
        NamedSizeSpec::lemma_from_into,
        NamedSizeSpec::lemma_into_from,
        AliasSizeSpec::lemma_from_into,
        AliasSizeSpec::lemma_into_from,
        FixedChoiceSpec::lemma_from_into,
        FixedChoiceSpec::lemma_into_from,
        ChoiceFormatSizeSpec::lemma_from_into,
        ChoiceFormatSizeSpec::lemma_into_from,
        ChoiceArraysFoldedSpec::lemma_from_into,
        ChoiceArraysFoldedSpec::lemma_into_from,
        SizeArithSpec::lemma_from_into,
        SizeArithSpec::lemma_into_from,
        SimpleSubSpec::lemma_from_into,
        SimpleSubSpec::lemma_into_from,
        MultiArithSpec::lemma_from_into,
        MultiArithSpec::lemma_into_from,
        ParenExprSpec::lemma_from_into,
        ParenExprSpec::lemma_into_from,
        MixedConstSpec::lemma_from_into,
        MixedConstSpec::lemma_into_from,
        PayloadWithHeaderSpec::lemma_from_into,
        PayloadWithHeaderSpec::lemma_into_from,
        ChoiceArraysFoldedBodySpec::lemma_from_into,
        ChoiceArraysFoldedBodySpec::lemma_into_from,
    };

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
            assert forall|input: PrimitiveSizesInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                PrimitiveSizesSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecParser>::spec_parse);
            reveal(<PrimitiveSizesFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: PrimitiveSizesInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                PrimitiveSizesSpec::lemma_into_from(input);
            }
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
            assert forall|output: PrimitiveSizesSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                PrimitiveSizesSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for PrimitiveSizesFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<PrimitiveSizesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: PrimitiveSizesInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                PrimitiveSizesSpec::lemma_into_from(input);
            }
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
            assert forall|input: NamedSizeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NamedSizeSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecParser>::spec_parse);
            reveal(<NamedSizeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: NamedSizeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NamedSizeSpec::lemma_into_from(input);
            }
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
            assert forall|output: NamedSizeSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                NamedSizeSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NamedSizeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NamedSizeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: NamedSizeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NamedSizeSpec::lemma_into_from(input);
            }
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
            assert forall|input: AliasSizeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                AliasSizeSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecParser>::spec_parse);
            reveal(<AliasSizeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: AliasSizeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                AliasSizeSpec::lemma_into_from(input);
            }
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
            assert forall|output: AliasSizeSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                AliasSizeSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AliasSizeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AliasSizeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: AliasSizeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                AliasSizeSpec::lemma_into_from(input);
            }
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
            assert forall|input: FixedChoiceInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                FixedChoiceSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecParser>::spec_parse);
            reveal(<FixedChoiceFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.tag_spec());
            assert forall|input: FixedChoiceInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                FixedChoiceSpec::lemma_into_from(input);
            }
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
            assert forall|output: FixedChoiceSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                FixedChoiceSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for FixedChoiceFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<FixedChoiceFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert forall|input: FixedChoiceInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                FixedChoiceSpec::lemma_into_from(input);
            }
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
            assert forall|input: ChoiceFormatSizeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ChoiceFormatSizeSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecParser>::spec_parse);
            reveal(<ChoiceFormatSizeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: ChoiceFormatSizeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ChoiceFormatSizeSpec::lemma_into_from(input);
            }
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
            assert forall|output: ChoiceFormatSizeSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                ChoiceFormatSizeSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ChoiceFormatSizeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ChoiceFormatSizeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: ChoiceFormatSizeInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ChoiceFormatSizeSpec::lemma_into_from(input);
            }
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
            assert forall|input: ChoiceArraysFoldedInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ChoiceArraysFoldedSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecParser>::spec_parse);
            reveal(<ChoiceArraysFoldedFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: ChoiceArraysFoldedInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ChoiceArraysFoldedSpec::lemma_into_from(input);
            }
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
            assert forall|output: ChoiceArraysFoldedSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                ChoiceArraysFoldedSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ChoiceArraysFoldedFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ChoiceArraysFoldedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: ChoiceArraysFoldedInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ChoiceArraysFoldedSpec::lemma_into_from(input);
            }
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
            assert forall|input: SizeArithInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                SizeArithSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<SizeArithFmt as SpecParser>::spec_parse);
            reveal(<SizeArithFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: SizeArithInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                SizeArithSpec::lemma_into_from(input);
            }
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
            assert forall|output: SizeArithSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                SizeArithSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for SizeArithFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<SizeArithFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: SizeArithInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                SizeArithSpec::lemma_into_from(input);
            }
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
            assert forall|input: SimpleSubInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                SimpleSubSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecParser>::spec_parse);
            reveal(<SimpleSubFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.len_spec());
            assert forall|input: SimpleSubInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                SimpleSubSpec::lemma_into_from(input);
            }
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
            assert forall|output: SimpleSubSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                SimpleSubSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for SimpleSubFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<SimpleSubFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.len_spec());
            assert forall|input: SimpleSubInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                SimpleSubSpec::lemma_into_from(input);
            }
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
            assert forall|input: MultiArithInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                MultiArithSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MultiArithFmt as SpecParser>::spec_parse);
            reveal(<MultiArithFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert forall|input: MultiArithInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                MultiArithSpec::lemma_into_from(input);
            }
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
            assert forall|output: MultiArithSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                MultiArithSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MultiArithFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MultiArithFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.total_spec(), self.hdr_len_spec());
            assert forall|input: MultiArithInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                MultiArithSpec::lemma_into_from(input);
            }
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
            assert forall|input: ParenExprInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ParenExprSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ParenExprFmt as SpecParser>::spec_parse);
            reveal(<ParenExprFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert forall|input: ParenExprInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ParenExprSpec::lemma_into_from(input);
            }
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
            assert forall|output: ParenExprSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                ParenExprSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ParenExprFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ParenExprFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.a_spec(), self.b_spec(), self.c_spec());
            assert forall|input: ParenExprInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ParenExprSpec::lemma_into_from(input);
            }
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
            assert forall|input: MixedConstInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                MixedConstSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MixedConstFmt as SpecParser>::spec_parse);
            reveal(<MixedConstFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.len_spec());
            assert forall|input: MixedConstInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                MixedConstSpec::lemma_into_from(input);
            }
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
            assert forall|output: MixedConstSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                MixedConstSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MixedConstFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MixedConstFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.len_spec());
            assert forall|input: MixedConstInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                MixedConstSpec::lemma_into_from(input);
            }
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
            let fmt = Self::spec_inner(self.hdr_spec());
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
            let fmt = Self::spec_inner(self.hdr_spec());
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
            assert forall|input: ChoiceArraysFoldedBodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ChoiceArraysFoldedBodySpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert forall|input: ChoiceArraysFoldedBodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ChoiceArraysFoldedBodySpec::lemma_into_from(input);
            }
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
            assert forall|output: ChoiceArraysFoldedBodySpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                ChoiceArraysFoldedBodySpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<'i> NonMalleable for ChoiceArraysFoldedBodyFmt<'i> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.tag_spec());
            assert forall|input: ChoiceArraysFoldedBodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                ChoiceArraysFoldedBodySpec::lemma_into_from(input);
            }
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<HeaderFmt as SpecParser>::spec_parse);
            reveal(<Header as DeepView>::deep_view);
            reveal(HeaderSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<HeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<HeaderFmt as SpecByteLen>::byte_len);
            reveal(<Header as DeepView>::deep_view);
            reveal(HeaderSpec::into_structural);
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
            reveal(<Header as DeepView>::deep_view);
            reveal(HeaderSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<PrimitiveSizesFmt as SpecParser>::spec_parse);
            reveal(<PrimitiveSizes as DeepView>::deep_view);
            reveal(PrimitiveSizesSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<PrimitiveSizesFmt as SpecSerializer>::spec_serialize);
            reveal(<PrimitiveSizesFmt as SpecByteLen>::byte_len);
            reveal(<PrimitiveSizes as DeepView>::deep_view);
            reveal(PrimitiveSizesSpec::into_structural);
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
            reveal(<PrimitiveSizes as DeepView>::deep_view);
            reveal(PrimitiveSizesSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NamedSizeFmt as SpecParser>::spec_parse);
            reveal(<NamedSize as DeepView>::deep_view);
            reveal(NamedSizeSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<NamedSizeFmt as SpecSerializer>::spec_serialize);
            reveal(<NamedSizeFmt as SpecByteLen>::byte_len);
            reveal(<NamedSize as DeepView>::deep_view);
            reveal(NamedSizeSpec::into_structural);
            let ghost old_obuf = obuf@;

            let NamedSize { bytes } = v;
            Fixed::<3>.serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NamedSize<'i>> for NamedSizeFmt {
        fn prepare(&self, v: &NamedSize<'i>) -> Result<usize, PreSerializeError> {
            reveal(<NamedSizeFmt as SpecByteLen>::byte_len);
            reveal(<NamedSize as DeepView>::deep_view);
            reveal(NamedSizeSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<AliasSizeFmt as SpecParser>::spec_parse);
            reveal(<AliasSize as DeepView>::deep_view);
            reveal(AliasSizeSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<AliasSizeFmt as SpecSerializer>::spec_serialize);
            reveal(<AliasSizeFmt as SpecByteLen>::byte_len);
            reveal(<AliasSize as DeepView>::deep_view);
            reveal(AliasSizeSpec::into_structural);
            let ghost old_obuf = obuf@;

            let AliasSize { bytes } = v;
            Fixed::<3>.serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<AliasSize<'i>> for AliasSizeFmt {
        fn prepare(&self, v: &AliasSize<'i>) -> Result<usize, PreSerializeError> {
            reveal(<AliasSizeFmt as SpecByteLen>::byte_len);
            reveal(<AliasSize as DeepView>::deep_view);
            reveal(AliasSizeSpec::into_structural);
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
            reveal(<FixedChoice as DeepView>::deep_view);
            reveal(FixedChoiceSpec::from_structural);
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
            reveal(<FixedChoice as DeepView>::deep_view);
            reveal(FixedChoiceSpec::into_structural);
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
            reveal(<FixedChoice as DeepView>::deep_view);
            reveal(FixedChoiceSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ChoiceFormatSizeFmt as SpecParser>::spec_parse);
            reveal(<ChoiceFormatSize as DeepView>::deep_view);
            reveal(ChoiceFormatSizeSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<ChoiceFormatSizeFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceFormatSizeFmt as SpecByteLen>::byte_len);
            reveal(<ChoiceFormatSize as DeepView>::deep_view);
            reveal(ChoiceFormatSizeSpec::into_structural);
            let ghost old_obuf = obuf@;

            let ChoiceFormatSize { bytes } = v;
            Fixed::<2>.serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceFormatSize<'i>> for ChoiceFormatSizeFmt {
        fn prepare(&self, v: &ChoiceFormatSize<'i>) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceFormatSizeFmt as SpecByteLen>::byte_len);
            reveal(<ChoiceFormatSize as DeepView>::deep_view);
            reveal(ChoiceFormatSizeSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ChoiceArraysFoldedFmt as SpecParser>::spec_parse);
            reveal(<ChoiceArraysFolded as DeepView>::deep_view);
            reveal(ChoiceArraysFoldedSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<ChoiceArraysFoldedFmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceArraysFoldedFmt as SpecByteLen>::byte_len);
            reveal(<ChoiceArraysFolded as DeepView>::deep_view);
            reveal(ChoiceArraysFoldedSpec::into_structural);
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
            reveal(<ChoiceArraysFolded as DeepView>::deep_view);
            reveal(ChoiceArraysFoldedSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<SizeArithFmt as SpecParser>::spec_parse);
            reveal(<SizeArith as DeepView>::deep_view);
            reveal(SizeArithSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<SizeArithFmt as SpecSerializer>::spec_serialize);
            reveal(<SizeArithFmt as SpecByteLen>::byte_len);
            reveal(<SizeArith as DeepView>::deep_view);
            reveal(SizeArithSpec::into_structural);
            let ghost old_obuf = obuf@;

            let SizeArith { bytes } = v;
            Fixed::<4>.serialize_into(*bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<SizeArith<'i>> for SizeArithFmt {
        fn prepare(&self, v: &SizeArith<'i>) -> Result<usize, PreSerializeError> {
            reveal(<SizeArithFmt as SpecByteLen>::byte_len);
            reveal(<SizeArith as DeepView>::deep_view);
            reveal(SizeArithSpec::into_structural);
            let SizeArith { bytes } = v;
            let l1 = (Fixed::<4>).prepare(bytes)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for SimpleSubFmt {
        type PT = SimpleSub<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<SimpleSubFmt as SpecParser>::spec_parse);
            reveal(<SimpleSub as DeepView>::deep_view);
            reveal(SimpleSubSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<SimpleSubFmt as SpecSerializer>::spec_serialize);
            reveal(<SimpleSubFmt as SpecByteLen>::byte_len);
            reveal(<SimpleSub as DeepView>::deep_view);
            reveal(SimpleSubSpec::into_structural);
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
            reveal(<SimpleSub as DeepView>::deep_view);
            reveal(SimpleSubSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MultiArithFmt as SpecParser>::spec_parse);
            reveal(<MultiArith as DeepView>::deep_view);
            reveal(MultiArithSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<MultiArithFmt as SpecSerializer>::spec_serialize);
            reveal(<MultiArithFmt as SpecByteLen>::byte_len);
            reveal(<MultiArith as DeepView>::deep_view);
            reveal(MultiArithSpec::into_structural);
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
            reveal(<MultiArith as DeepView>::deep_view);
            reveal(MultiArithSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ParenExprFmt as SpecParser>::spec_parse);
            reveal(<ParenExpr as DeepView>::deep_view);
            reveal(ParenExprSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<ParenExprFmt as SpecSerializer>::spec_serialize);
            reveal(<ParenExprFmt as SpecByteLen>::byte_len);
            reveal(<ParenExpr as DeepView>::deep_view);
            reveal(ParenExprSpec::into_structural);
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
            reveal(<ParenExpr as DeepView>::deep_view);
            reveal(ParenExprSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MixedConstFmt as SpecParser>::spec_parse);
            reveal(<MixedConst as DeepView>::deep_view);
            reveal(MixedConstSpec::from_structural);
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<MixedConstFmt as SpecSerializer>::spec_serialize);
            reveal(<MixedConstFmt as SpecByteLen>::byte_len);
            reveal(<MixedConst as DeepView>::deep_view);
            reveal(MixedConstSpec::into_structural);
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
            reveal(<MixedConst as DeepView>::deep_view);
            reveal(MixedConstSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<PayloadWithHeaderFmt as SpecParser>::spec_parse);
            reveal(<PayloadWithHeader as DeepView>::deep_view);
            reveal(PayloadWithHeaderSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            proof {
                self.hdr.lemma_deep_view_fields();
                self.hdr.deep_view().lemma_into_structural_fields();
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
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<PayloadWithHeaderFmt as SpecSerializer>::spec_serialize);
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            reveal(<PayloadWithHeader as DeepView>::deep_view);
            reveal(PayloadWithHeaderSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let PayloadWithHeader { data } = v;
            proof {
                self.hdr.lemma_deep_view_fields();
                self.hdr.deep_view().lemma_into_structural_fields();
            }

            Varied((self.hdr.len - 3)).serialize_into(*data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<PayloadWithHeader<'i>> for PayloadWithHeaderFmt {
        fn prepare(&self, v: &PayloadWithHeader<'i>) -> Result<usize, PreSerializeError> {
            reveal(<PayloadWithHeaderFmt as SpecByteLen>::byte_len);
            reveal(<PayloadWithHeader as DeepView>::deep_view);
            reveal(PayloadWithHeaderSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let PayloadWithHeader { data } = v;
            proof {
                self.hdr.lemma_deep_view_fields();
                self.hdr.deep_view().lemma_into_structural_fields();
            }

            let l1 = (Varied((self.hdr.len - 3))).prepare(data)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for ChoiceArraysFoldedBodyFmt<'i> {
        type PT = ChoiceArraysFoldedBody;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ChoiceArraysFoldedBodyFmt as SpecParser>::spec_parse);
            reveal(<ChoiceArraysFoldedBody as DeepView>::deep_view);
            reveal(ChoiceArraysFoldedBodySpec::from_structural);
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
            reveal(<ChoiceArraysFoldedBody as DeepView>::deep_view);
            reveal(ChoiceArraysFoldedBodySpec::into_structural);
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
            reveal(<ChoiceArraysFoldedBody as DeepView>::deep_view);
            reveal(ChoiceArraysFoldedBodySpec::into_structural);
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
