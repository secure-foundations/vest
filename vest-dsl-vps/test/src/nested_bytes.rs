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
# [doc = "data type for `anything`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Anything {
    pub x: u8,
}

# [verifier::ext_equal]
pub struct AnythingSpec<T0 = u8> {
    pub x: T0,
}

pub type AnythingInner = u8;

impl DeepView for Anything {
    type V = AnythingSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        AnythingSpec { x: self.x.deep_view() }
    }
}

impl Anything {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().x == self.x.deep_view(),
    {
        reveal(<Anything as DeepView>::deep_view);
    }
}

impl<T0> AnythingSpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let x = input;
        Self { x }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { x } = self;
        x
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(AnythingSpec::from_structural);
        reveal(AnythingSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(AnythingSpec::from_structural);
        reveal(AnythingSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { x } => x,
            },
    {
        reveal(AnythingSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct AnythingForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct AnythingReverse;

impl SpecMap for AnythingForward {
    type Input = AnythingInner;

    type Output = AnythingSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        AnythingSpec::from_structural(input)
    }
}

impl SpecMap for AnythingReverse {
    type Input = AnythingSpec;

    type Output = AnythingInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nested_dynamic_bytes`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct NestedDynamicBytes<'i> {
    pub num: u16,
    pub num_inner: u16,
    pub xs: Vec<&'i [u8]>,
}

# [verifier::ext_equal]
pub struct NestedDynamicBytesSpec<T0 = u16, T1 = u16, T2 = Seq<Seq<u8>>> {
    pub num: T0,
    pub num_inner: T1,
    pub xs: T2,
}

pub type NestedDynamicBytesInner = (u16, (u16, Seq<Seq<u8>>));

impl<'i> DeepView for NestedDynamicBytes<'i> {
    type V = NestedDynamicBytesSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        NestedDynamicBytesSpec {
            num: self.num.deep_view(),
            num_inner: self.num_inner.deep_view(),
            xs: self.xs.deep_view(),
        }
    }
}

impl<'i> NestedDynamicBytes<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().num == self.num.deep_view(),
            self.deep_view().num_inner == self.num_inner.deep_view(),
            self.deep_view().xs == self.xs.deep_view(),
    {
        reveal(<NestedDynamicBytes as DeepView>::deep_view);
    }
}

impl<T0, T1, T2> NestedDynamicBytesSpec<T0, T1, T2> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, (T1, T2))) -> Self {
        let (num, (num_inner, xs)) = input;
        Self { num, num_inner, xs }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, T2)) {
        let Self { num, num_inner, xs } = self;
        (num, (num_inner, xs))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(NestedDynamicBytesSpec::from_structural);
        reveal(NestedDynamicBytesSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, (T1, T2)))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(NestedDynamicBytesSpec::from_structural);
        reveal(NestedDynamicBytesSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { num, num_inner, xs } => (num, (num_inner, xs)),
            },
    {
        reveal(NestedDynamicBytesSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedDynamicBytesForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedDynamicBytesReverse;

impl SpecMap for NestedDynamicBytesForward {
    type Input = NestedDynamicBytesInner;

    type Output = NestedDynamicBytesSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        NestedDynamicBytesSpec::from_structural(input)
    }
}

impl SpecMap for NestedDynamicBytesReverse {
    type Input = NestedDynamicBytesSpec;

    type Output = NestedDynamicBytesInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nested_fixed_bytes`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct NestedFixedBytes<'i> {
    pub num: u16,
    pub xs: Vec<&'i [u8]>,
}

# [verifier::ext_equal]
pub struct NestedFixedBytesSpec<T0 = u16, T1 = Seq<Seq<u8>>> {
    pub num: T0,
    pub xs: T1,
}

pub type NestedFixedBytesInner = (u16, Seq<Seq<u8>>);

impl<'i> DeepView for NestedFixedBytes<'i> {
    type V = NestedFixedBytesSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        NestedFixedBytesSpec { num: self.num.deep_view(), xs: self.xs.deep_view() }
    }
}

impl<'i> NestedFixedBytes<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().num == self.num.deep_view(),
            self.deep_view().xs == self.xs.deep_view(),
    {
        reveal(<NestedFixedBytes as DeepView>::deep_view);
    }
}

impl<T0, T1> NestedFixedBytesSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (num, xs) = input;
        Self { num, xs }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { num, xs } = self;
        (num, xs)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(NestedFixedBytesSpec::from_structural);
        reveal(NestedFixedBytesSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(NestedFixedBytesSpec::from_structural);
        reveal(NestedFixedBytesSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { num, xs } => (num, xs),
            },
    {
        reveal(NestedFixedBytesSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedFixedBytesForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedFixedBytesReverse;

impl SpecMap for NestedFixedBytesForward {
    type Input = NestedFixedBytesInner;

    type Output = NestedFixedBytesSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        NestedFixedBytesSpec::from_structural(input)
    }
}

impl SpecMap for NestedFixedBytesReverse {
    type Input = NestedFixedBytesSpec;

    type Output = NestedFixedBytesInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `fixed_array_of_bytes`."]
pub type FixedArrayOfBytes<'i> = [&'i [u8]; 3];

pub type FixedArrayOfBytesSpec = Seq<Seq<u8>>;

# [doc = "data type for `vec_of_bytes`."]
pub type VecOfBytes<'i> = Vec<&'i [u8]>;

pub type VecOfBytesSpec = Seq<Seq<u8>>;

# [doc = "data type for `optional_bytes`."]
pub type OptionalBytes<'i> = Option<&'i [u8]>;

pub type OptionalBytesSpec = Option<Seq<u8>>;

# [doc = "data type for `tail_vec`."]
# [derive (Debug, PartialEq, Eq, Clone)]
pub struct TailVec {
    pub xs: Vec<Anything>,
}

# [verifier::ext_equal]
pub struct TailVecSpec<T0 = Seq<AnythingSpec>> {
    pub xs: T0,
}

pub type TailVecInner = Seq<AnythingSpec>;

impl DeepView for TailVec {
    type V = TailVecSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        TailVecSpec { xs: self.xs.deep_view() }
    }
}

impl TailVec {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().xs == self.xs.deep_view(),
    {
        reveal(<TailVec as DeepView>::deep_view);
    }
}

impl<T0> TailVecSpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let xs = input;
        Self { xs }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { xs } = self;
        xs
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(TailVecSpec::from_structural);
        reveal(TailVecSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(TailVecSpec::from_structural);
        reveal(TailVecSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { xs } => xs,
            },
    {
        reveal(TailVecSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TailVecForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TailVecReverse;

impl SpecMap for TailVecForward {
    type Input = TailVecInner;

    type Output = TailVecSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        TailVecSpec::from_structural(input)
    }
}

impl SpecMap for TailVecReverse {
    type Input = TailVecSpec;

    type Output = TailVecInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `anything`."]
# [derive (Clone, Copy)]
pub struct AnythingFmt;

pub type AnythingFmtSpec = Named<Mapped<U8, BiMap<AnythingForward, AnythingReverse>>>;

impl AnythingFmt {
    # [doc = "specification constructor for `anything`."]
    pub open spec fn spec_inner() -> AnythingFmtSpec {
        Named("anything", Mapped { inner: U8, mapper: BiMap(AnythingForward, AnythingReverse) })
    }
}

# [doc = "named format combinator for `nested_dynamic_bytes`."]
# [derive (Clone, Copy)]
pub struct NestedDynamicBytesFmt;

pub type NestedDynamicBytesFmtSpec = Named<
    Mapped<
        Bind<U16Le, spec_fn(u16) -> Bind<U16Le, spec_fn(u16) -> RepeatN<Varied<u16>, u16>>>,
        BiMap<NestedDynamicBytesForward, NestedDynamicBytesReverse>,
    >,
>;

impl NestedDynamicBytesFmt {
    # [doc = "specification constructor for `nested_dynamic_bytes`."]
    pub open spec fn spec_inner() -> NestedDynamicBytesFmtSpec {
        Named(
            "nested_dynamic_bytes",
            Mapped {
                inner: Bind(
                    U16Le,
                    |num: u16| Bind(U16Le, |num_inner: u16| RepeatN(num, Varied(num_inner))),
                ),
                mapper: BiMap(NestedDynamicBytesForward, NestedDynamicBytesReverse),
            },
        )
    }
}

# [doc = "named format combinator for `nested_fixed_bytes`."]
# [derive (Clone, Copy)]
pub struct NestedFixedBytesFmt;

pub type NestedFixedBytesFmtSpec = Named<
    Mapped<
        Bind<U16Le, spec_fn(u16) -> RepeatN<Fixed<10>, u16>>,
        BiMap<NestedFixedBytesForward, NestedFixedBytesReverse>,
    >,
>;

impl NestedFixedBytesFmt {
    # [doc = "specification constructor for `nested_fixed_bytes`."]
    pub open spec fn spec_inner() -> NestedFixedBytesFmtSpec {
        Named(
            "nested_fixed_bytes",
            Mapped {
                inner: Bind(U16Le, |num: u16| RepeatN(num, Fixed::<10>)),
                mapper: BiMap(NestedFixedBytesForward, NestedFixedBytesReverse),
            },
        )
    }
}

# [doc = "named format combinator for `fixed_array_of_bytes`."]
# [derive (Clone, Copy)]
pub struct FixedArrayOfBytesFmt;

pub type FixedArrayOfBytesFmtSpec = Named<Array<3, Fixed<2>>>;

impl FixedArrayOfBytesFmt {
    # [doc = "specification constructor for `fixed_array_of_bytes`."]
    pub open spec fn spec_inner() -> FixedArrayOfBytesFmtSpec {
        Named("fixed_array_of_bytes", Array::<3, _>(Fixed::<2>))
    }
}

# [doc = "named format combinator for `vec_of_bytes`."]
# [derive (Clone, Copy)]
pub struct VecOfBytesFmt;

pub type VecOfBytesFmtSpec = Named<RepeatTillEnd<Fixed<2>>>;

impl VecOfBytesFmt {
    # [doc = "specification constructor for `vec_of_bytes`."]
    pub open spec fn spec_inner() -> VecOfBytesFmtSpec {
        Named("vec_of_bytes", RepeatTillEnd(Fixed::<2>))
    }
}

# [doc = "named format combinator for `optional_bytes`."]
# [derive (Clone, Copy)]
pub struct OptionalBytesFmt;

pub type OptionalBytesFmtSpec = Named<OptionalEnd<Fixed<2>>>;

impl OptionalBytesFmt {
    # [doc = "specification constructor for `optional_bytes`."]
    pub open spec fn spec_inner() -> OptionalBytesFmtSpec {
        Named("optional_bytes", OptionalEnd(Fixed::<2>))
    }
}

# [doc = "named format combinator for `tail_vec`."]
# [derive (Clone, Copy)]
pub struct TailVecFmt;

pub type TailVecFmtSpec = Named<
    Mapped<AndThen<Tail, RepeatTillEnd<AnythingFmt>>, BiMap<TailVecForward, TailVecReverse>>,
>;

impl TailVecFmt {
    # [doc = "specification constructor for `tail_vec`."]
    pub open spec fn spec_inner() -> TailVecFmtSpec {
        Named(
            "tail_vec",
            Mapped {
                inner: AndThen(Tail, RepeatTillEnd(AnythingFmt)),
                mapper: BiMap(TailVecForward, TailVecReverse),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for AnythingFmt {
        type PVal = AnythingSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for AnythingFmt {
        type Val = AnythingSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for AnythingFmt {
        type SValue = AnythingSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AnythingFmt {
        type SVal = AnythingSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for AnythingFmt {
        type T = AnythingSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for NestedDynamicBytesFmt {
        type PVal = NestedDynamicBytesSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for NestedDynamicBytesFmt {
        type Val = NestedDynamicBytesSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for NestedDynamicBytesFmt {
        type SValue = NestedDynamicBytesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for NestedDynamicBytesFmt {
        type SVal = NestedDynamicBytesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for NestedDynamicBytesFmt {
        type T = NestedDynamicBytesSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for NestedFixedBytesFmt {
        type PVal = NestedFixedBytesSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for NestedFixedBytesFmt {
        type Val = NestedFixedBytesSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for NestedFixedBytesFmt {
        type SValue = NestedFixedBytesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for NestedFixedBytesFmt {
        type SVal = NestedFixedBytesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for NestedFixedBytesFmt {
        type T = NestedFixedBytesSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for FixedArrayOfBytesFmt {
        type PVal = FixedArrayOfBytesSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for FixedArrayOfBytesFmt {
        type Val = FixedArrayOfBytesSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for FixedArrayOfBytesFmt {
        type SValue = FixedArrayOfBytesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for FixedArrayOfBytesFmt {
        type SVal = FixedArrayOfBytesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for FixedArrayOfBytesFmt {
        type T = FixedArrayOfBytesSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for VecOfBytesFmt {
        type PVal = VecOfBytesSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for VecOfBytesFmt {
        type Val = VecOfBytesSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for VecOfBytesFmt {
        type SValue = VecOfBytesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for VecOfBytesFmt {
        type SVal = VecOfBytesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for VecOfBytesFmt {
        type T = VecOfBytesSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for OptionalBytesFmt {
        type PVal = OptionalBytesSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for OptionalBytesFmt {
        type Val = OptionalBytesSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for OptionalBytesFmt {
        type SValue = OptionalBytesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for OptionalBytesFmt {
        type SVal = OptionalBytesSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for OptionalBytesFmt {
        type T = OptionalBytesSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for TailVecFmt {
        type PVal = TailVecSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for TailVecFmt {
        type Val = TailVecSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for TailVecFmt {
        type SValue = TailVecSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for TailVecFmt {
        type SVal = TailVecSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for TailVecFmt {
        type T = TailVecSpec;

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
        AnythingSpec::lemma_from_into,
        AnythingSpec::lemma_into_from,
        NestedDynamicBytesSpec::lemma_from_into,
        NestedDynamicBytesSpec::lemma_into_from,
        NestedFixedBytesSpec::lemma_from_into,
        NestedFixedBytesSpec::lemma_into_from,
        TailVecSpec::lemma_from_into,
        TailVecSpec::lemma_into_from,
    };

    impl SafeParser for AnythingFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AnythingFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AnythingFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AnythingFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AnythingFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AnythingFmt as SpecParser>::spec_parse);
            reveal(<AnythingFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: AnythingInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                AnythingSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AnythingFmt as SpecParser>::spec_parse);
            reveal(<AnythingFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: AnythingInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                AnythingSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for AnythingFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AnythingFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AnythingFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnythingFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for AnythingFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AnythingFmt as SpecSerializer>::spec_serialize);
            reveal(<AnythingFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for AnythingFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<AnythingFmt as SpecParser>::spec_parse);
            reveal(<AnythingFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnythingFmt as Consistency>::consistent);
            reveal(<AnythingFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: AnythingSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                AnythingSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AnythingFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AnythingFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: AnythingInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                AnythingSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for AnythingFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<AnythingFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnythingFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for AnythingFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AnythingFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AnythingFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for NestedDynamicBytesFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<NestedDynamicBytesFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for NestedDynamicBytesFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<NestedDynamicBytesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for NestedDynamicBytesFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<NestedDynamicBytesFmt as SpecParser>::spec_parse);
            reveal(<NestedDynamicBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: NestedDynamicBytesInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedDynamicBytesSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedDynamicBytesFmt as SpecParser>::spec_parse);
            reveal(<NestedDynamicBytesFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: NestedDynamicBytesInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedDynamicBytesSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for NestedDynamicBytesFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedDynamicBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedDynamicBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedDynamicBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for NestedDynamicBytesFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<NestedDynamicBytesFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedDynamicBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for NestedDynamicBytesFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<NestedDynamicBytesFmt as SpecParser>::spec_parse);
            reveal(<NestedDynamicBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedDynamicBytesFmt as Consistency>::consistent);
            reveal(<NestedDynamicBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: NestedDynamicBytesSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                NestedDynamicBytesSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedDynamicBytesFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedDynamicBytesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: NestedDynamicBytesInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedDynamicBytesSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for NestedDynamicBytesFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<NestedDynamicBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedDynamicBytesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for NestedDynamicBytesFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<NestedDynamicBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedDynamicBytesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for NestedFixedBytesFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<NestedFixedBytesFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for NestedFixedBytesFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<NestedFixedBytesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for NestedFixedBytesFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<NestedFixedBytesFmt as SpecParser>::spec_parse);
            reveal(<NestedFixedBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: NestedFixedBytesInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedFixedBytesSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedFixedBytesFmt as SpecParser>::spec_parse);
            reveal(<NestedFixedBytesFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: NestedFixedBytesInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedFixedBytesSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for NestedFixedBytesFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedFixedBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedFixedBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedFixedBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for NestedFixedBytesFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<NestedFixedBytesFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedFixedBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for NestedFixedBytesFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<NestedFixedBytesFmt as SpecParser>::spec_parse);
            reveal(<NestedFixedBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedFixedBytesFmt as Consistency>::consistent);
            reveal(<NestedFixedBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: NestedFixedBytesSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                NestedFixedBytesSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedFixedBytesFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedFixedBytesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: NestedFixedBytesInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedFixedBytesSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for NestedFixedBytesFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<NestedFixedBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedFixedBytesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for NestedFixedBytesFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<NestedFixedBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedFixedBytesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for FixedArrayOfBytesFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<FixedArrayOfBytesFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for FixedArrayOfBytesFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<FixedArrayOfBytesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for FixedArrayOfBytesFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<FixedArrayOfBytesFmt as SpecParser>::spec_parse);
            reveal(<FixedArrayOfBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<FixedArrayOfBytesFmt as SpecParser>::spec_parse);
            reveal(<FixedArrayOfBytesFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for FixedArrayOfBytesFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<FixedArrayOfBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<FixedArrayOfBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FixedArrayOfBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for FixedArrayOfBytesFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<FixedArrayOfBytesFmt as SpecSerializer>::spec_serialize);
            reveal(<FixedArrayOfBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for FixedArrayOfBytesFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<FixedArrayOfBytesFmt as SpecParser>::spec_parse);
            reveal(<FixedArrayOfBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FixedArrayOfBytesFmt as Consistency>::consistent);
            reveal(<FixedArrayOfBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for FixedArrayOfBytesFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<FixedArrayOfBytesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for FixedArrayOfBytesFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<FixedArrayOfBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FixedArrayOfBytesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for FixedArrayOfBytesFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<FixedArrayOfBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<FixedArrayOfBytesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for VecOfBytesFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<VecOfBytesFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for VecOfBytesFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<VecOfBytesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for VecOfBytesFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<VecOfBytesFmt as SpecParser>::spec_parse);
            reveal(<VecOfBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<VecOfBytesFmt as SpecParser>::spec_parse);
            reveal(<VecOfBytesFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for VecOfBytesFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<VecOfBytesFmt as SpecSerializer>::spec_serialize);
            reveal(<VecOfBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for VecOfBytesFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<VecOfBytesFmt as SpecParser>::spec_parse);
            reveal(<VecOfBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<VecOfBytesFmt as Consistency>::consistent);
            reveal(<VecOfBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for VecOfBytesFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<VecOfBytesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for VecOfBytesFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<VecOfBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<VecOfBytesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for OptionalBytesFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<OptionalBytesFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for OptionalBytesFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<OptionalBytesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for OptionalBytesFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<OptionalBytesFmt as SpecParser>::spec_parse);
            reveal(<OptionalBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<OptionalBytesFmt as SpecParser>::spec_parse);
            reveal(<OptionalBytesFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for OptionalBytesFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<OptionalBytesFmt as SpecSerializer>::spec_serialize);
            reveal(<OptionalBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for OptionalBytesFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<OptionalBytesFmt as SpecParser>::spec_parse);
            reveal(<OptionalBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OptionalBytesFmt as Consistency>::consistent);
            reveal(<OptionalBytesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for OptionalBytesFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<OptionalBytesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for OptionalBytesFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<OptionalBytesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<OptionalBytesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for TailVecFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<TailVecFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for TailVecFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<TailVecFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for TailVecFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<TailVecFmt as SpecParser>::spec_parse);
            reveal(<TailVecFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: TailVecInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TailVecSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<TailVecFmt as SpecParser>::spec_parse);
            reveal(<TailVecFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: TailVecInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TailVecSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for TailVecFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<TailVecFmt as SpecSerializer>::spec_serialize);
            reveal(<TailVecFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for TailVecFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<TailVecFmt as SpecParser>::spec_parse);
            reveal(<TailVecFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TailVecFmt as Consistency>::consistent);
            reveal(<TailVecFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: TailVecSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                TailVecSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for TailVecFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<TailVecFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: TailVecInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                TailVecSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for TailVecFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<TailVecFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<TailVecFmt as SpecSerializer>::spec_serialize);
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

    impl<'i> Parser<&'i [u8]> for AnythingFmt {
        type PT = Anything;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<AnythingFmt as SpecParser>::spec_parse);
            reveal(<Anything as DeepView>::deep_view);
            reveal(AnythingSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, x) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Anything { x };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Anything> for AnythingFmt {
        fn serialize_into(&self, v: &Anything, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<AnythingFmt as SpecSerializer>::spec_serialize);
            reveal(<AnythingFmt as SpecByteLen>::byte_len);
            reveal(<Anything as DeepView>::deep_view);
            reveal(AnythingSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Anything { x } = v;
            U8.serialize_into(x, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Anything> for AnythingFmt {
        fn prepare(&self, v: &Anything) -> Result<usize, PreSerializeError> {
            reveal(<AnythingFmt as SpecByteLen>::byte_len);
            reveal(<Anything as DeepView>::deep_view);
            reveal(AnythingSpec::into_structural);
            let Anything { x } = v;
            let l1 = (U8).prepare(x)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for NestedDynamicBytesFmt {
        type PT = NestedDynamicBytes<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NestedDynamicBytesFmt as SpecParser>::spec_parse);
            reveal(<NestedDynamicBytes as DeepView>::deep_view);
            reveal(NestedDynamicBytesSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, num) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, num_inner) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, xs) = (RepeatN(num, Varied(num_inner))).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = NestedDynamicBytes { num, num_inner, xs };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        NestedDynamicBytes<'i>,
    > for NestedDynamicBytesFmt {
        fn serialize_into(&self, v: &NestedDynamicBytes<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<NestedDynamicBytesFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedDynamicBytesFmt as SpecByteLen>::byte_len);
            reveal(<NestedDynamicBytes as DeepView>::deep_view);
            reveal(NestedDynamicBytesSpec::into_structural);
            let ghost old_obuf = obuf@;

            let NestedDynamicBytes { num, num_inner, xs } = v;
            U16Le.serialize_into(num, obuf);
            U16Le.serialize_into(num_inner, obuf);
            RepeatN(*num, Varied(*num_inner)).serialize_into(xs, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedDynamicBytes<'i>> for NestedDynamicBytesFmt {
        fn prepare(&self, v: &NestedDynamicBytes<'i>) -> Result<usize, PreSerializeError> {
            reveal(<NestedDynamicBytesFmt as SpecByteLen>::byte_len);
            reveal(<NestedDynamicBytes as DeepView>::deep_view);
            reveal(NestedDynamicBytesSpec::into_structural);
            let NestedDynamicBytes { num, num_inner, xs } = v;
            let l1 = (U16Le).prepare(num)?;
            let l2 = (U16Le).prepare(num_inner)?;
            let l3 = (RepeatN(*num, Varied(*num_inner))).prepare(xs)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for NestedFixedBytesFmt {
        type PT = NestedFixedBytes<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NestedFixedBytesFmt as SpecParser>::spec_parse);
            reveal(<NestedFixedBytes as DeepView>::deep_view);
            reveal(NestedFixedBytesSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, num) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, xs) = (RepeatN(num, Fixed::<10>)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = NestedFixedBytes { num, xs };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, NestedFixedBytes<'i>> for NestedFixedBytesFmt {
        fn serialize_into(&self, v: &NestedFixedBytes<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<NestedFixedBytesFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedFixedBytesFmt as SpecByteLen>::byte_len);
            reveal(<NestedFixedBytes as DeepView>::deep_view);
            reveal(NestedFixedBytesSpec::into_structural);
            let ghost old_obuf = obuf@;

            let NestedFixedBytes { num, xs } = v;
            U16Le.serialize_into(num, obuf);
            RepeatN(*num, Fixed::<10>).serialize_into(xs, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedFixedBytes<'i>> for NestedFixedBytesFmt {
        fn prepare(&self, v: &NestedFixedBytes<'i>) -> Result<usize, PreSerializeError> {
            reveal(<NestedFixedBytesFmt as SpecByteLen>::byte_len);
            reveal(<NestedFixedBytes as DeepView>::deep_view);
            reveal(NestedFixedBytesSpec::into_structural);
            let NestedFixedBytes { num, xs } = v;
            let l1 = (U16Le).prepare(num)?;
            let l2 = (RepeatN(*num, Fixed::<10>)).prepare(xs)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for FixedArrayOfBytesFmt {
        type PT = FixedArrayOfBytes<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<FixedArrayOfBytesFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Array::<3, _>(Fixed::<2>).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, FixedArrayOfBytes<'i>> for FixedArrayOfBytesFmt {
        fn serialize_into(&self, v: &FixedArrayOfBytes<'i>, obuf: &mut Output) {
            reveal(<FixedArrayOfBytesFmt as SpecSerializer>::spec_serialize);
            reveal(<FixedArrayOfBytesFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            Array::<3, _>(Fixed::<2>).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<FixedArrayOfBytes<'i>> for FixedArrayOfBytesFmt {
        fn prepare(&self, v: &FixedArrayOfBytes<'i>) -> Result<usize, PreSerializeError> {
            reveal(<FixedArrayOfBytesFmt as SpecByteLen>::byte_len);
            (Array::<3, _>(Fixed::<2>)).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for VecOfBytesFmt {
        type PT = VecOfBytes<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<VecOfBytesFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Star(Fixed::<2>).parse(ibuf)?;
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let rest = ibuf.skip(n);
            let _ = Eof.parse(&rest)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, VecOfBytes<'i>> for VecOfBytesFmt {
        fn serialize_into(&self, v: &VecOfBytes<'i>, obuf: &mut Output) {
            reveal(<VecOfBytesFmt as SpecSerializer>::spec_serialize);
            reveal(<VecOfBytesFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            Star(Fixed::<2>).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<VecOfBytes<'i>> for VecOfBytesFmt {
        fn prepare(&self, v: &VecOfBytes<'i>) -> Result<usize, PreSerializeError> {
            reveal(<VecOfBytesFmt as SpecByteLen>::byte_len);
            (Star(Fixed::<2>)).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for OptionalBytesFmt {
        type PT = OptionalBytes<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<OptionalBytesFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Opt(Fixed::<2>).parse(ibuf)?;
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;

            let rest = ibuf.skip(n);
            let _ = Eof.parse(&rest)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, OptionalBytes<'i>> for OptionalBytesFmt {
        fn serialize_into(&self, v: &OptionalBytes<'i>, obuf: &mut Output) {
            reveal(<OptionalBytesFmt as SpecSerializer>::spec_serialize);
            reveal(<OptionalBytesFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            Opt(Fixed::<2>).serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<OptionalBytes<'i>> for OptionalBytesFmt {
        fn prepare(&self, v: &OptionalBytes<'i>) -> Result<usize, PreSerializeError> {
            reveal(<OptionalBytesFmt as SpecByteLen>::byte_len);
            (Opt(Fixed::<2>)).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for TailVecFmt {
        type PT = TailVec;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TailVecFmt as SpecParser>::spec_parse);
            reveal(<TailVec as DeepView>::deep_view);
            reveal(TailVecSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, xs) = (AndThen(Tail, Star(AnythingFmt))).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = TailVec { xs };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TailVec> for TailVecFmt {
        fn serialize_into(&self, v: &TailVec, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<TailVecFmt as SpecSerializer>::spec_serialize);
            reveal(<TailVecFmt as SpecByteLen>::byte_len);
            reveal(<TailVec as DeepView>::deep_view);
            reveal(TailVecSpec::into_structural);
            let ghost old_obuf = obuf@;

            let TailVec { xs } = v;
            AndThen(Tail, Star(AnythingFmt)).serialize_into(xs, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TailVec> for TailVecFmt {
        fn prepare(&self, v: &TailVec) -> Result<usize, PreSerializeError> {
            broadcast use vps_lib::combinators::bytes::spec::tail_and_then_lemmas;

            reveal(<TailVecFmt as SpecByteLen>::byte_len);
            reveal(<TailVec as DeepView>::deep_view);
            reveal(TailVecSpec::into_structural);
            let TailVec { xs } = v;
            let l1 = (AndThen(Tail, Star(AnythingFmt))).prepare(xs)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

}

} // verus!
