#![allow(warnings)]
use vest_lib::combinators::mapped::spec::*;
use vest_lib::combinators::*;
use vest_lib::combinators::recursive::*;
use Sum::Inl as L;
use Sum::Inr as R;
use vest_lib::Never;
use vest_lib::core::exec::input::{InputBuf, InputSlice};
use vest_lib::core::exec::output::OutputBuf;
use vest_lib::core::exec::parser::*;
use vest_lib::core::exec::serializer::*;
use vest_lib::core::exec::ParseError;
use vest_lib::core::exec::bytes_eq;
use vest_lib::core::{proof::*, spec::*};
use vest_lib::primitives::btcvarint::VarInt;
use vest_lib::primitives::leb128::ULeb128;
use vstd::prelude::*;
verus! {
// ============================================================
// Data Types
// ============================================================
/// data type for `internal_names`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct InternalNames<'i> {
    pub n: u8,
    pub l: u8,
    pub raw: &'i [u8],
    pub packed: &'i [u8],
    pub inner: u16,
    pub total: u16,
    pub total_len: u16,
    pub final_v: u8,
    pub x: u8,
    pub tag: u8,
}

#[verifier::ext_equal]
pub struct InternalNamesSpec<
    T0 = u8,
    T1 = u8,
    T2 = Seq<u8>,
    T3 = Seq<u8>,
    T4 = u16,
    T5 = u16,
    T6 = u16,
    T7 = u8,
    T8 = u8,
    T9 = u8,
> {
    pub n: T0,
    pub l: T1,
    pub raw: T2,
    pub packed: T3,
    pub inner: T4,
    pub total: T5,
    pub total_len: T6,
    pub final_v: T7,
    pub x: T8,
    pub tag: T9,
}

pub type InternalNamesInner = (u8, (u8, (Seq<u8>, (Seq<u8>, (u16, (u16, (u16, (u8, (u8, u8)))))))));

impl<'i> DeepView for InternalNames<'i> {
    type V = InternalNamesSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        InternalNamesSpec {
            n: self.n.deep_view(),
            l: self.l.deep_view(),
            raw: self.raw.deep_view(),
            packed: self.packed.deep_view(),
            inner: self.inner.deep_view(),
            total: self.total.deep_view(),
            total_len: self.total_len.deep_view(),
            final_v: self.final_v.deep_view(),
            x: self.x.deep_view(),
            tag: self.tag.deep_view(),
        }
    }
}

impl<'i> InternalNames<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().n == self.n.deep_view(),
            self.deep_view().l == self.l.deep_view(),
            self.deep_view().raw == self.raw.deep_view(),
            self.deep_view().packed == self.packed.deep_view(),
            self.deep_view().inner == self.inner.deep_view(),
            self.deep_view().total == self.total.deep_view(),
            self.deep_view().total_len == self.total_len.deep_view(),
            self.deep_view().final_v == self.final_v.deep_view(),
            self.deep_view().x == self.x.deep_view(),
            self.deep_view().tag == self.tag.deep_view(),
    {
        reveal(<InternalNames as DeepView>::deep_view);
    }
}

/// data type for `bit_names`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[verifier::ext_equal]
pub struct BitNames {
    pub raw: u8,
    pub packed: u8,
    pub x: u8,
}

pub type BitNamesSpec = BitNames;
pub type BitNamesInner = u8;

impl DeepView for BitNames {
    type V = Self;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl BitNames {
    pub proof fn lemma_deep_view(&self)
        ensures
            self.deep_view() == *self,
    {
        reveal(<BitNames as DeepView>::deep_view);
    }
}

/// data type for `with_bits`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct WithBits {
    pub flags: BitNames,
    pub total_len: u8,
}

#[verifier::ext_equal]
pub struct WithBitsSpec<T0 = BitNamesSpec, T1 = u8> {
    pub flags: T0,
    pub total_len: T1,
}

pub type WithBitsInner = (BitNamesSpec, u8);

impl DeepView for WithBits {
    type V = WithBitsSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        WithBitsSpec { flags: self.flags.deep_view(), total_len: self.total_len.deep_view() }
    }
}

impl WithBits {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().flags == self.flags.deep_view(),
            self.deep_view().total_len == self.total_len.deep_view(),
    {
        reveal(<WithBits as DeepView>::deep_view);
    }
}

/// data type for `counted`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Counted<'i> {
    pub items: &'i [u8],
    pub final_v: u8,
}

#[verifier::ext_equal]
pub struct CountedSpec<T0 = Seq<u8>, T1 = u8> {
    pub items: T0,
    pub final_v: T1,
}

pub type CountedInner = (Seq<u8>, u8);

impl<'i> DeepView for Counted<'i> {
    type V = CountedSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CountedSpec { items: self.items.deep_view(), final_v: self.final_v.deep_view() }
    }
}

impl<'i> Counted<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().items == self.items.deep_view(),
            self.deep_view().final_v == self.final_v.deep_view(),
    {
        reveal(<Counted as DeepView>::deep_view);
    }
}

/// data type for `uses_counted`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct UsesCounted<'i> {
    pub n: u8,
    pub body: Counted<'i>,
}

#[verifier::ext_equal]
pub struct UsesCountedSpec<T0 = u8, T1 = CountedSpec> {
    pub n: T0,
    pub body: T1,
}

pub type UsesCountedInner = (u8, CountedSpec);

impl<'i> DeepView for UsesCounted<'i> {
    type V = UsesCountedSpec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        UsesCountedSpec { n: self.n.deep_view(), body: self.body.deep_view() }
    }
}

impl<'i> UsesCounted<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().n == self.n.deep_view(),
            self.deep_view().body == self.body.deep_view(),
    {
        reveal(<UsesCounted as DeepView>::deep_view);
    }
}

// ============================================================
// Structural Mappers
// ============================================================
impl<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> InternalNamesSpec<
    T0,
    T1,
    T2,
    T3,
    T4,
    T5,
    T6,
    T7,
    T8,
    T9,
> {
    #[verifier::opaque]
    pub open spec fn from_structural(
        input: (T0, (T1, (T2, (T3, (T4, (T5, (T6, (T7, (T8, T9)))))))))
    ) -> Self {
        let (n, (l, (raw, (packed, (inner, (total, (total_len, (final_v, (x, tag))))))))) = input;
        Self { n, l, raw, packed, inner, total, total_len, final_v, x, tag }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, (T1, (T2, (T3, (T4, (T5, (T6, (T7,
        (T8, T9))))))))) {
        let Self { n, l, raw, packed, inner, total, total_len, final_v, x, tag } = self;
        (n, (l, (raw, (packed, (inner, (total, (total_len, (final_v, (x, tag)))))))))
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(InternalNamesSpec::from_structural);
        reveal(InternalNamesSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(
        input: (T0, (T1, (T2, (T3, (T4, (T5, (T6, (T7, (T8, T9)))))))))
    )
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(InternalNamesSpec::from_structural);
        reveal(InternalNamesSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { n, l, raw, packed, inner, total, total_len, final_v, x, tag } =>
                        (n, (l, (raw, (packed, (inner, (total, (total_len, (final_v,
                            (x, tag))))))))),
                },
    {
        reveal(InternalNamesSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct InternalNamesForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct InternalNamesReverse;

impl SpecMap for InternalNamesForward {
    type Input = InternalNamesInner;
    type Output = InternalNamesSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        InternalNamesSpec::from_structural(input)
    }
}

impl SpecMap for InternalNamesReverse {
    type Input = InternalNamesSpec;
    type Output = InternalNamesInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0, T1> WithBitsSpec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (flags, total_len) = input;
        Self { flags, total_len }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { flags, total_len } = self;
        (flags, total_len)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(WithBitsSpec::from_structural);
        reveal(WithBitsSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(WithBitsSpec::from_structural);
        reveal(WithBitsSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { flags, total_len } => (flags, total_len),
                },
    {
        reveal(WithBitsSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct WithBitsForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct WithBitsReverse;

impl SpecMap for WithBitsForward {
    type Input = WithBitsInner;
    type Output = WithBitsSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        WithBitsSpec::from_structural(input)
    }
}

impl SpecMap for WithBitsReverse {
    type Input = WithBitsSpec;
    type Output = WithBitsInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0, T1> CountedSpec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (items, final_v) = input;
        Self { items, final_v }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { items, final_v } = self;
        (items, final_v)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CountedSpec::from_structural);
        reveal(CountedSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CountedSpec::from_structural);
        reveal(CountedSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { items, final_v } => (items, final_v),
                },
    {
        reveal(CountedSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct CountedForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct CountedReverse;

impl SpecMap for CountedForward {
    type Input = CountedInner;
    type Output = CountedSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CountedSpec::from_structural(input)
    }
}

impl SpecMap for CountedReverse {
    type Input = CountedSpec;
    type Output = CountedInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0, T1> UsesCountedSpec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (n, body) = input;
        Self { n, body }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { n, body } = self;
        (n, body)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(UsesCountedSpec::from_structural);
        reveal(UsesCountedSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(UsesCountedSpec::from_structural);
        reveal(UsesCountedSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self)
                == match self {
                    Self { n, body } => (n, body),
                },
    {
        reveal(UsesCountedSpec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct UsesCountedForward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct UsesCountedReverse;

impl SpecMap for UsesCountedForward {
    type Input = UsesCountedInner;
    type Output = UsesCountedSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        UsesCountedSpec::from_structural(input)
    }
}

impl SpecMap for UsesCountedReverse {
    type Input = UsesCountedSpec;
    type Output = UsesCountedInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
/// named format combinator for `internal_names`.
#[derive(Clone, Copy)]
pub struct InternalNamesFmt;

pub type InternalNamesFmtSpec = Named<
    Mapped<
        Bind<
            U8,
            spec_fn(u8) -> Bind<
                U8,
                spec_fn(u8) -> Pair<
                    Varied<u8>,
                    Pair<Varied<u8>, Pair<U16Le, Pair<U16Le, Pair<U16Le, Pair<U8, Pair<U8, U8>>>>>>,
                >,
            >,
        >,
        BiMap<InternalNamesForward, InternalNamesReverse>,
    >,
>;

impl InternalNamesFmt {
    /// specification constructor for `internal_names`.
    pub open spec fn spec_inner() -> InternalNamesFmtSpec {
        Named(
            "internal_names",
            Mapped {
                inner: Bind(
                    U8,
                    |n: u8| Bind(
                        U8,
                        |l: u8| Pair(
                            Varied(n),
                            Pair(
                                Varied(l),
                                Pair(U16Le, Pair(U16Le, Pair(U16Le, Pair(U8, Pair(U8, U8))))),
                            ),
                        ),
                    ),
                ),
                mapper: BiMap(InternalNamesForward, InternalNamesReverse),
            },
        )
    }
}

/// named format combinator for `bit_names`.
#[derive(Clone, Copy)]
pub struct BitNamesFmt;

pub const BIT_NAMES_RAW_MASK: u8 = 0b00001111u8;
pub const BIT_NAMES_RAW_SHIFT: u8 = 4;
pub const BIT_NAMES_RAW_MAX: u8 = 0b00010000u8;
pub const BIT_NAMES_PACKED_MASK: u8 = 0b00000011u8;
pub const BIT_NAMES_PACKED_SHIFT: u8 = 2;
pub const BIT_NAMES_PACKED_MAX: u8 = 0b00000100u8;
pub const BIT_NAMES_X_MASK: u8 = 0b00000011u8;
pub const BIT_NAMES_X_SHIFT: u8 = 0;
pub const BIT_NAMES_X_MAX: u8 = 0b00000100u8;

#[verifier::allow_in_spec]
pub fn unpack_bit_names(raw: u8) -> (u8, u8, u8)
    returns
        (
            (((raw >> BIT_NAMES_RAW_SHIFT) & BIT_NAMES_RAW_MASK) as u8),
            (((raw >> BIT_NAMES_PACKED_SHIFT) & BIT_NAMES_PACKED_MASK) as u8),
            ((raw & BIT_NAMES_X_MASK) as u8),
        ),
{
    (
        (((raw >> BIT_NAMES_RAW_SHIFT) & BIT_NAMES_RAW_MASK) as u8),
        (((raw >> BIT_NAMES_PACKED_SHIFT) & BIT_NAMES_PACKED_MASK) as u8),
        ((raw & BIT_NAMES_X_MASK) as u8),
    )
}

#[verifier::allow_in_spec]
pub fn pack_bit_names(raw: u8, packed: u8, x: u8) -> u8
    returns
        (((raw as u8) & BIT_NAMES_RAW_MASK) << BIT_NAMES_RAW_SHIFT) | (
            ((packed as u8) & BIT_NAMES_PACKED_MASK) << BIT_NAMES_PACKED_SHIFT
        ) | (((x as u8) & BIT_NAMES_X_MASK)),
{
    (((raw as u8) & BIT_NAMES_RAW_MASK) << BIT_NAMES_RAW_SHIFT) | (
        ((packed as u8) & BIT_NAMES_PACKED_MASK) << BIT_NAMES_PACKED_SHIFT
    ) | (((x as u8) & BIT_NAMES_X_MASK))
}

#[verifier::allow_in_spec]
pub fn bit_names_bounds(raw: u8, packed: u8, x: u8) -> bool
    returns
        (raw < BIT_NAMES_RAW_MAX) &&(packed < BIT_NAMES_PACKED_MAX) &&(x < BIT_NAMES_X_MAX),
{
    (raw < BIT_NAMES_RAW_MAX) &&(packed < BIT_NAMES_PACKED_MAX) &&(x < BIT_NAMES_X_MAX)
}

pub broadcast proof fn lemma_bit_names_unpack_pack(raw: u8) by (bit_vector)
    ensures
        #[trigger] pack_bit_names(
            unpack_bit_names(raw).0,
            unpack_bit_names(raw).1,
            unpack_bit_names(raw).2,
        )
            == raw,
{}

pub broadcast proof fn lemma_bit_names_pack_unpack(raw: u8, packed: u8, x: u8) by (bit_vector)
    requires
        #[trigger] bit_names_bounds(raw, packed, x),
    ensures
        unpack_bit_names(pack_bit_names(raw, packed, x)).0 == raw,
        unpack_bit_names(pack_bit_names(raw, packed, x)).1 == packed,
        unpack_bit_names(pack_bit_names(raw, packed, x)).2 == x,
{}

pub broadcast proof fn lemma_bit_names_mapper_wf_in_out(i: u8) by (bit_vector)
    ensures
        #[trigger] bit_names_bounds(
            unpack_bit_names(i).0,
            unpack_bit_names(i).1,
            unpack_bit_names(i).2,
        ),
{}

pub type BitNamesFmtSpec = Named<Bits<U8, (u8, u8, u8), BitNamesSpec>>;

impl BitNamesFmt {
    /// specification constructor for `bit_names`.
    pub open spec fn spec_inner() -> BitNamesFmtSpec {
        Named(
            "bit_names",
            Bits {
                repr: U8,
                unpack: |packed: u8| unpack_bit_names(packed),
                pack: |unpacked: (u8, u8, u8)| {
                    let (raw, packed, x) = unpacked;
                    pack_bit_names(raw, packed, x)
                },
                refinement: |unpacked: (u8, u8, u8)| {
                    let (raw, packed, x) = unpacked;
                    true
                },
                ctor: |unpacked: (u8, u8, u8)| {
                    let (raw, packed, x) = unpacked;
                    BitNamesSpec { raw: raw, packed: packed, x: x }
                },
                dtor: |value: BitNamesSpec| {
                    let BitNamesSpec { raw, packed, x } = value;
                    (raw, packed, x)
                },
                consistent: |value: BitNamesSpec| {
                    let BitNamesSpec { raw, packed, x } = value;
                    bit_names_bounds(raw, packed, x)
                },
            },
        )
    }
}

/// named format combinator for `with_bits`.
#[derive(Clone, Copy)]
pub struct WithBitsFmt;

pub type WithBitsFmtSpec = Named<
    Mapped<Pair<BitNamesFmt, U8>, BiMap<WithBitsForward, WithBitsReverse>>,
>;

impl WithBitsFmt {
    /// specification constructor for `with_bits`.
    pub open spec fn spec_inner() -> WithBitsFmtSpec {
        Named(
            "with_bits",
            Mapped {
                inner: Pair(BitNamesFmt, U8),
                mapper: BiMap(WithBitsForward, WithBitsReverse),
            },
        )
    }
}

/// named format combinator for `counted`.
#[derive(Clone, Copy)]
pub struct CountedFmt {
    n: u8,
}

impl CountedFmt {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn n_spec(&self) -> u8 {
        self.n.deep_view()
    }

    pub closed spec fn spec(n: u8) -> Self {
        CountedFmt { n }
    }
}

pub type CountedFmtSpec = Named<
    Mapped<Pair<Varied<u8>, U8>, BiMap<CountedForward, CountedReverse>>,
>;

impl CountedFmt {
    /// specification constructor for `counted`.
    pub open spec fn spec_inner(n: u8) -> CountedFmtSpec {
        Named(
            "counted",
            Mapped { inner: Pair(Varied(n), U8), mapper: BiMap(CountedForward, CountedReverse) },
        )
    }
}

/// named format combinator for `uses_counted`.
#[derive(Clone, Copy)]
pub struct UsesCountedFmt;

pub type UsesCountedFmtSpec = Named<
    Mapped<Bind<U8, spec_fn(u8) -> CountedFmt>, BiMap<UsesCountedForward, UsesCountedReverse>>,
>;

impl UsesCountedFmt {
    /// specification constructor for `uses_counted`.
    pub open spec fn spec_inner() -> UsesCountedFmtSpec {
        Named(
            "uses_counted",
            Mapped {
                inner: Bind(U8, |n: u8| CountedFmt::spec(n)),
                mapper: BiMap(UsesCountedForward, UsesCountedReverse),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for InternalNamesFmt {
        type PVal = InternalNamesSpec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for InternalNamesFmt {
        type Val = InternalNamesSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for InternalNamesFmt {
        type SValue = InternalNamesSpec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for InternalNamesFmt {
        type SVal = InternalNamesSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for InternalNamesFmt {
        type T = InternalNamesSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for BitNamesFmt {
        type PVal = BitNamesSpec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for BitNamesFmt {
        type Val = BitNamesSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for BitNamesFmt {
        type SValue = BitNamesSpec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for BitNamesFmt {
        type SVal = BitNamesSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for BitNamesFmt {
        type T = BitNamesSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for WithBitsFmt {
        type PVal = WithBitsSpec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for WithBitsFmt {
        type Val = WithBitsSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for WithBitsFmt {
        type SValue = WithBitsSpec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for WithBitsFmt {
        type SVal = WithBitsSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for WithBitsFmt {
        type T = WithBitsSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for CountedFmt {
        type PVal = CountedSpec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.n_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CountedFmt {
        type Val = CountedSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.n_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CountedFmt {
        type SValue = CountedSpec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.n_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CountedFmt {
        type SVal = CountedSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.n_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CountedFmt {
        type T = CountedSpec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.n_spec()).byte_len(v)
        }
    }

    impl SpecParser for UsesCountedFmt {
        type PVal = UsesCountedSpec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for UsesCountedFmt {
        type Val = UsesCountedSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for UsesCountedFmt {
        type SValue = UsesCountedSpec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for UsesCountedFmt {
        type SVal = UsesCountedSpec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for UsesCountedFmt {
        type T = UsesCountedSpec;

        #[verifier::opaque]
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
        InternalNamesSpec::lemma_from_into,
        InternalNamesSpec::lemma_into_from,
        WithBitsSpec::lemma_from_into,
        WithBitsSpec::lemma_into_from,
        CountedSpec::lemma_from_into,
        CountedSpec::lemma_into_from,
        UsesCountedSpec::lemma_from_into,
        UsesCountedSpec::lemma_into_from,
    };

    impl SafeParser for InternalNamesFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<InternalNamesFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for InternalNamesFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<InternalNamesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for InternalNamesFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<InternalNamesFmt as SpecParser>::spec_parse);
            reveal(<InternalNamesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: InternalNamesInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                InternalNamesSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<InternalNamesFmt as SpecParser>::spec_parse);
            reveal(<InternalNamesFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: InternalNamesInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                InternalNamesSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for InternalNamesFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<InternalNamesFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<InternalNamesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<InternalNamesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for InternalNamesFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<InternalNamesFmt as SpecSerializer>::spec_serialize);
            reveal(<InternalNamesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for InternalNamesFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<InternalNamesFmt as SpecParser>::spec_parse);
            reveal(<InternalNamesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<InternalNamesFmt as Consistency>::consistent);
            reveal(<InternalNamesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: InternalNamesSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                InternalNamesSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for InternalNamesFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<InternalNamesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: InternalNamesInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                InternalNamesSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for InternalNamesFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<InternalNamesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<InternalNamesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for InternalNamesFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<InternalNamesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<InternalNamesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for BitNamesFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<BitNamesFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for BitNamesFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<BitNamesFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for BitNamesFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<BitNamesFmt as SpecParser>::spec_parse);
            reveal(<BitNamesFmt as SpecByteLen>::byte_len);
            let fmt = BitNamesFmt::spec_inner();
            broadcast use lemma_bit_names_unpack_pack, lemma_bit_names_mapper_wf_in_out;
            assert(fmt.1.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<BitNamesFmt as SpecParser>::spec_parse);
            reveal(<BitNamesFmt as Consistency>::consistent);
            broadcast use lemma_bit_names_unpack_pack, lemma_bit_names_mapper_wf_in_out;
            let fmt = BitNamesFmt::spec_inner();
            assert(fmt.1.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for BitNamesFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BitNamesFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<BitNamesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BitNamesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for BitNamesFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<BitNamesFmt as SpecSerializer>::spec_serialize);
            reveal(<BitNamesFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for BitNamesFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<BitNamesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BitNamesFmt as SpecByteLen>::byte_len);
            reveal(<BitNamesFmt as SpecParser>::spec_parse);
            broadcast use lemma_bit_names_pack_unpack;
            let fmt = BitNamesFmt::spec_inner();
            assert(fmt.1.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for BitNamesFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<BitNamesFmt as SpecParser>::spec_parse);
            broadcast use lemma_bit_names_unpack_pack, lemma_bit_names_mapper_wf_in_out;
            let fmt = BitNamesFmt::spec_inner();
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for BitNamesFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<BitNamesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BitNamesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for BitNamesFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<BitNamesFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<BitNamesFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for WithBitsFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<WithBitsFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for WithBitsFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<WithBitsFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for WithBitsFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<WithBitsFmt as SpecParser>::spec_parse);
            reveal(<WithBitsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: WithBitsInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WithBitsSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<WithBitsFmt as SpecParser>::spec_parse);
            reveal(<WithBitsFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: WithBitsInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WithBitsSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for WithBitsFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WithBitsFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<WithBitsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WithBitsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for WithBitsFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<WithBitsFmt as SpecSerializer>::spec_serialize);
            reveal(<WithBitsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for WithBitsFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<WithBitsFmt as SpecParser>::spec_parse);
            reveal(<WithBitsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WithBitsFmt as Consistency>::consistent);
            reveal(<WithBitsFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: WithBitsSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                WithBitsSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for WithBitsFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<WithBitsFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: WithBitsInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                WithBitsSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for WithBitsFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<WithBitsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WithBitsFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for WithBitsFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<WithBitsFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<WithBitsFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CountedFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CountedFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.n_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CountedFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.n_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CountedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.n_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CountedFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CountedFmt as SpecParser>::spec_parse);
            reveal(<CountedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.n_spec());
            assert forall|input: CountedInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CountedSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CountedFmt as SpecParser>::spec_parse);
            reveal(<CountedFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.n_spec());
            assert forall|input: CountedInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CountedSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CountedFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CountedFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.n_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CountedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CountedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.n_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CountedFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CountedFmt as SpecSerializer>::spec_serialize);
            reveal(<CountedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.n_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CountedFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CountedFmt as SpecParser>::spec_parse);
            reveal(<CountedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CountedFmt as Consistency>::consistent);
            reveal(<CountedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.n_spec());
            assert forall|output: CountedSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CountedSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CountedFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CountedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.n_spec());
            assert forall|input: CountedInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CountedSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CountedFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CountedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CountedFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.n_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CountedFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CountedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CountedFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.n_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for UsesCountedFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<UsesCountedFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for UsesCountedFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<UsesCountedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for UsesCountedFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<UsesCountedFmt as SpecParser>::spec_parse);
            reveal(<UsesCountedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: UsesCountedInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                UsesCountedSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<UsesCountedFmt as SpecParser>::spec_parse);
            reveal(<UsesCountedFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: UsesCountedInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                UsesCountedSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for UsesCountedFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<UsesCountedFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<UsesCountedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<UsesCountedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for UsesCountedFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<UsesCountedFmt as SpecSerializer>::spec_serialize);
            reveal(<UsesCountedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for UsesCountedFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<UsesCountedFmt as SpecParser>::spec_parse);
            reveal(<UsesCountedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<UsesCountedFmt as Consistency>::consistent);
            reveal(<UsesCountedFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: UsesCountedSpec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                UsesCountedSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for UsesCountedFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<UsesCountedFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: UsesCountedInner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                UsesCountedSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for UsesCountedFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<UsesCountedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<UsesCountedFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for UsesCountedFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<UsesCountedFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<UsesCountedFmt as SpecSerializer>::spec_serialize);
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

    impl<'i> Parser<&'i [u8]> for InternalNamesFmt {
        type PT = InternalNames<'i>;

        fn min_byte_len(&self) -> usize {
            11
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<InternalNamesFmt as SpecParser>::spec_parse);
            reveal(<InternalNames as DeepView>::deep_view);
            reveal(InternalNamesSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, n) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, l) = (U8).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, raw) = (Varied(n)).parse(&rest)?;
            let rest = rest.skip(n3);
            let (n4, packed) = (Varied(l)).parse(&rest)?;
            let rest = rest.skip(n4);
            let (n5, inner) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n5);
            let (n6, total) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n6);
            let (n7, total_len) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n7);
            let (n8, final_v) = (U8).parse(&rest)?;
            let rest = rest.skip(n8);
            let (n9, x) = (U8).parse(&rest)?;
            let rest = rest.skip(n9);
            let (n10, tag) = (U8).parse(&rest)?;
            let rest = rest.skip(n10);
            let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n10;

            let final_v = InternalNames {
                n,
                l,
                raw,
                packed,
                inner,
                total,
                total_len,
                final_v,
                x,
                tag,
            };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, InternalNames<'i>> for InternalNamesFmt {
        fn serialize_into(&self, v: &InternalNames<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<InternalNamesFmt as SpecSerializer>::spec_serialize);
            reveal(<InternalNamesFmt as SpecByteLen>::byte_len);
            reveal(<InternalNames as DeepView>::deep_view);
            reveal(InternalNamesSpec::into_structural);
            let ghost old_obuf = obuf@;

            let InternalNames { n, l, raw, packed, inner, total, total_len, final_v, x, tag } = v;

            U8.serialize_into(n, obuf);
            U8.serialize_into(l, obuf);
            Varied(*n).serialize_into(*raw, obuf);
            Varied(*l).serialize_into(*packed, obuf);
            U16Le.serialize_into(inner, obuf);
            U16Le.serialize_into(total, obuf);
            U16Le.serialize_into(total_len, obuf);
            U8.serialize_into(final_v, obuf);
            U8.serialize_into(x, obuf);
            U8.serialize_into(tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<InternalNames<'i>> for InternalNamesFmt {
        fn prepare(&self, v: &InternalNames<'i>) -> Result<usize, PreSerializeError> {
            reveal(<InternalNamesFmt as SpecByteLen>::byte_len);
            reveal(<InternalNames as DeepView>::deep_view);
            reveal(InternalNamesSpec::into_structural);
            let InternalNames { n, l, raw, packed, inner, total, total_len, final_v, x, tag } = v;
            let l1 = (U8).prepare(n)?;
            let l2 = (U8).prepare(l)?;
            let l3 = (Varied(*n)).prepare(raw)?;
            let l4 = (Varied(*l)).prepare(packed)?;
            let l5 = (U16Le).prepare(inner)?;
            let l6 = (U16Le).prepare(total)?;
            let l7 = (U16Le).prepare(total_len)?;
            let l8 = (U8).prepare(final_v)?;
            let l9 = (U8).prepare(x)?;
            let l10 = (U8).prepare(tag)?;
            let total_len = l1
                .checked_add(l2)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l3)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l4)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l5)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l6)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l7)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l8)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l9)
                .ok_or(PreSerializeError::length_too_large())?
                .checked_add(l10)
                .ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for BitNamesFmt {
        type PT = BitNames;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<BitNamesFmt as SpecParser>::spec_parse);
            reveal(<BitNames as DeepView>::deep_view);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, raw) = U8.parse(ibuf)?;
            let (raw, packed, x) = unpack_bit_names(raw);
            let final_v = BitNames { raw: raw, packed: packed, x: x };
            assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));
            Ok((n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, BitNames> for BitNamesFmt {
        fn serialize_into(&self, v: &BitNames, obuf: &mut Output) {
            reveal(<BitNamesFmt as SpecSerializer>::spec_serialize);
            reveal(<BitNamesFmt as SpecByteLen>::byte_len);
            reveal(<BitNames as DeepView>::deep_view);
            let ghost old_obuf = obuf@;

            let BitNames { raw, packed, x } = *v;
            let packed = pack_bit_names(raw, packed, x);
            U8.serialize_into(&packed, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<BitNames> for BitNamesFmt {
        fn prepare(&self, v: &BitNames) -> Result<usize, PreSerializeError> {
            reveal(<BitNamesFmt as SpecByteLen>::byte_len);
            reveal(<BitNames as DeepView>::deep_view);
            let BitNames { raw, packed, x } = *v;
            if !(bit_names_bounds(raw, packed, x)) {
                return Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed));
            }
            let packed = pack_bit_names(raw, packed, x);
            U8.prepare(&packed)
        }
    }

    impl<'i> Parser<&'i [u8]> for WithBitsFmt {
        type PT = WithBits;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<WithBitsFmt as SpecParser>::spec_parse);
            reveal(<WithBits as DeepView>::deep_view);
            reveal(WithBitsSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, flags) = (Named("bit_names", BitNamesFmt)).parse(&rest)?;

            proof {
                flags.lemma_deep_view();
            }

            let rest = rest.skip(n1);
            let (n2, total_len) = (U8).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;

            let final_v = WithBits { flags, total_len };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, WithBits> for WithBitsFmt {
        fn serialize_into(&self, v: &WithBits, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<WithBitsFmt as SpecSerializer>::spec_serialize);
            reveal(<WithBitsFmt as SpecByteLen>::byte_len);
            reveal(<WithBits as DeepView>::deep_view);
            reveal(WithBitsSpec::into_structural);
            let ghost old_obuf = obuf@;

            let WithBits { flags, total_len } = v;

            proof {
                flags.lemma_deep_view();
            }

            BitNamesFmt.serialize_into(flags, obuf);
            U8.serialize_into(total_len, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<WithBits> for WithBitsFmt {
        fn prepare(&self, v: &WithBits) -> Result<usize, PreSerializeError> {
            reveal(<WithBitsFmt as SpecByteLen>::byte_len);
            reveal(<WithBits as DeepView>::deep_view);
            reveal(WithBitsSpec::into_structural);
            let WithBits { flags, total_len } = v;
            proof {
                flags.lemma_deep_view();
            }

            let l1 = (Named("bit_names", BitNamesFmt)).prepare(flags)?;
            let l2 = (U8).prepare(total_len)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CountedFmt {
        type PT = Counted<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CountedFmt as SpecParser>::spec_parse);
            reveal(<Counted as DeepView>::deep_view);
            reveal(CountedSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, items) = (Varied(self.n)).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, final_v) = (U8).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;

            let final_v = Counted { items, final_v };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Counted<'i>> for CountedFmt {
        fn serialize_into(&self, v: &Counted<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<CountedFmt as SpecSerializer>::spec_serialize);
            reveal(<CountedFmt as SpecByteLen>::byte_len);
            reveal(<Counted as DeepView>::deep_view);
            reveal(CountedSpec::into_structural);

            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let Counted { items, final_v } = v;

            Varied(self.n).serialize_into(*items, obuf);
            U8.serialize_into(final_v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Counted<'i>> for CountedFmt {
        fn prepare(&self, v: &Counted<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CountedFmt as SpecByteLen>::byte_len);
            reveal(<Counted as DeepView>::deep_view);
            reveal(CountedSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let Counted { items, final_v } = v;
            let l1 = (Varied(self.n)).prepare(items)?;
            let l2 = (U8).prepare(final_v)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for UsesCountedFmt {
        type PT = UsesCounted<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<UsesCountedFmt as SpecParser>::spec_parse);
            reveal(<UsesCounted as DeepView>::deep_view);
            reveal(UsesCountedSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, n) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, body) = (Named("counted", CountedFmt { n: n })).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;

            let final_v = UsesCounted { n, body };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, UsesCounted<'i>> for UsesCountedFmt {
        fn serialize_into(&self, v: &UsesCounted<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<UsesCountedFmt as SpecSerializer>::spec_serialize);
            reveal(<UsesCountedFmt as SpecByteLen>::byte_len);
            reveal(<UsesCounted as DeepView>::deep_view);
            reveal(UsesCountedSpec::into_structural);
            let ghost old_obuf = obuf@;

            let UsesCounted { n, body } = v;

            U8.serialize_into(n, obuf);

            CountedFmt { n: *n }.serialize_into(body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<UsesCounted<'i>> for UsesCountedFmt {
        fn prepare(&self, v: &UsesCounted<'i>) -> Result<usize, PreSerializeError> {
            reveal(<UsesCountedFmt as SpecByteLen>::byte_len);
            reveal(<UsesCounted as DeepView>::deep_view);
            reveal(UsesCountedSpec::into_structural);
            let UsesCounted { n, body } = v;
            let l1 = (U8).prepare(n)?;
            let l2 = (Named("counted", CountedFmt { n: *n })).prepare(body)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }
}
}
