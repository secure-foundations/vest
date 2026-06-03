#![allow(warnings)]
use vest_lib2::combinators::mapped::spec::*;
use vest_lib2::combinators::*;
use vest_lib2::core::exec::input::{InputBuf, InputSlice};
use vest_lib2::core::exec::parser::*;
use vest_lib2::core::exec::serializer::*;
use vest_lib2::core::exec::ParseError;
use vest_lib2::core::exec::{DeepEq, SelfView};
use vest_lib2::core::{proof::*, spec::*};
use vest_lib2::macros::impl_self_view_for;
use vest_lib2::primitives::btcvarint::VarInt;
use vest_lib2::primitives::leb128::ULeb128;
use vstd::prelude::*;
use Sum::Inl as L;
use Sum::Inr as R;
verus! {

// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `msg1`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg1<'i> {
    pub a: u8,
    pub b: u16,
    pub c: &'i [u8],
}

# [verifier::ext_equal]
pub struct Msg1Spec {
    pub a: u8,
    pub b: u16,
    pub c: Seq<u8>,
}

pub type Msg1Inner = (u8, (u16, Seq<u8>));

impl<'i> DeepView for Msg1<'i> {
    type V = Msg1Spec;

    open spec fn deep_view(&self) -> Self::V {
        Msg1Spec { a: self.a.deep_view(), b: self.b.deep_view(), c: self.c.deep_view() }
    }
}

# [doc = "data type for `msg2`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct Msg2 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

pub type Msg2Spec = Msg2;

pub type Msg2Inner = (u8, (u16, u32));

impl DeepView for Msg2 {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `a_type`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum AType {
    A = 0,
    B = 1,
    C = 2,
}

pub type ATypeSpec = AType;

pub type ATypeInner = u8;

impl DeepView for AType {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl DeepEq for AType {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for AType {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `msg3`."]
pub type Msg3<'i> = &'i [u8];

pub type Msg3Spec = Seq<u8>;

# [doc = "data type for `msg4_val`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum Msg4Val<'i> {
    A(Msg1<'i>),
    B(Msg2),
    C(Msg3<'i>),
}

# [verifier::ext_equal]
pub enum Msg4ValSpec {
    A(Msg1Spec),
    B(Msg2Spec),
    C(Msg3Spec),
}

pub type Msg4ValInner = Sum<Msg1Spec, Sum<Msg2Spec, Msg3Spec>>;

impl<'i> DeepView for Msg4Val<'i> {
    type V = Msg4ValSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            Msg4Val::A(v) => Msg4ValSpec::A(v.deep_view()),
            Msg4Val::B(v) => Msg4ValSpec::B(v.deep_view()),
            Msg4Val::C(v) => Msg4ValSpec::C(v.deep_view()),
        }
    }
}

# [doc = "data type for `msg4`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg4<'i> {
    pub t: AType,
    pub val: Msg4Val<'i>,
    pub tail: &'i [u8],
}

# [verifier::ext_equal]
pub struct Msg4Spec {
    pub t: ATypeSpec,
    pub val: Msg4ValSpec,
    pub tail: Seq<u8>,
}

pub type Msg4Inner = (ATypeSpec, (Msg4ValSpec, Seq<u8>));

impl<'i> DeepView for Msg4<'i> {
    type V = Msg4Spec;

    open spec fn deep_view(&self) -> Self::V {
        Msg4Spec { t: self.t.deep_view(), val: self.val.deep_view(), tail: self.tail.deep_view() }
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `msg1`."]
# [derive (Clone, Copy)]
pub struct Msg1Fmt;

pub type Msg1FmtSpec = Named<
    Mapped<
        Pair<Refined<U8, PredFnSpec<u8>>, Pair<U16Le, Fixed<3>>>,
        FnSpecMapper<Msg1Inner, Msg1Spec>,
    >,
>;

impl Msg1Fmt {
    # [doc = "specification constructor for `msg1`."]
    pub open spec fn spec_inner() -> Msg1FmtSpec {
        Named(
            "msg1",
            Mapped {
                inner: Pair(
                    Refined(U8, |x: u8| x >= 0 && x <= 10 || x == 32 || x >= 100),
                    Pair(U16Le, Fixed::<3>),
                ),
                mapper: (
                    |parsed: Msg1Inner| -> Msg1Spec
                        {
                            let (a, (b, c)) = parsed;
                            Msg1Spec { a, b, c }
                        },
                    |value: Msg1Spec| -> Msg1Inner
                        {
                            let Msg1Spec { a, b, c } = value;
                            (a, (b, c))
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg2`."]
# [derive (Clone, Copy)]
pub struct Msg2Fmt;

pub type Msg2FmtSpec = Named<
    Mapped<Pair<U8, Pair<U16Le, U32Le>>, FnSpecMapper<Msg2Inner, Msg2Spec>>,
>;

impl Msg2Fmt {
    # [doc = "specification constructor for `msg2`."]
    pub open spec fn spec_inner() -> Msg2FmtSpec {
        Named(
            "msg2",
            Mapped {
                inner: Pair(U8, Pair(U16Le, U32Le)),
                mapper: (
                    |parsed: Msg2Inner| -> Msg2Spec
                        {
                            let (a, (b, c)) = parsed;
                            Msg2Spec { a, b, c }
                        },
                    |value: Msg2Spec| -> Msg2Inner
                        {
                            let Msg2Spec { a, b, c } = value;
                            (a, (b, c))
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `a_type`."]
# [derive (Clone, Copy)]
pub struct ATypeFmt;

pub type ATypeFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<ATypeInner, ATypeSpec>>,
>;

impl ATypeFmt {
    # [doc = "specification constructor for `a_type`."]
    pub open spec fn spec_inner() -> ATypeFmtSpec {
        Named(
            "a_type",
            Mapped {
                inner: Refined(U8, |x: u8| x == 0 || x == 1 || x == 2),
                mapper: (
                    |parsed: ATypeInner| -> ATypeSpec
                        {
                            match parsed {
                                0 => ATypeSpec::A,
                                1 => ATypeSpec::B,
                                2 => ATypeSpec::C,
                                _ => arbitrary(),
                            }
                        },
                    |value: ATypeSpec| -> ATypeInner
                        {
                            match value {
                                ATypeSpec::A => 0,
                                ATypeSpec::B => 1,
                                ATypeSpec::C => 2,
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg3`."]
# [derive (Clone, Copy)]
pub struct Msg3Fmt;

pub type Msg3FmtSpec = Named<Fixed<6>>;

impl Msg3Fmt {
    # [doc = "specification constructor for `msg3`."]
    pub open spec fn spec_inner() -> Msg3FmtSpec {
        Named("msg3", Fixed::<6>)
    }
}

# [doc = "named format combinator for `msg4_val`."]
# [derive (Clone, Copy)]
pub struct Msg4ValFmt {
    t: AType,
}

impl Msg4ValFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        ATypeFmt.consistent(self.t.deep_view())
    }

    pub closed spec fn t_spec(&self) -> ATypeSpec {
        self.t.deep_view()
    }

    pub closed spec fn spec(t: AType) -> Self {
        Msg4ValFmt { t }
    }
}

pub type Msg4ValFmtSpec = Named<
    Mapped<Sum<Msg1Fmt, Sum<Msg2Fmt, Msg3Fmt>>, FnSpecMapper<Msg4ValInner, Msg4ValSpec>>,
>;

impl Msg4ValFmt {
    # [doc = "specification constructor for `msg4_val`."]
    pub open spec fn spec_inner(t: ATypeSpec) -> Msg4ValFmtSpec {
        Named(
            "msg4_val",
            Mapped {
                inner: match t {
                    ATypeSpec::A => L(Msg1Fmt),
                    ATypeSpec::B => R(L(Msg2Fmt)),
                    ATypeSpec::C => R(R(Msg3Fmt)),
                },
                mapper: (
                    |parsed: Msg4ValInner| -> Msg4ValSpec
                        {
                            match parsed {
                                L(v) => Msg4ValSpec::A(v),
                                R(L(v)) => Msg4ValSpec::B(v),
                                R(R(v)) => Msg4ValSpec::C(v),
                            }
                        },
                    |value: Msg4ValSpec| -> Msg4ValInner
                        {
                            match value {
                                Msg4ValSpec::A(v) => L(v),
                                Msg4ValSpec::B(v) => R(L(v)),
                                Msg4ValSpec::C(v) => R(R(v)),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg4`."]
# [derive (Clone, Copy)]
pub struct Msg4Fmt;

pub type Msg4FmtSpec = Named<
    Mapped<
        Bind<ATypeFmt, spec_fn(ATypeSpec) -> Pair<Msg4ValFmt, Tail>>,
        FnSpecMapper<Msg4Inner, Msg4Spec>,
    >,
>;

impl Msg4Fmt {
    # [doc = "specification constructor for `msg4`."]
    pub open spec fn spec_inner() -> Msg4FmtSpec {
        Named(
            "msg4",
            Mapped {
                inner: Bind(ATypeFmt, |t: ATypeSpec| Pair(Msg4ValFmt::spec(t), Tail)),
                mapper: (
                    |parsed: Msg4Inner| -> Msg4Spec
                        {
                            let (t, (val, tail)) = parsed;
                            Msg4Spec { t, val, tail }
                        },
                    |value: Msg4Spec| -> Msg4Inner
                        {
                            let Msg4Spec { t, val, tail } = value;
                            (t, (val, tail))
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

    impl SpecParser for Msg1Fmt {
        type PVal = Msg1Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Msg1Fmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg1Fmt {
        type Val = Msg1Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Msg1Fmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg1Fmt {
        type SValue = Msg1Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Msg1Fmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg1Fmt {
        type SVal = Msg1Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Msg1Fmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg1Fmt {
        type T = Msg1Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Msg1Fmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Msg2Fmt {
        type PVal = Msg2Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Msg2Fmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg2Fmt {
        type Val = Msg2Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Msg2Fmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg2Fmt {
        type SValue = Msg2Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Msg2Fmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg2Fmt {
        type SVal = Msg2Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Msg2Fmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg2Fmt {
        type T = Msg2Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Msg2Fmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ATypeFmt {
        type PVal = ATypeSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ATypeFmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ATypeFmt {
        type Val = ATypeSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            ATypeFmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ATypeFmt {
        type SValue = ATypeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ATypeFmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ATypeFmt {
        type SVal = ATypeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            ATypeFmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ATypeFmt {
        type T = ATypeSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            ATypeFmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Msg3Fmt {
        type PVal = Msg3Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Msg3Fmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg3Fmt {
        type Val = Msg3Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Msg3Fmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg3Fmt {
        type SValue = Msg3Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Msg3Fmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg3Fmt {
        type SVal = Msg3Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Msg3Fmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg3Fmt {
        type T = Msg3Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Msg3Fmt::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Msg4ValFmt {
        type PVal = Msg4ValSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Msg4ValFmt::spec_inner(self.t_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for Msg4ValFmt {
        type Val = Msg4ValSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Msg4ValFmt::spec_inner(self.t_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for Msg4ValFmt {
        type SValue = Msg4ValSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Msg4ValFmt::spec_inner(self.t_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg4ValFmt {
        type SVal = Msg4ValSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Msg4ValFmt::spec_inner(self.t_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg4ValFmt {
        type T = Msg4ValSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Msg4ValFmt::spec_inner(self.t_spec()).byte_len(v)
        }
    }

    impl SpecParser for Msg4Fmt {
        type PVal = Msg4Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Msg4Fmt::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg4Fmt {
        type Val = Msg4Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Msg4Fmt::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg4Fmt {
        type SValue = Msg4Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Msg4Fmt::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg4Fmt {
        type SVal = Msg4Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Msg4Fmt::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg4Fmt {
        type T = Msg4Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Msg4Fmt::spec_inner().byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

    impl SafeParser for Msg1Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            Msg1Fmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg1Fmt {
        open spec fn productive_inv(&self) -> bool {
            Msg1Fmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            let fmt = Msg1Fmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg1Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Msg1Fmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1Fmt as Consistency>::consistent);
            let fmt = Msg1Fmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg1Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Msg1Fmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Msg1Fmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg1Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Msg1Fmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg1Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as Consistency>::consistent);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Msg1Fmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg1Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            let fmt = Msg1Fmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg1Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            let fmt = Msg1Fmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg1Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            let fmt = Msg1Fmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg2Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            Msg2Fmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg2Fmt {
        open spec fn productive_inv(&self) -> bool {
            Msg2Fmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            let fmt = Msg2Fmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg2Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Msg2Fmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2Fmt as Consistency>::consistent);
            let fmt = Msg2Fmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg2Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Msg2Fmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Msg2Fmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg2Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Msg2Fmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg2Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as Consistency>::consistent);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Msg2Fmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg2Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            let fmt = Msg2Fmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg2Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            let fmt = Msg2Fmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg2Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            let fmt = Msg2Fmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ATypeFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            ATypeFmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ATypeFmt {
        open spec fn productive_inv(&self) -> bool {
            ATypeFmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            let fmt = ATypeFmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ATypeFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            reveal(<ATypeFmt as SpecByteLen>::byte_len);
            let fmt = ATypeFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            reveal(<ATypeFmt as Consistency>::consistent);
            let fmt = ATypeFmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ATypeFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = ATypeFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypeFmt as SpecByteLen>::byte_len);
            let fmt = ATypeFmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ATypeFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ATypeFmt as SpecSerializer>::spec_serialize);
            reveal(<ATypeFmt as SpecByteLen>::byte_len);
            let fmt = ATypeFmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ATypeFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            reveal(<ATypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypeFmt as Consistency>::consistent);
            reveal(<ATypeFmt as SpecByteLen>::byte_len);
            let fmt = ATypeFmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ATypeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ATypeFmt as SpecParser>::spec_parse);
            let fmt = ATypeFmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ATypeFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ATypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypeFmt as SpecSerializer>::spec_serialize);
            let fmt = ATypeFmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ATypeFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ATypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ATypeFmt as SpecSerializer>::spec_serialize);
            let fmt = ATypeFmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg3Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            Msg3Fmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg3Fmt {
        open spec fn productive_inv(&self) -> bool {
            Msg3Fmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            let fmt = Msg3Fmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg3Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Msg3Fmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            reveal(<Msg3Fmt as Consistency>::consistent);
            let fmt = Msg3Fmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg3Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Msg3Fmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Msg3Fmt::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg3Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Msg3Fmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg3Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as Consistency>::consistent);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Msg3Fmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg3Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            let fmt = Msg3Fmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg3Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            let fmt = Msg3Fmt::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg3Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            let fmt = Msg3Fmt::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg4ValFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            Msg4ValFmt::spec_inner(self.t_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg4ValFmt {
        open spec fn productive_inv(&self) -> bool {
            Msg4ValFmt::spec_inner(self.t_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            let fmt = Msg4ValFmt::spec_inner(self.t_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg4ValFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            reveal(<Msg4ValFmt as SpecByteLen>::byte_len);
            let fmt = Msg4ValFmt::spec_inner(self.t_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            reveal(<Msg4ValFmt as Consistency>::consistent);
            let fmt = Msg4ValFmt::spec_inner(self.t_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg4ValFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Msg4ValFmt::spec_inner(self.t_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ValFmt as SpecByteLen>::byte_len);
            let fmt = Msg4ValFmt::spec_inner(self.t_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg4ValFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg4ValFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg4ValFmt as SpecByteLen>::byte_len);
            let fmt = Msg4ValFmt::spec_inner(self.t_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg4ValFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            reveal(<Msg4ValFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ValFmt as Consistency>::consistent);
            reveal(<Msg4ValFmt as SpecByteLen>::byte_len);
            let fmt = Msg4ValFmt::spec_inner(self.t_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg4ValFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            let fmt = Msg4ValFmt::spec_inner(self.t_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg4ValFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg4ValFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ValFmt as SpecSerializer>::spec_serialize);
            let fmt = Msg4ValFmt::spec_inner(self.t_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg4ValFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg4ValFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ValFmt as SpecSerializer>::spec_serialize);
            let fmt = Msg4ValFmt::spec_inner(self.t_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg4Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            Msg4Fmt::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg4Fmt {
        open spec fn productive_inv(&self) -> bool {
            Msg4Fmt::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            let fmt = Msg4Fmt::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg4Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            let fmt = Msg4Fmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            reveal(<Msg4Fmt as Consistency>::consistent);
            let fmt = Msg4Fmt::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for Msg4Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg4Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            let fmt = Msg4Fmt::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg4Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            reveal(<Msg4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4Fmt as Consistency>::consistent);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            let fmt = Msg4Fmt::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg4Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            let fmt = Msg4Fmt::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for Msg4Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4Fmt as SpecSerializer>::spec_serialize);
            let fmt = Msg4Fmt::spec_inner();
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

    impl<'i> Parser<&'i [u8]> for Msg1Fmt {
        type PT = Msg1<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, a) = U8.parse(&rest)?;
            if !(a >= 0 && a <= 10 || a == 32 || a >= 100) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, b) = U16Le.parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, c) = Fixed::<3>.parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Msg1 { a, b, c };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Msg1<'i>> for Msg1Fmt {
        fn serialize(&self, v: &Msg1<'i>, obuf: &mut Vec<u8>) {
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Msg1 { a, b, c } = v;
            U8.serialize(a, obuf);
            U16Le.serialize(b, obuf);
            Fixed::<3>.serialize(c, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg2Fmt {
        type PT = Msg2;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, a) = U8.parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, b) = U16Le.parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, c) = U32Le.parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Msg2 { a, b, c };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Msg2> for Msg2Fmt {
        fn serialize(&self, v: &Msg2, obuf: &mut Vec<u8>) {
            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Msg2 { a, b, c } = v;
            U8.serialize(a, obuf);
            U16Le.serialize(b, obuf);
            U32Le.serialize(c, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for ATypeFmt {
        type PT = AType;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<ATypeFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                0 => AType::A,
                1 => AType::B,
                2 => AType::C,
                _ => return Err(ParseError::invalid_tag()),
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
            Ok((n, enum_val))
        }
    }

    impl<'i> Serializer<AType> for ATypeFmt {
        fn serialize(&self, v: &AType, obuf: &mut Vec<u8>) {
            reveal(<ATypeFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                AType::A => 0,
                AType::B => 1,
                AType::C => 2,
            };
            U8.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg3Fmt {
        type PT = Msg3<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = Fixed::<6>.parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<Msg3<'i>> for Msg3Fmt {
        fn serialize(&self, v: &Msg3<'i>, obuf: &mut Vec<u8>) {
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            Fixed::<6>.serialize(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg4ValFmt {
        type PT = Msg4Val<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg4ValFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.t {
                AType::A => {
                    let (n, v) = (Msg1Fmt).parse(&rest)?;
                    (n, Msg4Val::A(v))
                },
                AType::B => {
                    let (n, v) = (Msg2Fmt).parse(&rest)?;
                    (n, Msg4Val::B(v))
                },
                AType::C => {
                    let (n, v) = (Msg3Fmt).parse(&rest)?;
                    (n, Msg4Val::C(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<Msg4Val<'i>> for Msg4ValFmt {
        fn serialize(&self, v: &Msg4Val<'i>, obuf: &mut Vec<u8>) {
            reveal(<Msg4ValFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.t, v) {
                (AType::A, Msg4Val::A(v)) => {
                    (Msg1Fmt).serialize(v, obuf);
                },
                (AType::B, Msg4Val::B(v)) => {
                    (Msg2Fmt).serialize(v, obuf);
                },
                (AType::C, Msg4Val::C(v)) => {
                    (Msg3Fmt).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg4Fmt {
        type PT = Msg4<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, t) = ATypeFmt.parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, val) = Msg4ValFmt { t: t }.parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, tail) = Tail.parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Msg4 { t, val, tail };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Msg4<'i>> for Msg4Fmt {
        fn serialize(&self, v: &Msg4<'i>, obuf: &mut Vec<u8>) {
            reveal(<Msg4Fmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Msg4 { t, val, tail } = v;
            ATypeFmt.serialize(t, obuf);
            Msg4ValFmt { t: *t }.serialize(val, obuf);
            Tail.serialize(tail, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

}

} // verus!
