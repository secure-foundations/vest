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
# [doc = "data type for `F5`."]
pub type F5 = [u8; 5];

pub type F5Spec = Seq<u8>;

# [doc = "data type for `msg_d`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct MsgD {
    pub f1: [u8; 4],
    pub f2: u16,
    pub c: [u8; 5],
}

# [verifier::ext_equal]
pub struct MsgDSpec {
    pub f1: Seq<u8>,
    pub f2: u16,
    pub c: Seq<u8>,
}

pub type MsgDInner = (Seq<u8>, (u16, Seq<u8>));

impl DeepView for MsgD {
    type V = MsgDSpec;

    open spec fn deep_view(&self) -> Self::V {
        MsgDSpec { f1: self.f1.deep_view(), f2: self.f2.deep_view(), c: self.c.deep_view() }
    }
}

# [doc = "data type for `msg_b`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct MsgB {
    pub f1: MsgD,
}

# [verifier::ext_equal]
pub struct MsgBSpec {
    pub f1: MsgDSpec,
}

pub type MsgBInner = MsgDSpec;

impl DeepView for MsgB {
    type V = MsgBSpec;

    open spec fn deep_view(&self) -> Self::V {
        MsgBSpec { f1: self.f1.deep_view() }
    }
}

# [doc = "data type for `msg_a`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct MsgA<'i> {
    pub f1: MsgB,
    pub f2: &'i [u8],
}

# [verifier::ext_equal]
pub struct MsgASpec {
    pub f1: MsgBSpec,
    pub f2: Seq<u8>,
}

pub type MsgAInner = (MsgBSpec, Seq<u8>);

impl<'i> DeepView for MsgA<'i> {
    type V = MsgASpec;

    open spec fn deep_view(&self) -> Self::V {
        MsgASpec { f1: self.f1.deep_view(), f2: self.f2.deep_view() }
    }
}

# [doc = "data type for `content_type`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum ContentType {
    C0 = 0,
    C1 = 1,
    C2 = 2,
    Unknown(u8),
}

pub type ContentTypeSpec = ContentType;

pub type ContentTypeInner = Sum<u8, u8>;

impl DeepView for ContentType {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [cfg (not (verus_keep_ghost))]
unsafe impl Structural for ContentType {

}

# [doc = "data type for `msg_c`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct MsgC<'i> {
    pub f2: ContentType,
    pub f3: u32,
    pub f4: MsgCF4<'i>,
}

# [verifier::ext_equal]
pub struct MsgCSpec {
    pub f2: ContentTypeSpec,
    pub f3: u32,
    pub f4: MsgCF4Spec,
}

pub type MsgCInner = (ContentTypeSpec, (u32, MsgCF4Spec));

impl<'i> DeepView for MsgC<'i> {
    type V = MsgCSpec;

    open spec fn deep_view(&self) -> Self::V {
        MsgCSpec { f2: self.f2.deep_view(), f3: self.f3.deep_view(), f4: self.f4.deep_view() }
    }
}

# [doc = "data type for `content_0`."]
pub type Content0<'i> = &'i [u8];

pub type Content0Spec = Seq<u8>;

# [doc = "data type for `msg_c_f4`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum MsgCF4<'i> {
    C0(Content0<'i>),
    C1(u16),
    C2(u32),
    Default(&'i [u8]),
}

# [verifier::ext_equal]
pub enum MsgCF4Spec {
    C0(Content0Spec),
    C1(u16),
    C2(u32),
    Default(Seq<u8>),
}

pub type MsgCF4Inner = Sum<Content0Spec, Sum<u16, Sum<u32, Seq<u8>>>>;

impl<'i> DeepView for MsgCF4<'i> {
    type V = MsgCF4Spec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            MsgCF4::C0(v) => MsgCF4Spec::C0(v.deep_view()),
            MsgCF4::C1(v) => MsgCF4Spec::C1(v.deep_view()),
            MsgCF4::C2(v) => MsgCF4Spec::C2(v.deep_view()),
            MsgCF4::Default(v) => MsgCF4Spec::Default(v.deep_view()),
        }
    }
}

// ============================================================
// Format Specifications
// ============================================================
// TODO(specs): emit const-format spec wrappers for F5
# [doc = "named format combinator for `msg_d`."]
# [derive (Clone, Copy)]
pub struct MsgDFmt;

pub type MsgDFmtSpec = Named<
    Mapped<
        Pair<Const<Fixed<4>, [u8; 4]>, Pair<Const<U16Be, u16>, Const<Fixed<5>, [u8; 5]>>>,
        FnSpecMapper<MsgDInner, MsgDSpec>,
    >,
>;

impl MsgDFmt {
    # [doc = "specification constructor for `msg_d`."]
    pub open spec fn spec_inner() -> MsgDFmtSpec {
        Named(
            "msg_d",
            Mapped {
                inner: Pair(
                    Const(Fixed::<4>, [0x01u8, 0x02u8, 0x03u8, 0x04u8]),
                    Pair(
                        Const(U16Be, 4660),
                        Const(Fixed::<5>, [0x01u8, 0x01u8, 0x01u8, 0x01u8, 0x01u8]),
                    ),
                ),
                mapper: (
                    |parsed: MsgDInner| -> MsgDSpec
                        {
                            let (f1, (f2, c)) = parsed;
                            MsgDSpec { f1, f2, c }
                        },
                    |value: MsgDSpec| -> MsgDInner
                        {
                            let MsgDSpec { f1, f2, c } = value;
                            (f1, (f2, c))
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg_b`."]
# [derive (Clone, Copy)]
pub struct MsgBFmt;

pub type MsgBFmtSpec = Named<Mapped<MsgDFmt, FnSpecMapper<MsgBInner, MsgBSpec>>>;

impl MsgBFmt {
    # [doc = "specification constructor for `msg_b`."]
    pub open spec fn spec_inner() -> MsgBFmtSpec {
        Named(
            "msg_b",
            Mapped {
                inner: MsgDFmt,
                mapper: (
                    |parsed: MsgBInner| -> MsgBSpec
                        {
                            let f1 = parsed;
                            MsgBSpec { f1 }
                        },
                    |value: MsgBSpec| -> MsgBInner
                        {
                            let MsgBSpec { f1 } = value;
                            f1
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg_a`."]
# [derive (Clone, Copy)]
pub struct MsgAFmt;

pub type MsgAFmtSpec = Named<Mapped<Pair<MsgBFmt, Tail>, FnSpecMapper<MsgAInner, MsgASpec>>>;

impl MsgAFmt {
    # [doc = "specification constructor for `msg_a`."]
    pub open spec fn spec_inner() -> MsgAFmtSpec {
        Named(
            "msg_a",
            Mapped {
                inner: Pair(MsgBFmt, Tail),
                mapper: (
                    |parsed: MsgAInner| -> MsgASpec
                        {
                            let (f1, f2) = parsed;
                            MsgASpec { f1, f2 }
                        },
                    |value: MsgASpec| -> MsgAInner
                        {
                            let MsgASpec { f1, f2 } = value;
                            (f1, f2)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `content_type`."]
# [derive (Clone, Copy)]
pub struct ContentTypeFmt;

pub type ContentTypeFmtSpec = Named<
    Mapped<
        Choice<Refined<U8, PredFnSpec<u8>>, Refined<U8, PredFnSpec<u8>>>,
        FnSpecMapper<ContentTypeInner, ContentTypeSpec>,
    >,
>;

impl ContentTypeFmt {
    # [doc = "specification constructor for `content_type`."]
    pub open spec fn spec_inner() -> ContentTypeFmtSpec {
        Named(
            "content_type",
            Mapped {
                inner: Choice(
                    Refined(U8, |x: u8| ((x == 0) || (x == 1)) || (x == 2)),
                    Refined(U8, |x: u8| ((x != 0) && (x != 1)) && (x != 2)),
                ),
                mapper: (
                    |parsed: ContentTypeInner| -> ContentTypeSpec
                        {
                            match parsed {
                                L(x) => match x {
                                    0 => ContentTypeSpec::C0,
                                    1 => ContentTypeSpec::C1,
                                    2 => ContentTypeSpec::C2,
                                    _ => arbitrary(),
                                },
                                R(x) => ContentTypeSpec::Unknown(x),
                            }
                        },
                    |value: ContentTypeSpec| -> ContentTypeInner
                        {
                            match value {
                                ContentTypeSpec::C0 => L(0),
                                ContentTypeSpec::C1 => L(1),
                                ContentTypeSpec::C2 => L(2),
                                ContentTypeSpec::Unknown(x) => R(x),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg_c`."]
# [derive (Clone, Copy)]
pub struct MsgCFmt;

pub type MsgCFmtSpec = Named<
    Mapped<
        Bind<
            ContentTypeFmt,
            spec_fn(ContentTypeSpec) -> Bind<U24Be, spec_fn(u32) -> ExactLen<MsgCF4Fmt, u32>>,
        >,
        FnSpecMapper<MsgCInner, MsgCSpec>,
    >,
>;

impl MsgCFmt {
    # [doc = "specification constructor for `msg_c`."]
    pub open spec fn spec_inner() -> MsgCFmtSpec {
        Named(
            "msg_c",
            Mapped {
                inner: Bind(
                    ContentTypeFmt,
                    |f2: ContentTypeSpec|
                        Bind(U24Be, |f3: u32| ExactLen(f3, MsgCF4Fmt::spec(f2, f3))),
                ),
                mapper: (
                    |parsed: MsgCInner| -> MsgCSpec
                        {
                            let (f2, (f3, f4)) = parsed;
                            MsgCSpec { f2, f3, f4 }
                        },
                    |value: MsgCSpec| -> MsgCInner
                        {
                            let MsgCSpec { f2, f3, f4 } = value;
                            (f2, (f3, f4))
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `content_0`."]
# [derive (Clone, Copy)]
pub struct Content0Fmt {
    num: u32,
}

impl Content0Fmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn num_spec(&self) -> u32 {
        self.num.deep_view()
    }

    pub closed spec fn spec(num: u32) -> Self {
        Content0Fmt { num }
    }
}

pub type Content0FmtSpec = Named<Varied<u32>>;

impl Content0Fmt {
    # [doc = "specification constructor for `content_0`."]
    pub open spec fn spec_inner(num: u32) -> Content0FmtSpec {
        Named("content_0", Varied(num))
    }
}

# [doc = "named format combinator for `msg_c_f4`."]
# [derive (Clone, Copy)]
pub struct MsgCF4Fmt {
    f2: ContentType,
    f3: u32,
}

impl MsgCF4Fmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        ContentTypeFmt.consistent(self.f2.deep_view())
    }

    pub closed spec fn f2_spec(&self) -> ContentTypeSpec {
        self.f2.deep_view()
    }

    pub closed spec fn f3_spec(&self) -> u32 {
        self.f3.deep_view()
    }

    pub closed spec fn spec(f2: ContentType, f3: u32) -> Self {
        MsgCF4Fmt { f2, f3 }
    }
}

pub type MsgCF4FmtSpec = Named<
    Mapped<Sum<Content0Fmt, Sum<U16Be, Sum<U32Be, Tail>>>, FnSpecMapper<MsgCF4Inner, MsgCF4Spec>>,
>;

impl MsgCF4Fmt {
    # [doc = "specification constructor for `msg_c_f4`."]
    pub open spec fn spec_inner(f2: ContentTypeSpec, f3: u32) -> MsgCF4FmtSpec {
        Named(
            "msg_c_f4",
            Mapped {
                inner: match f2 {
                    ContentTypeSpec::C0 => L(Content0Fmt::spec(f3)),
                    ContentTypeSpec::C1 => R(L(U16Be)),
                    ContentTypeSpec::C2 => R(R(L(U32Be))),
                    _ => R(R(R(Tail))),
                },
                mapper: (
                    |parsed: MsgCF4Inner| -> MsgCF4Spec
                        {
                            match parsed {
                                L(v) => MsgCF4Spec::C0(v),
                                R(L(v)) => MsgCF4Spec::C1(v),
                                R(R(L(v))) => MsgCF4Spec::C2(v),
                                R(R(R(v))) => MsgCF4Spec::Default(v),
                            }
                        },
                    |value: MsgCF4Spec| -> MsgCF4Inner
                        {
                            match value {
                                MsgCF4Spec::C0(v) => L(v),
                                MsgCF4Spec::C1(v) => R(L(v)),
                                MsgCF4Spec::C2(v) => R(R(L(v))),
                                MsgCF4Spec::Default(v) => R(R(R(v))),
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

    // TODO(derived-specs): emit const-format trait wrappers for F5
    impl SpecParser for MsgDFmt {
        type PVal = MsgDSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MsgDFmt {
        type Val = MsgDSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MsgDFmt {
        type SValue = MsgDSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgDFmt {
        type SVal = MsgDSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgDFmt {
        type T = MsgDSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for MsgBFmt {
        type PVal = MsgBSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MsgBFmt {
        type Val = MsgBSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MsgBFmt {
        type SValue = MsgBSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgBFmt {
        type SVal = MsgBSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgBFmt {
        type T = MsgBSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for MsgAFmt {
        type PVal = MsgASpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MsgAFmt {
        type Val = MsgASpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MsgAFmt {
        type SValue = MsgASpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgAFmt {
        type SVal = MsgASpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgAFmt {
        type T = MsgASpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ContentTypeFmt {
        type PVal = ContentTypeSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ContentTypeFmt {
        type Val = ContentTypeSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ContentTypeFmt {
        type SValue = ContentTypeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ContentTypeFmt {
        type SVal = ContentTypeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ContentTypeFmt {
        type T = ContentTypeSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for MsgCFmt {
        type PVal = MsgCSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MsgCFmt {
        type Val = MsgCSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MsgCFmt {
        type SValue = MsgCSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgCFmt {
        type SVal = MsgCSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgCFmt {
        type T = MsgCSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Content0Fmt {
        type PVal = Content0Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.num_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for Content0Fmt {
        type Val = Content0Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.num_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for Content0Fmt {
        type SValue = Content0Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.num_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Content0Fmt {
        type SVal = Content0Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.num_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for Content0Fmt {
        type T = Content0Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.num_spec()).byte_len(v)
        }
    }

    impl SpecParser for MsgCF4Fmt {
        type PVal = MsgCF4Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.f2_spec(), self.f3_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for MsgCF4Fmt {
        type Val = MsgCF4Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.f2_spec(), self.f3_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for MsgCF4Fmt {
        type SValue = MsgCF4Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.f2_spec(), self.f3_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgCF4Fmt {
        type SVal = MsgCF4Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.f2_spec(), self.f3_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgCF4Fmt {
        type T = MsgCF4Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.f2_spec(), self.f3_spec()).byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;
    // TODO(proofs): emit const-format proof wrappers for F5

    impl SafeParser for MsgDFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgDFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgDFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgDFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgDFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgDFmt as SpecParser>::spec_parse);
            reveal(<MsgDFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgDFmt as SpecParser>::spec_parse);
            reveal(<MsgDFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MsgDFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgDFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgDFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgDFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MsgDFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgDFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgDFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgDFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgDFmt as SpecParser>::spec_parse);
            reveal(<MsgDFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgDFmt as Consistency>::consistent);
            reveal(<MsgDFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgDFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgDFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MsgDFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MsgDFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgDFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MsgDFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgDFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgDFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MsgBFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgBFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgBFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgBFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgBFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgBFmt as SpecParser>::spec_parse);
            reveal(<MsgBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgBFmt as SpecParser>::spec_parse);
            reveal(<MsgBFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MsgBFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgBFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MsgBFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgBFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgBFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgBFmt as SpecParser>::spec_parse);
            reveal(<MsgBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgBFmt as Consistency>::consistent);
            reveal(<MsgBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgBFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgBFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MsgBFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MsgBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgBFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MsgBFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgBFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MsgAFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgAFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgAFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgAFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgAFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgAFmt as SpecParser>::spec_parse);
            reveal(<MsgAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgAFmt as SpecParser>::spec_parse);
            reveal(<MsgAFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for MsgAFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgAFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgAFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgAFmt as SpecParser>::spec_parse);
            reveal(<MsgAFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgAFmt as Consistency>::consistent);
            reveal(<MsgAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgAFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgAFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for MsgAFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgAFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgAFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ContentTypeFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ContentTypeFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ContentTypeFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ContentTypeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ContentTypeFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ContentTypeFmt as SpecParser>::spec_parse);
            reveal(<ContentTypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ContentTypeFmt as SpecParser>::spec_parse);
            reveal(<ContentTypeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ContentTypeFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ContentTypeFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ContentTypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ContentTypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ContentTypeFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ContentTypeFmt as SpecSerializer>::spec_serialize);
            reveal(<ContentTypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ContentTypeFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ContentTypeFmt as SpecParser>::spec_parse);
            reveal(<ContentTypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ContentTypeFmt as Consistency>::consistent);
            reveal(<ContentTypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ContentTypeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ContentTypeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ContentTypeFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ContentTypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ContentTypeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ContentTypeFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ContentTypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ContentTypeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MsgCFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgCFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgCFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgCFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgCFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgCFmt as SpecParser>::spec_parse);
            reveal(<MsgCFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgCFmt as SpecParser>::spec_parse);
            reveal(<MsgCFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MsgCFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgCFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgCFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgCFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MsgCFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgCFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgCFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgCFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgCFmt as SpecParser>::spec_parse);
            reveal(<MsgCFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgCFmt as Consistency>::consistent);
            reveal(<MsgCFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgCFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgCFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MsgCFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MsgCFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgCFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MsgCFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgCFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgCFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Content0Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Content0Fmt as SpecParser>::spec_parse);
            Self::spec_inner(self.num_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Content0Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.num_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Content0Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.num_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Content0Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Content0Fmt as SpecParser>::spec_parse);
            reveal(<Content0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.num_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Content0Fmt as SpecParser>::spec_parse);
            reveal(<Content0Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.num_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Content0Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Content0Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.num_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Content0Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Content0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.num_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Content0Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Content0Fmt as SpecSerializer>::spec_serialize);
            reveal(<Content0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.num_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Content0Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Content0Fmt as SpecParser>::spec_parse);
            reveal(<Content0Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Content0Fmt as Consistency>::consistent);
            reveal(<Content0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.num_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Content0Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Content0Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.num_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Content0Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Content0Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Content0Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.num_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Content0Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Content0Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Content0Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.num_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MsgCF4Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgCF4Fmt as SpecParser>::spec_parse);
            Self::spec_inner(self.f2_spec(), self.f3_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgCF4Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.f2_spec(), self.f3_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgCF4Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.f2_spec(), self.f3_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgCF4Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgCF4Fmt as SpecParser>::spec_parse);
            reveal(<MsgCF4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.f2_spec(), self.f3_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgCF4Fmt as SpecParser>::spec_parse);
            reveal(<MsgCF4Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.f2_spec(), self.f3_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for MsgCF4Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgCF4Fmt as SpecSerializer>::spec_serialize);
            reveal(<MsgCF4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.f2_spec(), self.f3_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgCF4Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgCF4Fmt as SpecParser>::spec_parse);
            reveal(<MsgCF4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgCF4Fmt as Consistency>::consistent);
            reveal(<MsgCF4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.f2_spec(), self.f3_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgCF4Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgCF4Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.f2_spec(), self.f3_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for MsgCF4Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgCF4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgCF4Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.f2_spec(), self.f3_spec());
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

    // TODO(execs): emit const-format exec wrappers for F5
    impl<'i> Parser<&'i [u8]> for MsgDFmt {
        type PT = MsgD;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MsgDFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, f1) = Const(Fixed::<4>, [0x01, 0x02, 0x03, 0x04]).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, f2) = Const(U16Be, 4660).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, c) = Const(Fixed::<5>, [0x01, 0x01, 0x01, 0x01, 0x01]).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = MsgD { f1, f2, c };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, MsgD> for MsgDFmt {
        fn serialize_into(&self, v: &MsgD, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<MsgDFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgDFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let MsgD { f1, f2, c } = v;
            Fixed::<4>.serialize_into(f1, obuf);
            U16Be.serialize_into(f2, obuf);
            Fixed::<5>.serialize_into(c, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MsgD> for MsgDFmt {
        fn prepare(&self, v: &MsgD) -> Result<usize, PreSerializeError> {
            reveal(<MsgDFmt as SpecByteLen>::byte_len);
            let MsgD { f1, f2, c } = v;
            let l1 = (Const(Fixed::<4>, [0x01, 0x02, 0x03, 0x04])).prepare(f1)?;
            let l2 = (Const(U16Be, 4660)).prepare(f2)?;
            let l3 = (Const(Fixed::<5>, [0x01, 0x01, 0x01, 0x01, 0x01])).prepare(c)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for MsgBFmt {
        type PT = MsgB;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MsgBFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, f1) = (Named("msg_d", MsgDFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = MsgB { f1 };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, MsgB> for MsgBFmt {
        fn serialize_into(&self, v: &MsgB, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<MsgBFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgBFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let MsgB { f1 } = v;
            MsgDFmt.serialize_into(f1, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MsgB> for MsgBFmt {
        fn prepare(&self, v: &MsgB) -> Result<usize, PreSerializeError> {
            reveal(<MsgBFmt as SpecByteLen>::byte_len);
            let MsgB { f1 } = v;
            let l1 = (Named("msg_d", MsgDFmt)).prepare(f1)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for MsgAFmt {
        type PT = MsgA<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MsgAFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, f1) = (Named("msg_b", MsgBFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, f2) = (Tail).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = MsgA { f1, f2 };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, MsgA<'i>> for MsgAFmt {
        fn serialize_into(&self, v: &MsgA<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<MsgAFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgAFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let MsgA { f1, f2 } = v;
            MsgBFmt.serialize_into(f1, obuf);
            Tail.serialize_into(f2, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MsgA<'i>> for MsgAFmt {
        fn prepare(&self, v: &MsgA<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MsgAFmt as SpecByteLen>::byte_len);
            let MsgA { f1, f2 } = v;
            let l1 = (Named("msg_b", MsgBFmt)).prepare(f1)?;
            let l2 = (Tail).prepare(f2)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for ContentTypeFmt {
        type PT = ContentType;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ContentTypeFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                0 => ContentType::C0,
                1 => ContentType::C1,
                2 => ContentType::C2,
                x => ContentType::Unknown(x),
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
            Ok((n, enum_val))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ContentType> for ContentTypeFmt {
        fn serialize_into(&self, v: &ContentType, obuf: &mut Output) {
            reveal(<ContentTypeFmt as SpecSerializer>::spec_serialize);
            reveal(<ContentTypeFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                ContentType::C0 => 0,
                ContentType::C1 => 1,
                ContentType::C2 => 2,
                ContentType::Unknown(x) => x,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ContentType> for ContentTypeFmt {
        fn prepare(&self, v: &ContentType) -> Result<usize, PreSerializeError> {
            reveal(<ContentTypeFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                ContentType::C0 => 0,
                ContentType::C1 => 1,
                ContentType::C2 => 2,
                ContentType::Unknown(x) if x != 0 && x != 1 && x != 2 => x,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for MsgCFmt {
        type PT = MsgC<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MsgCFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, f2) = (Named("content_type", ContentTypeFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, f3) = (U24Be).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, f4) = (ExactLen(f3, Named("msg_c_f4", MsgCF4Fmt { f2: f2, f3: f3 }))).parse(
                &rest,
            )?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = MsgC { f2, f3, f4 };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, MsgC<'i>> for MsgCFmt {
        fn serialize_into(&self, v: &MsgC<'i>, obuf: &mut Output) {
            broadcast use vest_lib2::core::exec::output::outbuf_lemmas;

            reveal(<MsgCFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgCFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            let MsgC { f2, f3, f4 } = v;
            ContentTypeFmt.serialize_into(f2, obuf);
            U24Be.serialize_into(f3, obuf);
            ExactLen(*f3, MsgCF4Fmt { f2: *f2, f3: *f3 }).serialize_into(f4, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MsgC<'i>> for MsgCFmt {
        fn prepare(&self, v: &MsgC<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MsgCFmt as SpecByteLen>::byte_len);
            let MsgC { f2, f3, f4 } = v;
            let l1 = (Named("content_type", ContentTypeFmt)).prepare(f2)?;
            let l2 = (U24Be).prepare(f3)?;
            let l3 = (ExactLen(*f3, Named("msg_c_f4", MsgCF4Fmt { f2: *f2, f3: *f3 }))).prepare(
                f4,
            )?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for Content0Fmt {
        type PT = Content0<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<Content0Fmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = Varied(self.num).parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Content0<'i>> for Content0Fmt {
        fn serialize_into(&self, v: &Content0<'i>, obuf: &mut Output) {
            reveal(<Content0Fmt as SpecSerializer>::spec_serialize);
            reveal(<Content0Fmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            Varied(self.num).serialize_into(*v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Content0<'i>> for Content0Fmt {
        fn prepare(&self, v: &Content0<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Content0Fmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            (Varied(self.num)).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for MsgCF4Fmt {
        type PT = MsgCF4<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<MsgCF4Fmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.f2 {
                ContentType::C0 => {
                    let (n, v) = (Named("content_0", Content0Fmt { num: self.f3 })).parse(&rest)?;
                    (n, MsgCF4::C0(v))
                },
                ContentType::C1 => {
                    let (n, v) = (U16Be).parse(&rest)?;
                    (n, MsgCF4::C1(v))
                },
                ContentType::C2 => {
                    let (n, v) = (U32Be).parse(&rest)?;
                    (n, MsgCF4::C2(v))
                },
                _ => {
                    let (n, v) = (Tail).parse(&rest)?;
                    (n, MsgCF4::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, MsgCF4<'i>> for MsgCF4Fmt {
        fn serialize_into(&self, v: &MsgCF4<'i>, obuf: &mut Output) {
            reveal(<MsgCF4Fmt as SpecSerializer>::spec_serialize);
            reveal(<MsgCF4Fmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.f2, v) {
                (ContentType::C0, MsgCF4::C0(v)) => {
                    (Content0Fmt { num: self.f3 }).serialize_into(v, obuf);
                },
                (ContentType::C1, MsgCF4::C1(v)) => {
                    (U16Be).serialize_into(v, obuf);
                },
                (ContentType::C2, MsgCF4::C2(v)) => {
                    (U32Be).serialize_into(v, obuf);
                },
                (_, MsgCF4::Default(v)) => {
                    (Tail).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MsgCF4<'i>> for MsgCF4Fmt {
        fn prepare(&self, v: &MsgCF4<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MsgCF4Fmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.f2, v) {
                (ContentType::C0, MsgCF4::C0(v)) => (Named(
                    "content_0",
                    Content0Fmt { num: self.f3 },
                )).prepare(v),
                (ContentType::C1, MsgCF4::C1(v)) => (U16Be).prepare(v),
                (ContentType::C2, MsgCF4::C2(v)) => (U32Be).prepare(v),
                (ContentType::Unknown(x), MsgCF4::Default(v)) if x != 0 && x != 1 && x != 2 => (
                Tail).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}

} // verus!
