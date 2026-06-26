#![allow(warnings)]
use vest_lib2::combinators::mapped::spec::*;
use vest_lib2::combinators::recursive::*;
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
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct Msg1Spec {
    pub a: u8,
    pub b: u16,
    pub c: Seq<u8>,
    pub data: Seq<u8>,
}

pub type Msg1Inner = (u8, (u16, (Seq<u8>, Seq<u8>)));

impl<'i> DeepView for Msg1<'i> {
    type V = Msg1Spec;

    open spec fn deep_view(&self) -> Self::V {
        Msg1Spec {
            a: self.a.deep_view(),
            b: self.b.deep_view(),
            c: self.c.deep_view(),
            data: self.data.deep_view(),
        }
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

# [doc = "data type for `msg3`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg3<'i> {
    pub data: &'i [u8],
}

# [verifier::ext_equal]
pub struct Msg3Spec {
    pub data: Seq<u8>,
}

pub type Msg3Inner = Seq<u8>;

impl<'i> DeepView for Msg3<'i> {
    type V = Msg3Spec;

    open spec fn deep_view(&self) -> Self::V {
        Msg3Spec { data: self.data.deep_view() }
    }
}

# [doc = "data type for `msg_type`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, Structural)]
pub enum MsgType {
    Msg1 = 1,
    Msg2 = 2,
    Msg3 = 3,
}

pub type MsgTypeSpec = MsgType;

pub type MsgTypeInner = u8;

impl DeepView for MsgType {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl DeepEq for MsgType {
    fn deep_eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

impl SelfView for MsgType {
    proof fn self_view(&self) {
    }

    fn eq(&self, other: &Self) -> bool {
        *self == *other
    }
}

# [doc = "data type for `msg`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg<'i> {
    pub tag: MsgType,
    pub len: u16,
    pub content: MsgContent<'i>,
}

# [verifier::ext_equal]
pub struct MsgSpec {
    pub tag: MsgTypeSpec,
    pub len: u16,
    pub content: MsgContentSpec,
}

pub type MsgInner = (MsgTypeSpec, (u16, MsgContentSpec));

impl<'i> DeepView for Msg<'i> {
    type V = MsgSpec;

    open spec fn deep_view(&self) -> Self::V {
        MsgSpec {
            tag: self.tag.deep_view(),
            len: self.len.deep_view(),
            content: self.content.deep_view(),
        }
    }
}

# [doc = "data type for `msg_param`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum MsgParam<'i> {
    Msg1(Msg1<'i>),
    Msg2(Msg2),
    Msg3(Msg3<'i>),
}

# [verifier::ext_equal]
pub enum MsgParamSpec {
    Msg1(Msg1Spec),
    Msg2(Msg2Spec),
    Msg3(Msg3Spec),
}

pub type MsgParamInner = Sum<Msg1Spec, Sum<Msg2Spec, Msg3Spec>>;

impl<'i> DeepView for MsgParam<'i> {
    type V = MsgParamSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            MsgParam::Msg1(v) => MsgParamSpec::Msg1(v.deep_view()),
            MsgParam::Msg2(v) => MsgParamSpec::Msg2(v.deep_view()),
            MsgParam::Msg3(v) => MsgParamSpec::Msg3(v.deep_view()),
        }
    }
}

# [doc = "data type for `msg_alt`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct MsgAlt<'i> {
    pub tag: u8,
    pub len: u16,
    pub content: MsgAltContent<'i>,
}

# [verifier::ext_equal]
pub struct MsgAltSpec {
    pub tag: u8,
    pub len: u16,
    pub content: MsgAltContentSpec,
}

pub type MsgAltInner = (u8, (u16, MsgAltContentSpec));

impl<'i> DeepView for MsgAlt<'i> {
    type V = MsgAltSpec;

    open spec fn deep_view(&self) -> Self::V {
        MsgAltSpec {
            tag: self.tag.deep_view(),
            len: self.len.deep_view(),
            content: self.content.deep_view(),
        }
    }
}

# [doc = "data type for `msg_content`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum MsgContent<'i> {
    Msg1(Msg1<'i>),
    Msg2(Msg2),
    Msg3(Msg3<'i>),
}

# [verifier::ext_equal]
pub enum MsgContentSpec {
    Msg1(Msg1Spec),
    Msg2(Msg2Spec),
    Msg3(Msg3Spec),
}

pub type MsgContentInner = Sum<Msg1Spec, Sum<Msg2Spec, Msg3Spec>>;

impl<'i> DeepView for MsgContent<'i> {
    type V = MsgContentSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            MsgContent::Msg1(v) => MsgContentSpec::Msg1(v.deep_view()),
            MsgContent::Msg2(v) => MsgContentSpec::Msg2(v.deep_view()),
            MsgContent::Msg3(v) => MsgContentSpec::Msg3(v.deep_view()),
        }
    }
}

# [doc = "data type for `msg_alt_content`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum MsgAltContent<'i> {
    Variant1(Msg1<'i>),
    Variant2(Msg2),
    Variant3(Msg3<'i>),
    Default(&'i [u8]),
}

# [verifier::ext_equal]
pub enum MsgAltContentSpec {
    Variant1(Msg1Spec),
    Variant2(Msg2Spec),
    Variant3(Msg3Spec),
    Default(Seq<u8>),
}

pub type MsgAltContentInner = Sum<Msg1Spec, Sum<Msg2Spec, Sum<Msg3Spec, Seq<u8>>>>;

impl<'i> DeepView for MsgAltContent<'i> {
    type V = MsgAltContentSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            MsgAltContent::Variant1(v) => MsgAltContentSpec::Variant1(v.deep_view()),
            MsgAltContent::Variant2(v) => MsgAltContentSpec::Variant2(v.deep_view()),
            MsgAltContent::Variant3(v) => MsgAltContentSpec::Variant3(v.deep_view()),
            MsgAltContent::Default(v) => MsgAltContentSpec::Default(v.deep_view()),
        }
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `msg1`."]
# [derive (Clone, Copy)]
pub struct Msg1Fmt;

pub type Msg1FmtSpec = Named<
    Mapped<Pair<U8, Pair<U16Le, Pair<Fixed<3>, Tail>>>, FnSpecMapper<Msg1Inner, Msg1Spec>>,
>;

impl Msg1Fmt {
    # [doc = "specification constructor for `msg1`."]
    pub open spec fn spec_inner() -> Msg1FmtSpec {
        Named(
            "msg1",
            Mapped {
                inner: Pair(U8, Pair(U16Le, Pair(Fixed::<3>, Tail))),
                mapper: (
                    |parsed: Msg1Inner| -> Msg1Spec
                        {
                            let (a, (b, (c, data))) = parsed;
                            Msg1Spec { a, b, c, data }
                        },
                    |value: Msg1Spec| -> Msg1Inner
                        {
                            let Msg1Spec { a, b, c, data } = value;
                            (a, (b, (c, data)))
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

# [doc = "named format combinator for `msg3`."]
# [derive (Clone, Copy)]
pub struct Msg3Fmt;

pub type Msg3FmtSpec = Named<Mapped<Fixed<6>, FnSpecMapper<Msg3Inner, Msg3Spec>>>;

impl Msg3Fmt {
    # [doc = "specification constructor for `msg3`."]
    pub open spec fn spec_inner() -> Msg3FmtSpec {
        Named(
            "msg3",
            Mapped {
                inner: Fixed::<6>,
                mapper: (
                    |parsed: Msg3Inner| -> Msg3Spec
                        {
                            let data = parsed;
                            Msg3Spec { data }
                        },
                    |value: Msg3Spec| -> Msg3Inner
                        {
                            let Msg3Spec { data } = value;
                            data
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg_type`."]
# [derive (Clone, Copy)]
pub struct MsgTypeFmt;

pub type MsgTypeFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<MsgTypeInner, MsgTypeSpec>>,
>;

impl MsgTypeFmt {
    # [doc = "specification constructor for `msg_type`."]
    pub open spec fn spec_inner() -> MsgTypeFmtSpec {
        Named(
            "msg_type",
            Mapped {
                inner: Refined(U8, |x: u8| ((x == 1) || (x == 2)) || (x == 3)),
                mapper: (
                    |parsed: MsgTypeInner| -> MsgTypeSpec
                        {
                            match parsed {
                                1 => MsgTypeSpec::Msg1,
                                2 => MsgTypeSpec::Msg2,
                                3 => MsgTypeSpec::Msg3,
                                _ => arbitrary(),
                            }
                        },
                    |value: MsgTypeSpec| -> MsgTypeInner
                        {
                            match value {
                                MsgTypeSpec::Msg1 => 1,
                                MsgTypeSpec::Msg2 => 2,
                                MsgTypeSpec::Msg3 => 3,
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg`."]
# [derive (Clone, Copy)]
pub struct MsgFmt;

pub type MsgFmtSpec = Named<
    Mapped<
        Bind<
            MsgTypeFmt,
            spec_fn(MsgTypeSpec) -> Bind<U16Le, spec_fn(u16) -> ExactLen<MsgContentFmt, u16>>,
        >,
        FnSpecMapper<MsgInner, MsgSpec>,
    >,
>;

impl MsgFmt {
    # [doc = "specification constructor for `msg`."]
    pub open spec fn spec_inner() -> MsgFmtSpec {
        Named(
            "msg",
            Mapped {
                inner: Bind(
                    MsgTypeFmt,
                    |tag: MsgTypeSpec|
                        Bind(U16Le, |len: u16| ExactLen(len, MsgContentFmt::spec(tag))),
                ),
                mapper: (
                    |parsed: MsgInner| -> MsgSpec
                        {
                            let (tag, (len, content)) = parsed;
                            MsgSpec { tag, len, content }
                        },
                    |value: MsgSpec| -> MsgInner
                        {
                            let MsgSpec { tag, len, content } = value;
                            (tag, (len, content))
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg_param`."]
# [derive (Clone, Copy)]
pub struct MsgParamFmt {
    tag: MsgType,
}

impl MsgParamFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        MsgTypeFmt.consistent(self.tag.deep_view())
    }

    pub closed spec fn tag_spec(&self) -> MsgTypeSpec {
        self.tag.deep_view()
    }

    pub closed spec fn spec(tag: MsgType) -> Self {
        MsgParamFmt { tag }
    }
}

pub type MsgParamFmtSpec = Named<
    Mapped<Sum<Msg1Fmt, Sum<Msg2Fmt, Msg3Fmt>>, FnSpecMapper<MsgParamInner, MsgParamSpec>>,
>;

impl MsgParamFmt {
    # [doc = "specification constructor for `msg_param`."]
    pub open spec fn spec_inner(tag: MsgTypeSpec) -> MsgParamFmtSpec {
        Named(
            "msg_param",
            Mapped {
                inner: match tag {
                    MsgTypeSpec::Msg1 => L(Msg1Fmt),
                    MsgTypeSpec::Msg2 => R(L(Msg2Fmt)),
                    MsgTypeSpec::Msg3 => R(R(Msg3Fmt)),
                },
                mapper: (
                    |parsed: MsgParamInner| -> MsgParamSpec
                        {
                            match parsed {
                                L(v) => MsgParamSpec::Msg1(v),
                                R(L(v)) => MsgParamSpec::Msg2(v),
                                R(R(v)) => MsgParamSpec::Msg3(v),
                            }
                        },
                    |value: MsgParamSpec| -> MsgParamInner
                        {
                            match value {
                                MsgParamSpec::Msg1(v) => L(v),
                                MsgParamSpec::Msg2(v) => R(L(v)),
                                MsgParamSpec::Msg3(v) => R(R(v)),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg_alt`."]
# [derive (Clone, Copy)]
pub struct MsgAltFmt;

pub type MsgAltFmtSpec = Named<
    Mapped<
        Bind<U8, spec_fn(u8) -> Bind<U16Le, spec_fn(u16) -> ExactLen<MsgAltContentFmt, u16>>>,
        FnSpecMapper<MsgAltInner, MsgAltSpec>,
    >,
>;

impl MsgAltFmt {
    # [doc = "specification constructor for `msg_alt`."]
    pub open spec fn spec_inner() -> MsgAltFmtSpec {
        Named(
            "msg_alt",
            Mapped {
                inner: Bind(
                    U8,
                    |tag: u8|
                        Bind(U16Le, |len: u16| ExactLen(len, MsgAltContentFmt::spec(len, tag))),
                ),
                mapper: (
                    |parsed: MsgAltInner| -> MsgAltSpec
                        {
                            let (tag, (len, content)) = parsed;
                            MsgAltSpec { tag, len, content }
                        },
                    |value: MsgAltSpec| -> MsgAltInner
                        {
                            let MsgAltSpec { tag, len, content } = value;
                            (tag, (len, content))
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg_content`."]
# [derive (Clone, Copy)]
pub struct MsgContentFmt {
    tag: MsgType,
}

impl MsgContentFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        MsgTypeFmt.consistent(self.tag.deep_view())
    }

    pub closed spec fn tag_spec(&self) -> MsgTypeSpec {
        self.tag.deep_view()
    }

    pub closed spec fn spec(tag: MsgType) -> Self {
        MsgContentFmt { tag }
    }
}

pub type MsgContentFmtSpec = Named<
    Mapped<Sum<Msg1Fmt, Sum<Msg2Fmt, Msg3Fmt>>, FnSpecMapper<MsgContentInner, MsgContentSpec>>,
>;

impl MsgContentFmt {
    # [doc = "specification constructor for `msg_content`."]
    pub open spec fn spec_inner(tag: MsgTypeSpec) -> MsgContentFmtSpec {
        Named(
            "msg_content",
            Mapped {
                inner: match tag {
                    MsgTypeSpec::Msg1 => L(Msg1Fmt),
                    MsgTypeSpec::Msg2 => R(L(Msg2Fmt)),
                    MsgTypeSpec::Msg3 => R(R(Msg3Fmt)),
                },
                mapper: (
                    |parsed: MsgContentInner| -> MsgContentSpec
                        {
                            match parsed {
                                L(v) => MsgContentSpec::Msg1(v),
                                R(L(v)) => MsgContentSpec::Msg2(v),
                                R(R(v)) => MsgContentSpec::Msg3(v),
                            }
                        },
                    |value: MsgContentSpec| -> MsgContentInner
                        {
                            match value {
                                MsgContentSpec::Msg1(v) => L(v),
                                MsgContentSpec::Msg2(v) => R(L(v)),
                                MsgContentSpec::Msg3(v) => R(R(v)),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `msg_alt_content`."]
# [derive (Clone, Copy)]
pub struct MsgAltContentFmt {
    len: u16,
    tag: u8,
}

impl MsgAltContentFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn len_spec(&self) -> u16 {
        self.len.deep_view()
    }

    pub closed spec fn tag_spec(&self) -> u8 {
        self.tag.deep_view()
    }

    pub closed spec fn spec(len: u16, tag: u8) -> Self {
        MsgAltContentFmt { len, tag }
    }
}

pub type MsgAltContentFmtSpec = Named<
    Mapped<
        Sum<Msg1Fmt, Sum<Msg2Fmt, Sum<Msg3Fmt, Varied<u16>>>>,
        FnSpecMapper<MsgAltContentInner, MsgAltContentSpec>,
    >,
>;

impl MsgAltContentFmt {
    # [doc = "specification constructor for `msg_alt_content`."]
    pub open spec fn spec_inner(len: u16, tag: u8) -> MsgAltContentFmtSpec {
        Named(
            "msg_alt_content",
            Mapped {
                inner: match tag {
                    1 => L(Msg1Fmt),
                    2 => R(L(Msg2Fmt)),
                    3 => R(R(L(Msg3Fmt))),
                    _ => R(R(R(Varied(len)))),
                },
                mapper: (
                    |parsed: MsgAltContentInner| -> MsgAltContentSpec
                        {
                            match parsed {
                                L(v) => MsgAltContentSpec::Variant1(v),
                                R(L(v)) => MsgAltContentSpec::Variant2(v),
                                R(R(L(v))) => MsgAltContentSpec::Variant3(v),
                                R(R(R(v))) => MsgAltContentSpec::Default(v),
                            }
                        },
                    |value: MsgAltContentSpec| -> MsgAltContentInner
                        {
                            match value {
                                MsgAltContentSpec::Variant1(v) => L(v),
                                MsgAltContentSpec::Variant2(v) => R(L(v)),
                                MsgAltContentSpec::Variant3(v) => R(R(L(v))),
                                MsgAltContentSpec::Default(v) => R(R(R(v))),
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

    impl SpecParser for Msg1Fmt {
        type PVal = Msg1Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg1Fmt {
        type Val = Msg1Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg1Fmt {
        type SValue = Msg1Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg1Fmt {
        type SVal = Msg1Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg1Fmt {
        type T = Msg1Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Msg2Fmt {
        type PVal = Msg2Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg2Fmt {
        type Val = Msg2Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg2Fmt {
        type SValue = Msg2Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg2Fmt {
        type SVal = Msg2Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg2Fmt {
        type T = Msg2Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Msg3Fmt {
        type PVal = Msg3Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg3Fmt {
        type Val = Msg3Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg3Fmt {
        type SValue = Msg3Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg3Fmt {
        type SVal = Msg3Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg3Fmt {
        type T = Msg3Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for MsgTypeFmt {
        type PVal = MsgTypeSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MsgTypeFmt {
        type Val = MsgTypeSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MsgTypeFmt {
        type SValue = MsgTypeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgTypeFmt {
        type SVal = MsgTypeSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgTypeFmt {
        type T = MsgTypeSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for MsgFmt {
        type PVal = MsgSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MsgFmt {
        type Val = MsgSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MsgFmt {
        type SValue = MsgSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgFmt {
        type SVal = MsgSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgFmt {
        type T = MsgSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for MsgParamFmt {
        type PVal = MsgParamSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.tag_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for MsgParamFmt {
        type Val = MsgParamSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.tag_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for MsgParamFmt {
        type SValue = MsgParamSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgParamFmt {
        type SVal = MsgParamSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgParamFmt {
        type T = MsgParamSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.tag_spec()).byte_len(v)
        }
    }

    impl SpecParser for MsgAltFmt {
        type PVal = MsgAltSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for MsgAltFmt {
        type Val = MsgAltSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for MsgAltFmt {
        type SValue = MsgAltSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgAltFmt {
        type SVal = MsgAltSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgAltFmt {
        type T = MsgAltSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for MsgContentFmt {
        type PVal = MsgContentSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.tag_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for MsgContentFmt {
        type Val = MsgContentSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.tag_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for MsgContentFmt {
        type SValue = MsgContentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgContentFmt {
        type SVal = MsgContentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgContentFmt {
        type T = MsgContentSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.tag_spec()).byte_len(v)
        }
    }

    impl SpecParser for MsgAltContentFmt {
        type PVal = MsgAltContentSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.len_spec(), self.tag_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for MsgAltContentFmt {
        type Val = MsgAltContentSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.len_spec(), self.tag_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for MsgAltContentFmt {
        type SValue = MsgAltContentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.len_spec(), self.tag_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for MsgAltContentFmt {
        type SVal = MsgAltContentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.len_spec(), self.tag_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for MsgAltContentFmt {
        type T = MsgAltContentSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.len_spec(), self.tag_spec()).byte_len(v)
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
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg1Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg1Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for Msg1Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg1Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for Msg1Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg2Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg2Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg2Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg2Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg2Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg2Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg2Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg2Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg3Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg3Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg3Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            reveal(<Msg3Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg3Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg3Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg3Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg3Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg3Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MsgTypeFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgTypeFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgTypeFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgTypeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgTypeFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgTypeFmt as SpecParser>::spec_parse);
            reveal(<MsgTypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgTypeFmt as SpecParser>::spec_parse);
            reveal(<MsgTypeFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MsgTypeFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgTypeFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgTypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgTypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MsgTypeFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgTypeFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgTypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgTypeFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgTypeFmt as SpecParser>::spec_parse);
            reveal(<MsgTypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgTypeFmt as Consistency>::consistent);
            reveal(<MsgTypeFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgTypeFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgTypeFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MsgTypeFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MsgTypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgTypeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MsgTypeFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgTypeFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgTypeFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MsgFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            reveal(<MsgFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MsgFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MsgFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            reveal(<MsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgFmt as Consistency>::consistent);
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MsgFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MsgFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MsgParamFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgParamFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.tag_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgParamFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.tag_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgParamFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgParamFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgParamFmt as SpecParser>::spec_parse);
            reveal(<MsgParamFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgParamFmt as SpecParser>::spec_parse);
            reveal(<MsgParamFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for MsgParamFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgParamFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgParamFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgParamFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgParamFmt as SpecParser>::spec_parse);
            reveal(<MsgParamFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgParamFmt as Consistency>::consistent);
            reveal(<MsgParamFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgParamFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgParamFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for MsgParamFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgParamFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgParamFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MsgAltFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgAltFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgAltFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgAltFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgAltFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgAltFmt as SpecParser>::spec_parse);
            reveal(<MsgAltFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgAltFmt as SpecParser>::spec_parse);
            reveal(<MsgAltFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for MsgAltFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgAltFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<MsgAltFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgAltFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for MsgAltFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgAltFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgAltFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgAltFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgAltFmt as SpecParser>::spec_parse);
            reveal(<MsgAltFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgAltFmt as Consistency>::consistent);
            reveal(<MsgAltFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgAltFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgAltFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for MsgAltFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<MsgAltFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgAltFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for MsgAltFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgAltFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgAltFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MsgContentFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgContentFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.tag_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgContentFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.tag_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgContentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgContentFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgContentFmt as SpecParser>::spec_parse);
            reveal(<MsgContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgContentFmt as SpecParser>::spec_parse);
            reveal(<MsgContentFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for MsgContentFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgContentFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgContentFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgContentFmt as SpecParser>::spec_parse);
            reveal(<MsgContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgContentFmt as Consistency>::consistent);
            reveal(<MsgContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgContentFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgContentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for MsgContentFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgContentFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for MsgAltContentFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<MsgAltContentFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.len_spec(), self.tag_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for MsgAltContentFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.len_spec(), self.tag_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<MsgAltContentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.len_spec(), self.tag_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for MsgAltContentFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<MsgAltContentFmt as SpecParser>::spec_parse);
            reveal(<MsgAltContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec(), self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<MsgAltContentFmt as SpecParser>::spec_parse);
            reveal(<MsgAltContentFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.len_spec(), self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for MsgAltContentFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<MsgAltContentFmt as SpecSerializer>::spec_serialize);
            reveal(<MsgAltContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec(), self.tag_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for MsgAltContentFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<MsgAltContentFmt as SpecParser>::spec_parse);
            reveal(<MsgAltContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgAltContentFmt as Consistency>::consistent);
            reveal(<MsgAltContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.len_spec(), self.tag_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for MsgAltContentFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<MsgAltContentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.len_spec(), self.tag_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for MsgAltContentFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<MsgAltContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<MsgAltContentFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.len_spec(), self.tag_spec());
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

            let (n1, a) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, b) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, c) = (Fixed::<3>).parse(&rest)?;
            let rest = rest.skip(n3);
            let (n4, data) = (Tail).parse(&rest)?;
            let rest = rest.skip(n4);
            let total_n = n1 + n2 + n3 + n4;
            let final_v = Msg1 { a, b, c, data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Msg1<'i>> for Msg1Fmt {
        fn serialize(&self, v: &Msg1<'i>, obuf: &mut Vec<u8>) {
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Msg1 { a, b, c, data } = v;
            U8.serialize(a, obuf);
            U16Le.serialize(b, obuf);
            Fixed::<3>.serialize(c, obuf);
            Tail.serialize(data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg1<'i>> for Msg1Fmt {
        fn prepare(&self, v: &Msg1<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let Msg1 { a, b, c, data } = v;
            let l1 = (U8).prepare(a)?;
            let l2 = (U16Le).prepare(b)?;
            let l3 = (Fixed::<3>).prepare(c)?;
            let l4 = (Tail).prepare(data)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?.checked_add(l4).ok_or(
                PreSerializeError::length_too_large(),
            )?;
            Ok(total_len)
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

            let (n1, a) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, b) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, c) = (U32Le).parse(&rest)?;
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

    impl<'i> Prepare<Msg2> for Msg2Fmt {
        fn prepare(&self, v: &Msg2) -> Result<usize, PreSerializeError> {
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            let Msg2 { a, b, c } = v;
            let l1 = (U8).prepare(a)?;
            let l2 = (U16Le).prepare(b)?;
            let l3 = (U32Le).prepare(c)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
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

            let (n1, data) = (Fixed::<6>).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Msg3 { data };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Msg3<'i>> for Msg3Fmt {
        fn serialize(&self, v: &Msg3<'i>, obuf: &mut Vec<u8>) {
            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Msg3 { data } = v;
            Fixed::<6>.serialize(data, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg3<'i>> for Msg3Fmt {
        fn prepare(&self, v: &Msg3<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            let Msg3 { data } = v;
            let l1 = (Fixed::<6>).prepare(data)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for MsgTypeFmt {
        type PT = MsgType;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<MsgTypeFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                1 => MsgType::Msg1,
                2 => MsgType::Msg2,
                3 => MsgType::Msg3,
                _ => return Err(ParseError::invalid_tag()),
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
            Ok((n, enum_val))
        }
    }

    impl<'i> Serializer<MsgType> for MsgTypeFmt {
        fn serialize(&self, v: &MsgType, obuf: &mut Vec<u8>) {
            reveal(<MsgTypeFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                MsgType::Msg1 => 1,
                MsgType::Msg2 => 2,
                MsgType::Msg3 => 3,
            };
            U8.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MsgType> for MsgTypeFmt {
        fn prepare(&self, v: &MsgType) -> Result<usize, PreSerializeError> {
            reveal(<MsgTypeFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                MsgType::Msg1 => 1,
                MsgType::Msg2 => 2,
                MsgType::Msg3 => 3,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for MsgFmt {
        type PT = Msg<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MsgFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, tag) = (Named("msg_type", MsgTypeFmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, len) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, content) = (ExactLen(
                len,
                Named("msg_content", MsgContentFmt { tag: tag }),
            )).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Msg { tag, len, content };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<Msg<'i>> for MsgFmt {
        fn serialize(&self, v: &Msg<'i>, obuf: &mut Vec<u8>) {
            reveal(<MsgFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let Msg { tag, len, content } = v;
            MsgTypeFmt.serialize(tag, obuf);
            U16Le.serialize(len, obuf);
            ExactLen(len, MsgContentFmt { tag: *tag }).serialize(content, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg<'i>> for MsgFmt {
        fn prepare(&self, v: &Msg<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MsgFmt as SpecByteLen>::byte_len);
            let Msg { tag, len, content } = v;
            let l1 = (Named("msg_type", MsgTypeFmt)).prepare(tag)?;
            let l2 = (U16Le).prepare(len)?;
            let l3 = (ExactLen(len, Named("msg_content", MsgContentFmt { tag: *tag }))).prepare(
                content,
            )?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for MsgParamFmt {
        type PT = MsgParam<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<MsgParamFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.tag {
                MsgType::Msg1 => {
                    let (n, v) = (Named("msg1", Msg1Fmt)).parse(&rest)?;
                    (n, MsgParam::Msg1(v))
                },
                MsgType::Msg2 => {
                    let (n, v) = (Named("msg2", Msg2Fmt)).parse(&rest)?;
                    (n, MsgParam::Msg2(v))
                },
                MsgType::Msg3 => {
                    let (n, v) = (Named("msg3", Msg3Fmt)).parse(&rest)?;
                    (n, MsgParam::Msg3(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<MsgParam<'i>> for MsgParamFmt {
        fn serialize(&self, v: &MsgParam<'i>, obuf: &mut Vec<u8>) {
            reveal(<MsgParamFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (MsgType::Msg1, MsgParam::Msg1(v)) => {
                    (Msg1Fmt).serialize(v, obuf);
                },
                (MsgType::Msg2, MsgParam::Msg2(v)) => {
                    (Msg2Fmt).serialize(v, obuf);
                },
                (MsgType::Msg3, MsgParam::Msg3(v)) => {
                    (Msg3Fmt).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MsgParam<'i>> for MsgParamFmt {
        fn prepare(&self, v: &MsgParam<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MsgParamFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.tag, v) {
                (MsgType::Msg1, MsgParam::Msg1(v)) => (Named("msg1", Msg1Fmt)).prepare(v),
                (MsgType::Msg2, MsgParam::Msg2(v)) => (Named("msg2", Msg2Fmt)).prepare(v),
                (MsgType::Msg3, MsgParam::Msg3(v)) => (Named("msg3", Msg3Fmt)).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for MsgAltFmt {
        type PT = MsgAlt<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MsgAltFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, tag) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, len) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n2);
            let (n3, content) = (ExactLen(
                len,
                Named("msg_alt_content", MsgAltContentFmt { len: len, tag: tag }),
            )).parse(&rest)?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = MsgAlt { tag, len, content };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<MsgAlt<'i>> for MsgAltFmt {
        fn serialize(&self, v: &MsgAlt<'i>, obuf: &mut Vec<u8>) {
            reveal(<MsgAltFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let MsgAlt { tag, len, content } = v;
            U8.serialize(tag, obuf);
            U16Le.serialize(len, obuf);
            ExactLen(len, MsgAltContentFmt { len: *len, tag: *tag }).serialize(content, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MsgAlt<'i>> for MsgAltFmt {
        fn prepare(&self, v: &MsgAlt<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MsgAltFmt as SpecByteLen>::byte_len);
            let MsgAlt { tag, len, content } = v;
            let l1 = (U8).prepare(tag)?;
            let l2 = (U16Le).prepare(len)?;
            let l3 = (ExactLen(
                len,
                Named("msg_alt_content", MsgAltContentFmt { len: *len, tag: *tag }),
            )).prepare(content)?;
            let total_len = l1.checked_add(l2).ok_or(
                PreSerializeError::length_too_large(),
            )?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for MsgContentFmt {
        type PT = MsgContent<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<MsgContentFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.tag {
                MsgType::Msg1 => {
                    let (n, v) = (Named("msg1", Msg1Fmt)).parse(&rest)?;
                    (n, MsgContent::Msg1(v))
                },
                MsgType::Msg2 => {
                    let (n, v) = (Named("msg2", Msg2Fmt)).parse(&rest)?;
                    (n, MsgContent::Msg2(v))
                },
                MsgType::Msg3 => {
                    let (n, v) = (Named("msg3", Msg3Fmt)).parse(&rest)?;
                    (n, MsgContent::Msg3(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<MsgContent<'i>> for MsgContentFmt {
        fn serialize(&self, v: &MsgContent<'i>, obuf: &mut Vec<u8>) {
            reveal(<MsgContentFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (MsgType::Msg1, MsgContent::Msg1(v)) => {
                    (Msg1Fmt).serialize(v, obuf);
                },
                (MsgType::Msg2, MsgContent::Msg2(v)) => {
                    (Msg2Fmt).serialize(v, obuf);
                },
                (MsgType::Msg3, MsgContent::Msg3(v)) => {
                    (Msg3Fmt).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MsgContent<'i>> for MsgContentFmt {
        fn prepare(&self, v: &MsgContent<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MsgContentFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.tag, v) {
                (MsgType::Msg1, MsgContent::Msg1(v)) => (Named("msg1", Msg1Fmt)).prepare(v),
                (MsgType::Msg2, MsgContent::Msg2(v)) => (Named("msg2", Msg2Fmt)).prepare(v),
                (MsgType::Msg3, MsgContent::Msg3(v)) => (Named("msg3", Msg3Fmt)).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for MsgAltContentFmt {
        type PT = MsgAltContent<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<MsgAltContentFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.tag {
                1 => {
                    let (n, v) = (Named("msg1", Msg1Fmt)).parse(&rest)?;
                    (n, MsgAltContent::Variant1(v))
                },
                2 => {
                    let (n, v) = (Named("msg2", Msg2Fmt)).parse(&rest)?;
                    (n, MsgAltContent::Variant2(v))
                },
                3 => {
                    let (n, v) = (Named("msg3", Msg3Fmt)).parse(&rest)?;
                    (n, MsgAltContent::Variant3(v))
                },
                _ => {
                    let (n, v) = (Varied(self.len)).parse(&rest)?;
                    (n, MsgAltContent::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<MsgAltContent<'i>> for MsgAltContentFmt {
        fn serialize(&self, v: &MsgAltContent<'i>, obuf: &mut Vec<u8>) {
            reveal(<MsgAltContentFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (1, MsgAltContent::Variant1(v)) => {
                    (Msg1Fmt).serialize(v, obuf);
                },
                (2, MsgAltContent::Variant2(v)) => {
                    (Msg2Fmt).serialize(v, obuf);
                },
                (3, MsgAltContent::Variant3(v)) => {
                    (Msg3Fmt).serialize(v, obuf);
                },
                (_, MsgAltContent::Default(v)) => {
                    (Varied(self.len)).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<MsgAltContent<'i>> for MsgAltContentFmt {
        fn prepare(&self, v: &MsgAltContent<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MsgAltContentFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.tag, v) {
                (1, MsgAltContent::Variant1(v)) => (Named("msg1", Msg1Fmt)).prepare(v),
                (2, MsgAltContent::Variant2(v)) => (Named("msg2", Msg2Fmt)).prepare(v),
                (3, MsgAltContent::Variant3(v)) => (Named("msg3", Msg3Fmt)).prepare(v),
                (x, MsgAltContent::Default(v)) if !(x == 1) && !(x == 2) && !(x == 3) => (Varied(
                    self.len,
                )).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}

} // verus!
