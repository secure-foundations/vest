#![allow(warnings)]
use vest_lib2::combinators::mapped::spec::*;
use vest_lib2::combinators::recursive::*;
use vest_lib2::combinators::*;
use vest_lib2::core::exec::bytes_eq;
use vest_lib2::core::exec::input::{InputBuf, InputSlice};
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
# [doc = "data type for `a_or_b`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum AOrB {
    A = 1,
    B = 2,
}

pub type AOrBSpec = AOrB;

pub type AOrBInner = u8;

impl DeepView for AOrB {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [cfg (not (verus_keep_ghost))]
unsafe impl Structural for AOrB {

}

# [doc = "data type for `c_or_d`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum COrD {
    C = 1,
    D = 2,
}

pub type COrDSpec = COrD;

pub type COrDInner = u8;

impl DeepView for COrD {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [cfg (not (verus_keep_ghost))]
unsafe impl Structural for COrD {

}

# [doc = "data type for `nested_inner_struct`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct NestedInnerStruct<'i> {
    pub len: u32,
    pub val: NestedInnerStructVal<'i>,
}

# [verifier::ext_equal]
pub struct NestedInnerStructSpec {
    pub len: u32,
    pub val: NestedInnerStructValSpec,
}

pub type NestedInnerStructInner = (u32, NestedInnerStructValSpec);

impl<'i> DeepView for NestedInnerStruct<'i> {
    type V = NestedInnerStructSpec;

    open spec fn deep_view(&self) -> Self::V {
        NestedInnerStructSpec { len: self.len.deep_view(), val: self.val.deep_view() }
    }
}

# [doc = "data type for `nested_inner_choice`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct NestedInnerChoice {
    pub x: NestedInnerChoiceX,
}

pub type NestedInnerChoiceSpec = NestedInnerChoice;

pub type NestedInnerChoiceInner = NestedInnerChoiceXSpec;

impl DeepView for NestedInnerChoice {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `capture_outer_and_local`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureOuterAndLocal<'i> {
    pub frame_len: u8,
    pub payload: CaptureOuterAndLocalPayload<'i>,
}

# [verifier::ext_equal]
pub struct CaptureOuterAndLocalSpec {
    pub frame_len: u8,
    pub payload: CaptureOuterAndLocalPayloadSpec,
}

pub type CaptureOuterAndLocalInner = (u8, CaptureOuterAndLocalPayloadSpec);

impl<'i> DeepView for CaptureOuterAndLocal<'i> {
    type V = CaptureOuterAndLocalSpec;

    open spec fn deep_view(&self) -> Self::V {
        CaptureOuterAndLocalSpec {
            frame_len: self.frame_len.deep_view(),
            payload: self.payload.deep_view(),
        }
    }
}

# [doc = "data type for `capture_local_in_anon_struct`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureLocalInAnonStruct<'i> {
    pub wrapper: CaptureLocalInAnonStructWrapper<'i>,
}

# [verifier::ext_equal]
pub struct CaptureLocalInAnonStructSpec {
    pub wrapper: CaptureLocalInAnonStructWrapperSpec,
}

pub type CaptureLocalInAnonStructInner = CaptureLocalInAnonStructWrapperSpec;

impl<'i> DeepView for CaptureLocalInAnonStruct<'i> {
    type V = CaptureLocalInAnonStructSpec;

    open spec fn deep_view(&self) -> Self::V {
        CaptureLocalInAnonStructSpec { wrapper: self.wrapper.deep_view() }
    }
}

# [doc = "data type for `capture_param_and_local`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureParamAndLocal<'i> {
    pub x: CaptureParamAndLocalX<'i>,
}

# [verifier::ext_equal]
pub struct CaptureParamAndLocalSpec {
    pub x: CaptureParamAndLocalXSpec,
}

pub type CaptureParamAndLocalInner = CaptureParamAndLocalXSpec;

impl<'i> DeepView for CaptureParamAndLocal<'i> {
    type V = CaptureParamAndLocalSpec;

    open spec fn deep_view(&self) -> Self::V {
        CaptureParamAndLocalSpec { x: self.x.deep_view() }
    }
}

# [doc = "data type for `nested_inner_struct_val`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct NestedInnerStructVal<'i> {
    pub x: u8,
    pub y: &'i [u8],
}

# [verifier::ext_equal]
pub struct NestedInnerStructValSpec {
    pub x: u8,
    pub y: Seq<u8>,
}

pub type NestedInnerStructValInner = (u8, Seq<u8>);

impl<'i> DeepView for NestedInnerStructVal<'i> {
    type V = NestedInnerStructValSpec;

    open spec fn deep_view(&self) -> Self::V {
        NestedInnerStructValSpec { x: self.x.deep_view(), y: self.y.deep_view() }
    }
}

# [doc = "data type for `nested_inner_choice_x_a`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub enum NestedInnerChoiceXA {
    C(u8),
    D(u16),
}

pub type NestedInnerChoiceXASpec = NestedInnerChoiceXA;

pub type NestedInnerChoiceXAInner = Sum<u8, u16>;

impl DeepView for NestedInnerChoiceXA {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `nested_inner_choice_x`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub enum NestedInnerChoiceX {
    A(NestedInnerChoiceXA),
    B(u32),
}

pub type NestedInnerChoiceXSpec = NestedInnerChoiceX;

pub type NestedInnerChoiceXInner = Sum<NestedInnerChoiceXASpec, u32>;

impl DeepView for NestedInnerChoiceX {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `capture_outer_and_local_payload_body_choice1`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureOuterAndLocalPayloadBodyChoice1<'i> {
    pub count: u8,
    pub items: &'i [u8],
}

# [verifier::ext_equal]
pub struct CaptureOuterAndLocalPayloadBodyChoice1Spec {
    pub count: u8,
    pub items: Seq<u8>,
}

pub type CaptureOuterAndLocalPayloadBodyChoice1Inner = (u8, Seq<u8>);

impl<'i> DeepView for CaptureOuterAndLocalPayloadBodyChoice1<'i> {
    type V = CaptureOuterAndLocalPayloadBodyChoice1Spec;

    open spec fn deep_view(&self) -> Self::V {
        CaptureOuterAndLocalPayloadBodyChoice1Spec {
            count: self.count.deep_view(),
            items: self.items.deep_view(),
        }
    }
}

# [doc = "data type for `capture_outer_and_local_payload_body`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum CaptureOuterAndLocalPayloadBody<'i> {
    Variant1(&'i [u8]),
    Default(CaptureOuterAndLocalPayloadBodyChoice1<'i>),
}

# [verifier::ext_equal]
pub enum CaptureOuterAndLocalPayloadBodySpec {
    Variant1(Seq<u8>),
    Default(CaptureOuterAndLocalPayloadBodyChoice1Spec),
}

pub type CaptureOuterAndLocalPayloadBodyInner = Sum<
    Seq<u8>,
    CaptureOuterAndLocalPayloadBodyChoice1Spec,
>;

impl<'i> DeepView for CaptureOuterAndLocalPayloadBody<'i> {
    type V = CaptureOuterAndLocalPayloadBodySpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            CaptureOuterAndLocalPayloadBody::Variant1(
                v,
            ) => CaptureOuterAndLocalPayloadBodySpec::Variant1(v.deep_view()),
            CaptureOuterAndLocalPayloadBody::Default(
                v,
            ) => CaptureOuterAndLocalPayloadBodySpec::Default(v.deep_view()),
        }
    }
}

# [doc = "data type for `capture_outer_and_local_payload`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureOuterAndLocalPayload<'i> {
    pub tag: u8,
    pub body: CaptureOuterAndLocalPayloadBody<'i>,
}

# [verifier::ext_equal]
pub struct CaptureOuterAndLocalPayloadSpec {
    pub tag: u8,
    pub body: CaptureOuterAndLocalPayloadBodySpec,
}

pub type CaptureOuterAndLocalPayloadInner = (u8, CaptureOuterAndLocalPayloadBodySpec);

impl<'i> DeepView for CaptureOuterAndLocalPayload<'i> {
    type V = CaptureOuterAndLocalPayloadSpec;

    open spec fn deep_view(&self) -> Self::V {
        CaptureOuterAndLocalPayloadSpec { tag: self.tag.deep_view(), body: self.body.deep_view() }
    }
}

# [doc = "data type for `capture_local_in_anon_struct_wrapper_value_choice0`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureLocalInAnonStructWrapperValueChoice0<'i> {
    pub len: u8,
    pub bytes: &'i [u8],
}

# [verifier::ext_equal]
pub struct CaptureLocalInAnonStructWrapperValueChoice0Spec {
    pub len: u8,
    pub bytes: Seq<u8>,
}

pub type CaptureLocalInAnonStructWrapperValueChoice0Inner = (u8, Seq<u8>);

impl<'i> DeepView for CaptureLocalInAnonStructWrapperValueChoice0<'i> {
    type V = CaptureLocalInAnonStructWrapperValueChoice0Spec;

    open spec fn deep_view(&self) -> Self::V {
        CaptureLocalInAnonStructWrapperValueChoice0Spec {
            len: self.len.deep_view(),
            bytes: self.bytes.deep_view(),
        }
    }
}

# [doc = "data type for `capture_local_in_anon_struct_wrapper_value`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum CaptureLocalInAnonStructWrapperValue<'i> {
    Variant1(CaptureLocalInAnonStructWrapperValueChoice0<'i>),
    Default(u16),
}

# [verifier::ext_equal]
pub enum CaptureLocalInAnonStructWrapperValueSpec {
    Variant1(CaptureLocalInAnonStructWrapperValueChoice0Spec),
    Default(u16),
}

pub type CaptureLocalInAnonStructWrapperValueInner = Sum<
    CaptureLocalInAnonStructWrapperValueChoice0Spec,
    u16,
>;

impl<'i> DeepView for CaptureLocalInAnonStructWrapperValue<'i> {
    type V = CaptureLocalInAnonStructWrapperValueSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            CaptureLocalInAnonStructWrapperValue::Variant1(
                v,
            ) => CaptureLocalInAnonStructWrapperValueSpec::Variant1(v.deep_view()),
            CaptureLocalInAnonStructWrapperValue::Default(
                v,
            ) => CaptureLocalInAnonStructWrapperValueSpec::Default(v.deep_view()),
        }
    }
}

# [doc = "data type for `capture_local_in_anon_struct_wrapper`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureLocalInAnonStructWrapper<'i> {
    pub tag: u8,
    pub value: CaptureLocalInAnonStructWrapperValue<'i>,
}

# [verifier::ext_equal]
pub struct CaptureLocalInAnonStructWrapperSpec {
    pub tag: u8,
    pub value: CaptureLocalInAnonStructWrapperValueSpec,
}

pub type CaptureLocalInAnonStructWrapperInner = (u8, CaptureLocalInAnonStructWrapperValueSpec);

impl<'i> DeepView for CaptureLocalInAnonStructWrapper<'i> {
    type V = CaptureLocalInAnonStructWrapperSpec;

    open spec fn deep_view(&self) -> Self::V {
        CaptureLocalInAnonStructWrapperSpec {
            tag: self.tag.deep_view(),
            value: self.value.deep_view(),
        }
    }
}

# [doc = "data type for `capture_param_and_local_x_a_payload`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum CaptureParamAndLocalXAPayload<'i> {
    C(&'i [u8]),
    D(&'i [u8]),
}

# [verifier::ext_equal]
pub enum CaptureParamAndLocalXAPayloadSpec {
    C(Seq<u8>),
    D(Seq<u8>),
}

pub type CaptureParamAndLocalXAPayloadInner = Sum<Seq<u8>, Seq<u8>>;

impl<'i> DeepView for CaptureParamAndLocalXAPayload<'i> {
    type V = CaptureParamAndLocalXAPayloadSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            CaptureParamAndLocalXAPayload::C(v) => CaptureParamAndLocalXAPayloadSpec::C(
                v.deep_view(),
            ),
            CaptureParamAndLocalXAPayload::D(v) => CaptureParamAndLocalXAPayloadSpec::D(
                v.deep_view(),
            ),
        }
    }
}

# [doc = "data type for `capture_param_and_local_x_a`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureParamAndLocalXA<'i> {
    pub len: u8,
    pub payload: CaptureParamAndLocalXAPayload<'i>,
}

# [verifier::ext_equal]
pub struct CaptureParamAndLocalXASpec {
    pub len: u8,
    pub payload: CaptureParamAndLocalXAPayloadSpec,
}

pub type CaptureParamAndLocalXAInner = (u8, CaptureParamAndLocalXAPayloadSpec);

impl<'i> DeepView for CaptureParamAndLocalXA<'i> {
    type V = CaptureParamAndLocalXASpec;

    open spec fn deep_view(&self) -> Self::V {
        CaptureParamAndLocalXASpec { len: self.len.deep_view(), payload: self.payload.deep_view() }
    }
}

# [doc = "data type for `capture_param_and_local_x_b_y`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub enum CaptureParamAndLocalXBY {
    Variant1(u8),
    Default(u16),
}

pub type CaptureParamAndLocalXBYSpec = CaptureParamAndLocalXBY;

pub type CaptureParamAndLocalXBYInner = Sum<u8, u16>;

impl DeepView for CaptureParamAndLocalXBY {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `capture_param_and_local_x_b`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
# [verifier::ext_equal]
pub struct CaptureParamAndLocalXB {
    pub tag: u8,
    pub y: CaptureParamAndLocalXBY,
}

pub type CaptureParamAndLocalXBSpec = CaptureParamAndLocalXB;

pub type CaptureParamAndLocalXBInner = (u8, CaptureParamAndLocalXBYSpec);

impl DeepView for CaptureParamAndLocalXB {
    type V = Self;

    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

# [doc = "data type for `capture_param_and_local_x`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum CaptureParamAndLocalX<'i> {
    A(CaptureParamAndLocalXA<'i>),
    B(CaptureParamAndLocalXB),
}

# [verifier::ext_equal]
pub enum CaptureParamAndLocalXSpec {
    A(CaptureParamAndLocalXASpec),
    B(CaptureParamAndLocalXBSpec),
}

pub type CaptureParamAndLocalXInner = Sum<CaptureParamAndLocalXASpec, CaptureParamAndLocalXBSpec>;

impl<'i> DeepView for CaptureParamAndLocalX<'i> {
    type V = CaptureParamAndLocalXSpec;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            CaptureParamAndLocalX::A(v) => CaptureParamAndLocalXSpec::A(v.deep_view()),
            CaptureParamAndLocalX::B(v) => CaptureParamAndLocalXSpec::B(v.deep_view()),
        }
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `a_or_b`."]
# [derive (Clone, Copy)]
pub struct AOrBFmt;

pub type AOrBFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<AOrBInner, AOrBSpec>>,
>;

impl AOrBFmt {
    # [doc = "specification constructor for `a_or_b`."]
    pub open spec fn spec_inner() -> AOrBFmtSpec {
        Named(
            "a_or_b",
            Mapped {
                inner: Refined(U8, |x: u8| (x == 1) || (x == 2)),
                mapper: (
                    |parsed: AOrBInner| -> AOrBSpec
                        {
                            match parsed {
                                1 => AOrBSpec::A,
                                2 => AOrBSpec::B,
                                _ => arbitrary(),
                            }
                        },
                    |value: AOrBSpec| -> AOrBInner
                        {
                            match value {
                                AOrBSpec::A => 1,
                                AOrBSpec::B => 2,
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `c_or_d`."]
# [derive (Clone, Copy)]
pub struct COrDFmt;

pub type COrDFmtSpec = Named<
    Mapped<Refined<U8, PredFnSpec<u8>>, FnSpecMapper<COrDInner, COrDSpec>>,
>;

impl COrDFmt {
    # [doc = "specification constructor for `c_or_d`."]
    pub open spec fn spec_inner() -> COrDFmtSpec {
        Named(
            "c_or_d",
            Mapped {
                inner: Refined(U8, |x: u8| (x == 1) || (x == 2)),
                mapper: (
                    |parsed: COrDInner| -> COrDSpec
                        {
                            match parsed {
                                1 => COrDSpec::C,
                                2 => COrDSpec::D,
                                _ => arbitrary(),
                            }
                        },
                    |value: COrDSpec| -> COrDInner
                        {
                            match value {
                                COrDSpec::C => 1,
                                COrDSpec::D => 2,
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `nested_inner_struct`."]
# [derive (Clone, Copy)]
pub struct NestedInnerStructFmt;

pub type NestedInnerStructFmtSpec = Named<
    Mapped<
        Bind<U32Le, spec_fn(u32) -> ExactLen<NestedInnerStructValFmt, u32>>,
        FnSpecMapper<NestedInnerStructInner, NestedInnerStructSpec>,
    >,
>;

impl NestedInnerStructFmt {
    # [doc = "specification constructor for `nested_inner_struct`."]
    pub open spec fn spec_inner() -> NestedInnerStructFmtSpec {
        Named(
            "nested_inner_struct",
            Mapped {
                inner: Bind(U32Le, |len: u32| ExactLen(len, NestedInnerStructValFmt)),
                mapper: (
                    |parsed: NestedInnerStructInner| -> NestedInnerStructSpec
                        {
                            let (len, val) = parsed;
                            NestedInnerStructSpec { len, val }
                        },
                    |value: NestedInnerStructSpec| -> NestedInnerStructInner
                        {
                            let NestedInnerStructSpec { len, val } = value;
                            (len, val)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `nested_inner_choice`."]
# [derive (Clone, Copy)]
pub struct NestedInnerChoiceFmt {
    choice1: AOrB,
    choice2: COrD,
}

impl NestedInnerChoiceFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        AOrBFmt.consistent(self.choice1.deep_view()) && COrDFmt.consistent(self.choice2.deep_view())
    }

    pub closed spec fn choice1_spec(&self) -> AOrBSpec {
        self.choice1.deep_view()
    }

    pub closed spec fn choice2_spec(&self) -> COrDSpec {
        self.choice2.deep_view()
    }

    pub closed spec fn spec(choice1: AOrB, choice2: COrD) -> Self {
        NestedInnerChoiceFmt { choice1, choice2 }
    }
}

pub type NestedInnerChoiceFmtSpec = Named<
    Mapped<NestedInnerChoiceXFmt, FnSpecMapper<NestedInnerChoiceInner, NestedInnerChoiceSpec>>,
>;

impl NestedInnerChoiceFmt {
    # [doc = "specification constructor for `nested_inner_choice`."]
    pub open spec fn spec_inner(choice1: AOrBSpec, choice2: COrDSpec) -> NestedInnerChoiceFmtSpec {
        Named(
            "nested_inner_choice",
            Mapped {
                inner: NestedInnerChoiceXFmt::spec(choice1, choice2),
                mapper: (
                    |parsed: NestedInnerChoiceInner| -> NestedInnerChoiceSpec
                        {
                            let x = parsed;
                            NestedInnerChoiceSpec { x }
                        },
                    |value: NestedInnerChoiceSpec| -> NestedInnerChoiceInner
                        {
                            let NestedInnerChoiceSpec { x } = value;
                            x
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_outer_and_local`."]
# [derive (Clone, Copy)]
pub struct CaptureOuterAndLocalFmt;

pub type CaptureOuterAndLocalFmtSpec = Named<
    Mapped<
        Bind<
            Refined<U8, PredFnSpec<u8>>,
            spec_fn(u8) -> ExactLen<CaptureOuterAndLocalPayloadFmt, u8>,
        >,
        FnSpecMapper<CaptureOuterAndLocalInner, CaptureOuterAndLocalSpec>,
    >,
>;

impl CaptureOuterAndLocalFmt {
    # [doc = "specification constructor for `capture_outer_and_local`."]
    pub open spec fn spec_inner() -> CaptureOuterAndLocalFmtSpec {
        Named(
            "capture_outer_and_local",
            Mapped {
                inner: Bind(
                    Refined(U8, |x: u8| x >= 1),
                    |frame_len: u8|
                        ExactLen(frame_len, CaptureOuterAndLocalPayloadFmt::spec(frame_len)),
                ),
                mapper: (
                    |parsed: CaptureOuterAndLocalInner| -> CaptureOuterAndLocalSpec
                        {
                            let (frame_len, payload) = parsed;
                            CaptureOuterAndLocalSpec { frame_len, payload }
                        },
                    |value: CaptureOuterAndLocalSpec| -> CaptureOuterAndLocalInner
                        {
                            let CaptureOuterAndLocalSpec { frame_len, payload } = value;
                            (frame_len, payload)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_local_in_anon_struct`."]
# [derive (Clone, Copy)]
pub struct CaptureLocalInAnonStructFmt;

pub type CaptureLocalInAnonStructFmtSpec = Named<
    Mapped<
        CaptureLocalInAnonStructWrapperFmt,
        FnSpecMapper<CaptureLocalInAnonStructInner, CaptureLocalInAnonStructSpec>,
    >,
>;

impl CaptureLocalInAnonStructFmt {
    # [doc = "specification constructor for `capture_local_in_anon_struct`."]
    pub open spec fn spec_inner() -> CaptureLocalInAnonStructFmtSpec {
        Named(
            "capture_local_in_anon_struct",
            Mapped {
                inner: CaptureLocalInAnonStructWrapperFmt,
                mapper: (
                    |parsed: CaptureLocalInAnonStructInner| -> CaptureLocalInAnonStructSpec
                        {
                            let wrapper = parsed;
                            CaptureLocalInAnonStructSpec { wrapper }
                        },
                    |value: CaptureLocalInAnonStructSpec| -> CaptureLocalInAnonStructInner
                        {
                            let CaptureLocalInAnonStructSpec { wrapper } = value;
                            wrapper
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_param_and_local`."]
# [derive (Clone, Copy)]
pub struct CaptureParamAndLocalFmt {
    choice1: AOrB,
    choice2: COrD,
}

impl CaptureParamAndLocalFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        AOrBFmt.consistent(self.choice1.deep_view()) && COrDFmt.consistent(self.choice2.deep_view())
    }

    pub closed spec fn choice1_spec(&self) -> AOrBSpec {
        self.choice1.deep_view()
    }

    pub closed spec fn choice2_spec(&self) -> COrDSpec {
        self.choice2.deep_view()
    }

    pub closed spec fn spec(choice1: AOrB, choice2: COrD) -> Self {
        CaptureParamAndLocalFmt { choice1, choice2 }
    }
}

pub type CaptureParamAndLocalFmtSpec = Named<
    Mapped<
        CaptureParamAndLocalXFmt,
        FnSpecMapper<CaptureParamAndLocalInner, CaptureParamAndLocalSpec>,
    >,
>;

impl CaptureParamAndLocalFmt {
    # [doc = "specification constructor for `capture_param_and_local`."]
    pub open spec fn spec_inner(
        choice1: AOrBSpec,
        choice2: COrDSpec,
    ) -> CaptureParamAndLocalFmtSpec {
        Named(
            "capture_param_and_local",
            Mapped {
                inner: CaptureParamAndLocalXFmt::spec(choice1, choice2),
                mapper: (
                    |parsed: CaptureParamAndLocalInner| -> CaptureParamAndLocalSpec
                        {
                            let x = parsed;
                            CaptureParamAndLocalSpec { x }
                        },
                    |value: CaptureParamAndLocalSpec| -> CaptureParamAndLocalInner
                        {
                            let CaptureParamAndLocalSpec { x } = value;
                            x
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `nested_inner_struct_val`."]
# [derive (Clone, Copy)]
pub struct NestedInnerStructValFmt;

pub type NestedInnerStructValFmtSpec = Named<
    Mapped<Pair<U8, Tail>, FnSpecMapper<NestedInnerStructValInner, NestedInnerStructValSpec>>,
>;

impl NestedInnerStructValFmt {
    # [doc = "specification constructor for `nested_inner_struct_val`."]
    pub open spec fn spec_inner() -> NestedInnerStructValFmtSpec {
        Named(
            "nested_inner_struct_val",
            Mapped {
                inner: Pair(U8, Tail),
                mapper: (
                    |parsed: NestedInnerStructValInner| -> NestedInnerStructValSpec
                        {
                            let (x, y) = parsed;
                            NestedInnerStructValSpec { x, y }
                        },
                    |value: NestedInnerStructValSpec| -> NestedInnerStructValInner
                        {
                            let NestedInnerStructValSpec { x, y } = value;
                            (x, y)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `nested_inner_choice_x_a`."]
# [derive (Clone, Copy)]
pub struct NestedInnerChoiceXAFmt {
    choice2: COrD,
}

impl NestedInnerChoiceXAFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        COrDFmt.consistent(self.choice2.deep_view())
    }

    pub closed spec fn choice2_spec(&self) -> COrDSpec {
        self.choice2.deep_view()
    }

    pub closed spec fn spec(choice2: COrD) -> Self {
        NestedInnerChoiceXAFmt { choice2 }
    }
}

pub type NestedInnerChoiceXAFmtSpec = Named<
    Mapped<Sum<U8, U16Le>, FnSpecMapper<NestedInnerChoiceXAInner, NestedInnerChoiceXASpec>>,
>;

impl NestedInnerChoiceXAFmt {
    # [doc = "specification constructor for `nested_inner_choice_x_a`."]
    pub open spec fn spec_inner(choice2: COrDSpec) -> NestedInnerChoiceXAFmtSpec {
        Named(
            "nested_inner_choice_x_a",
            Mapped {
                inner: match choice2 {
                    COrDSpec::C => L(U8),
                    COrDSpec::D => R(U16Le),
                },
                mapper: (
                    |parsed: NestedInnerChoiceXAInner| -> NestedInnerChoiceXASpec
                        {
                            match parsed {
                                L(v) => NestedInnerChoiceXASpec::C(v),
                                R(v) => NestedInnerChoiceXASpec::D(v),
                            }
                        },
                    |value: NestedInnerChoiceXASpec| -> NestedInnerChoiceXAInner
                        {
                            match value {
                                NestedInnerChoiceXASpec::C(v) => L(v),
                                NestedInnerChoiceXASpec::D(v) => R(v),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `nested_inner_choice_x`."]
# [derive (Clone, Copy)]
pub struct NestedInnerChoiceXFmt {
    choice1: AOrB,
    choice2: COrD,
}

impl NestedInnerChoiceXFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        AOrBFmt.consistent(self.choice1.deep_view()) && COrDFmt.consistent(self.choice2.deep_view())
    }

    pub closed spec fn choice1_spec(&self) -> AOrBSpec {
        self.choice1.deep_view()
    }

    pub closed spec fn choice2_spec(&self) -> COrDSpec {
        self.choice2.deep_view()
    }

    pub closed spec fn spec(choice1: AOrB, choice2: COrD) -> Self {
        NestedInnerChoiceXFmt { choice1, choice2 }
    }
}

pub type NestedInnerChoiceXFmtSpec = Named<
    Mapped<
        Sum<NestedInnerChoiceXAFmt, U32Le>,
        FnSpecMapper<NestedInnerChoiceXInner, NestedInnerChoiceXSpec>,
    >,
>;

impl NestedInnerChoiceXFmt {
    # [doc = "specification constructor for `nested_inner_choice_x`."]
    pub open spec fn spec_inner(choice1: AOrBSpec, choice2: COrDSpec) -> NestedInnerChoiceXFmtSpec {
        Named(
            "nested_inner_choice_x",
            Mapped {
                inner: match choice1 {
                    AOrBSpec::A => L(NestedInnerChoiceXAFmt::spec(choice2)),
                    AOrBSpec::B => R(U32Le),
                },
                mapper: (
                    |parsed: NestedInnerChoiceXInner| -> NestedInnerChoiceXSpec
                        {
                            match parsed {
                                L(v) => NestedInnerChoiceXSpec::A(v),
                                R(v) => NestedInnerChoiceXSpec::B(v),
                            }
                        },
                    |value: NestedInnerChoiceXSpec| -> NestedInnerChoiceXInner
                        {
                            match value {
                                NestedInnerChoiceXSpec::A(v) => L(v),
                                NestedInnerChoiceXSpec::B(v) => R(v),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_outer_and_local_payload_body_choice1`."]
# [derive (Clone, Copy)]
pub struct CaptureOuterAndLocalPayloadBodyChoice1Fmt;

pub type CaptureOuterAndLocalPayloadBodyChoice1FmtSpec = Named<
    Mapped<
        Bind<U8, spec_fn(u8) -> Varied<u8>>,
        FnSpecMapper<
            CaptureOuterAndLocalPayloadBodyChoice1Inner,
            CaptureOuterAndLocalPayloadBodyChoice1Spec,
        >,
    >,
>;

impl CaptureOuterAndLocalPayloadBodyChoice1Fmt {
    # [doc = "specification constructor for `capture_outer_and_local_payload_body_choice1`."]
    pub open spec fn spec_inner() -> CaptureOuterAndLocalPayloadBodyChoice1FmtSpec {
        Named(
            "capture_outer_and_local_payload_body_choice1",
            Mapped {
                inner: Bind(U8, |count: u8| Varied(count)),
                mapper: (
                    |parsed: CaptureOuterAndLocalPayloadBodyChoice1Inner|
                     -> CaptureOuterAndLocalPayloadBodyChoice1Spec
                        {
                            let (count, items) = parsed;
                            CaptureOuterAndLocalPayloadBodyChoice1Spec { count, items }
                        },
                    |value: CaptureOuterAndLocalPayloadBodyChoice1Spec|
                     -> CaptureOuterAndLocalPayloadBodyChoice1Inner
                        {
                            let CaptureOuterAndLocalPayloadBodyChoice1Spec { count, items } = value;
                            (count, items)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_outer_and_local_payload_body`."]
# [derive (Clone, Copy)]
pub struct CaptureOuterAndLocalPayloadBodyFmt {
    frame_len: u8,
    tag: u8,
}

impl CaptureOuterAndLocalPayloadBodyFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.frame_len >= 1
    }

    pub closed spec fn frame_len_spec(&self) -> u8 {
        self.frame_len.deep_view()
    }

    pub closed spec fn tag_spec(&self) -> u8 {
        self.tag.deep_view()
    }

    pub closed spec fn spec(frame_len: u8, tag: u8) -> Self {
        CaptureOuterAndLocalPayloadBodyFmt { frame_len, tag }
    }
}

pub type CaptureOuterAndLocalPayloadBodyFmtSpec = Named<
    Mapped<
        Sum<Varied<u8>, CaptureOuterAndLocalPayloadBodyChoice1Fmt>,
        FnSpecMapper<CaptureOuterAndLocalPayloadBodyInner, CaptureOuterAndLocalPayloadBodySpec>,
    >,
>;

impl CaptureOuterAndLocalPayloadBodyFmt {
    # [doc = "specification constructor for `capture_outer_and_local_payload_body`."]
    pub open spec fn spec_inner(frame_len: u8, tag: u8) -> CaptureOuterAndLocalPayloadBodyFmtSpec {
        Named(
            "capture_outer_and_local_payload_body",
            Mapped {
                inner: match tag {
                    0 => L(Varied(((frame_len - 1) as u8))),
                    _ => R(CaptureOuterAndLocalPayloadBodyChoice1Fmt),
                },
                mapper: (
                    |parsed: CaptureOuterAndLocalPayloadBodyInner|
                     -> CaptureOuterAndLocalPayloadBodySpec
                        {
                            match parsed {
                                L(v) => CaptureOuterAndLocalPayloadBodySpec::Variant1(v),
                                R(v) => CaptureOuterAndLocalPayloadBodySpec::Default(v),
                            }
                        },
                    |value: CaptureOuterAndLocalPayloadBodySpec|
                     -> CaptureOuterAndLocalPayloadBodyInner
                        {
                            match value {
                                CaptureOuterAndLocalPayloadBodySpec::Variant1(v) => L(v),
                                CaptureOuterAndLocalPayloadBodySpec::Default(v) => R(v),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_outer_and_local_payload`."]
# [derive (Clone, Copy)]
pub struct CaptureOuterAndLocalPayloadFmt {
    frame_len: u8,
}

impl CaptureOuterAndLocalPayloadFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.frame_len >= 1
    }

    pub closed spec fn frame_len_spec(&self) -> u8 {
        self.frame_len.deep_view()
    }

    pub closed spec fn spec(frame_len: u8) -> Self {
        CaptureOuterAndLocalPayloadFmt { frame_len }
    }
}

pub type CaptureOuterAndLocalPayloadFmtSpec = Named<
    Mapped<
        Bind<U8, spec_fn(u8) -> CaptureOuterAndLocalPayloadBodyFmt>,
        FnSpecMapper<CaptureOuterAndLocalPayloadInner, CaptureOuterAndLocalPayloadSpec>,
    >,
>;

impl CaptureOuterAndLocalPayloadFmt {
    # [doc = "specification constructor for `capture_outer_and_local_payload`."]
    pub open spec fn spec_inner(frame_len: u8) -> CaptureOuterAndLocalPayloadFmtSpec {
        Named(
            "capture_outer_and_local_payload",
            Mapped {
                inner: Bind(U8, |tag: u8| CaptureOuterAndLocalPayloadBodyFmt::spec(frame_len, tag)),
                mapper: (
                    |parsed: CaptureOuterAndLocalPayloadInner| -> CaptureOuterAndLocalPayloadSpec
                        {
                            let (tag, body) = parsed;
                            CaptureOuterAndLocalPayloadSpec { tag, body }
                        },
                    |value: CaptureOuterAndLocalPayloadSpec| -> CaptureOuterAndLocalPayloadInner
                        {
                            let CaptureOuterAndLocalPayloadSpec { tag, body } = value;
                            (tag, body)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_local_in_anon_struct_wrapper_value_choice0`."]
# [derive (Clone, Copy)]
pub struct CaptureLocalInAnonStructWrapperValueChoice0Fmt;

pub type CaptureLocalInAnonStructWrapperValueChoice0FmtSpec = Named<
    Mapped<
        Bind<U8, spec_fn(u8) -> Varied<u8>>,
        FnSpecMapper<
            CaptureLocalInAnonStructWrapperValueChoice0Inner,
            CaptureLocalInAnonStructWrapperValueChoice0Spec,
        >,
    >,
>;

impl CaptureLocalInAnonStructWrapperValueChoice0Fmt {
    # [doc = "specification constructor for `capture_local_in_anon_struct_wrapper_value_choice0`."]
    pub open spec fn spec_inner() -> CaptureLocalInAnonStructWrapperValueChoice0FmtSpec {
        Named(
            "capture_local_in_anon_struct_wrapper_value_choice0",
            Mapped {
                inner: Bind(U8, |len: u8| Varied(len)),
                mapper: (
                    |parsed: CaptureLocalInAnonStructWrapperValueChoice0Inner|
                     -> CaptureLocalInAnonStructWrapperValueChoice0Spec
                        {
                            let (len, bytes) = parsed;
                            CaptureLocalInAnonStructWrapperValueChoice0Spec { len, bytes }
                        },
                    |value: CaptureLocalInAnonStructWrapperValueChoice0Spec|
                     -> CaptureLocalInAnonStructWrapperValueChoice0Inner
                        {
                            let CaptureLocalInAnonStructWrapperValueChoice0Spec { len, bytes } =
                                value;
                            (len, bytes)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_local_in_anon_struct_wrapper_value`."]
# [derive (Clone, Copy)]
pub struct CaptureLocalInAnonStructWrapperValueFmt {
    tag: u8,
}

impl CaptureLocalInAnonStructWrapperValueFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn tag_spec(&self) -> u8 {
        self.tag.deep_view()
    }

    pub closed spec fn spec(tag: u8) -> Self {
        CaptureLocalInAnonStructWrapperValueFmt { tag }
    }
}

pub type CaptureLocalInAnonStructWrapperValueFmtSpec = Named<
    Mapped<
        Sum<CaptureLocalInAnonStructWrapperValueChoice0Fmt, U16Le>,
        FnSpecMapper<
            CaptureLocalInAnonStructWrapperValueInner,
            CaptureLocalInAnonStructWrapperValueSpec,
        >,
    >,
>;

impl CaptureLocalInAnonStructWrapperValueFmt {
    # [doc = "specification constructor for `capture_local_in_anon_struct_wrapper_value`."]
    pub open spec fn spec_inner(tag: u8) -> CaptureLocalInAnonStructWrapperValueFmtSpec {
        Named(
            "capture_local_in_anon_struct_wrapper_value",
            Mapped {
                inner: match tag {
                    0 => L(CaptureLocalInAnonStructWrapperValueChoice0Fmt),
                    _ => R(U16Le),
                },
                mapper: (
                    |parsed: CaptureLocalInAnonStructWrapperValueInner|
                     -> CaptureLocalInAnonStructWrapperValueSpec
                        {
                            match parsed {
                                L(v) => CaptureLocalInAnonStructWrapperValueSpec::Variant1(v),
                                R(v) => CaptureLocalInAnonStructWrapperValueSpec::Default(v),
                            }
                        },
                    |value: CaptureLocalInAnonStructWrapperValueSpec|
                     -> CaptureLocalInAnonStructWrapperValueInner
                        {
                            match value {
                                CaptureLocalInAnonStructWrapperValueSpec::Variant1(v) => L(v),
                                CaptureLocalInAnonStructWrapperValueSpec::Default(v) => R(v),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_local_in_anon_struct_wrapper`."]
# [derive (Clone, Copy)]
pub struct CaptureLocalInAnonStructWrapperFmt;

pub type CaptureLocalInAnonStructWrapperFmtSpec = Named<
    Mapped<
        Bind<U8, spec_fn(u8) -> CaptureLocalInAnonStructWrapperValueFmt>,
        FnSpecMapper<CaptureLocalInAnonStructWrapperInner, CaptureLocalInAnonStructWrapperSpec>,
    >,
>;

impl CaptureLocalInAnonStructWrapperFmt {
    # [doc = "specification constructor for `capture_local_in_anon_struct_wrapper`."]
    pub open spec fn spec_inner() -> CaptureLocalInAnonStructWrapperFmtSpec {
        Named(
            "capture_local_in_anon_struct_wrapper",
            Mapped {
                inner: Bind(U8, |tag: u8| CaptureLocalInAnonStructWrapperValueFmt::spec(tag)),
                mapper: (
                    |parsed: CaptureLocalInAnonStructWrapperInner|
                     -> CaptureLocalInAnonStructWrapperSpec
                        {
                            let (tag, value) = parsed;
                            CaptureLocalInAnonStructWrapperSpec { tag, value }
                        },
                    |value: CaptureLocalInAnonStructWrapperSpec|
                     -> CaptureLocalInAnonStructWrapperInner
                        {
                            let CaptureLocalInAnonStructWrapperSpec { tag, value } = value;
                            (tag, value)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_param_and_local_x_a_payload`."]
# [derive (Clone, Copy)]
pub struct CaptureParamAndLocalXAPayloadFmt {
    choice2: COrD,
    len: u8,
}

impl CaptureParamAndLocalXAPayloadFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        COrDFmt.consistent(self.choice2.deep_view())
    }

    pub closed spec fn choice2_spec(&self) -> COrDSpec {
        self.choice2.deep_view()
    }

    pub closed spec fn len_spec(&self) -> u8 {
        self.len.deep_view()
    }

    pub closed spec fn spec(choice2: COrD, len: u8) -> Self {
        CaptureParamAndLocalXAPayloadFmt { choice2, len }
    }
}

pub type CaptureParamAndLocalXAPayloadFmtSpec = Named<
    Mapped<
        Sum<Varied<u8>, Varied<u8>>,
        FnSpecMapper<CaptureParamAndLocalXAPayloadInner, CaptureParamAndLocalXAPayloadSpec>,
    >,
>;

impl CaptureParamAndLocalXAPayloadFmt {
    # [doc = "specification constructor for `capture_param_and_local_x_a_payload`."]
    pub open spec fn spec_inner(
        choice2: COrDSpec,
        len: u8,
    ) -> CaptureParamAndLocalXAPayloadFmtSpec {
        Named(
            "capture_param_and_local_x_a_payload",
            Mapped {
                inner: match choice2 {
                    COrDSpec::C => L(Varied(len)),
                    COrDSpec::D => R(Varied(len)),
                },
                mapper: (
                    |parsed: CaptureParamAndLocalXAPayloadInner|
                     -> CaptureParamAndLocalXAPayloadSpec
                        {
                            match parsed {
                                L(v) => CaptureParamAndLocalXAPayloadSpec::C(v),
                                R(v) => CaptureParamAndLocalXAPayloadSpec::D(v),
                            }
                        },
                    |value: CaptureParamAndLocalXAPayloadSpec|
                     -> CaptureParamAndLocalXAPayloadInner
                        {
                            match value {
                                CaptureParamAndLocalXAPayloadSpec::C(v) => L(v),
                                CaptureParamAndLocalXAPayloadSpec::D(v) => R(v),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_param_and_local_x_a`."]
# [derive (Clone, Copy)]
pub struct CaptureParamAndLocalXAFmt {
    choice2: COrD,
}

impl CaptureParamAndLocalXAFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        COrDFmt.consistent(self.choice2.deep_view())
    }

    pub closed spec fn choice2_spec(&self) -> COrDSpec {
        self.choice2.deep_view()
    }

    pub closed spec fn spec(choice2: COrD) -> Self {
        CaptureParamAndLocalXAFmt { choice2 }
    }
}

pub type CaptureParamAndLocalXAFmtSpec = Named<
    Mapped<
        Bind<U8, spec_fn(u8) -> CaptureParamAndLocalXAPayloadFmt>,
        FnSpecMapper<CaptureParamAndLocalXAInner, CaptureParamAndLocalXASpec>,
    >,
>;

impl CaptureParamAndLocalXAFmt {
    # [doc = "specification constructor for `capture_param_and_local_x_a`."]
    pub open spec fn spec_inner(choice2: COrDSpec) -> CaptureParamAndLocalXAFmtSpec {
        Named(
            "capture_param_and_local_x_a",
            Mapped {
                inner: Bind(U8, |len: u8| CaptureParamAndLocalXAPayloadFmt::spec(choice2, len)),
                mapper: (
                    |parsed: CaptureParamAndLocalXAInner| -> CaptureParamAndLocalXASpec
                        {
                            let (len, payload) = parsed;
                            CaptureParamAndLocalXASpec { len, payload }
                        },
                    |value: CaptureParamAndLocalXASpec| -> CaptureParamAndLocalXAInner
                        {
                            let CaptureParamAndLocalXASpec { len, payload } = value;
                            (len, payload)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_param_and_local_x_b_y`."]
# [derive (Clone, Copy)]
pub struct CaptureParamAndLocalXBYFmt {
    tag: u8,
}

impl CaptureParamAndLocalXBYFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn tag_spec(&self) -> u8 {
        self.tag.deep_view()
    }

    pub closed spec fn spec(tag: u8) -> Self {
        CaptureParamAndLocalXBYFmt { tag }
    }
}

pub type CaptureParamAndLocalXBYFmtSpec = Named<
    Mapped<Sum<U8, U16Le>, FnSpecMapper<CaptureParamAndLocalXBYInner, CaptureParamAndLocalXBYSpec>>,
>;

impl CaptureParamAndLocalXBYFmt {
    # [doc = "specification constructor for `capture_param_and_local_x_b_y`."]
    pub open spec fn spec_inner(tag: u8) -> CaptureParamAndLocalXBYFmtSpec {
        Named(
            "capture_param_and_local_x_b_y",
            Mapped {
                inner: match tag {
                    0 => L(U8),
                    _ => R(U16Le),
                },
                mapper: (
                    |parsed: CaptureParamAndLocalXBYInner| -> CaptureParamAndLocalXBYSpec
                        {
                            match parsed {
                                L(v) => CaptureParamAndLocalXBYSpec::Variant1(v),
                                R(v) => CaptureParamAndLocalXBYSpec::Default(v),
                            }
                        },
                    |value: CaptureParamAndLocalXBYSpec| -> CaptureParamAndLocalXBYInner
                        {
                            match value {
                                CaptureParamAndLocalXBYSpec::Variant1(v) => L(v),
                                CaptureParamAndLocalXBYSpec::Default(v) => R(v),
                            }
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_param_and_local_x_b`."]
# [derive (Clone, Copy)]
pub struct CaptureParamAndLocalXBFmt;

pub type CaptureParamAndLocalXBFmtSpec = Named<
    Mapped<
        Bind<U8, spec_fn(u8) -> CaptureParamAndLocalXBYFmt>,
        FnSpecMapper<CaptureParamAndLocalXBInner, CaptureParamAndLocalXBSpec>,
    >,
>;

impl CaptureParamAndLocalXBFmt {
    # [doc = "specification constructor for `capture_param_and_local_x_b`."]
    pub open spec fn spec_inner() -> CaptureParamAndLocalXBFmtSpec {
        Named(
            "capture_param_and_local_x_b",
            Mapped {
                inner: Bind(U8, |tag: u8| CaptureParamAndLocalXBYFmt::spec(tag)),
                mapper: (
                    |parsed: CaptureParamAndLocalXBInner| -> CaptureParamAndLocalXBSpec
                        {
                            let (tag, y) = parsed;
                            CaptureParamAndLocalXBSpec { tag, y }
                        },
                    |value: CaptureParamAndLocalXBSpec| -> CaptureParamAndLocalXBInner
                        {
                            let CaptureParamAndLocalXBSpec { tag, y } = value;
                            (tag, y)
                        },
                ),
            },
        )
    }
}

# [doc = "named format combinator for `capture_param_and_local_x`."]
# [derive (Clone, Copy)]
pub struct CaptureParamAndLocalXFmt {
    choice1: AOrB,
    choice2: COrD,
}

impl CaptureParamAndLocalXFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        AOrBFmt.consistent(self.choice1.deep_view()) && COrDFmt.consistent(self.choice2.deep_view())
    }

    pub closed spec fn choice1_spec(&self) -> AOrBSpec {
        self.choice1.deep_view()
    }

    pub closed spec fn choice2_spec(&self) -> COrDSpec {
        self.choice2.deep_view()
    }

    pub closed spec fn spec(choice1: AOrB, choice2: COrD) -> Self {
        CaptureParamAndLocalXFmt { choice1, choice2 }
    }
}

pub type CaptureParamAndLocalXFmtSpec = Named<
    Mapped<
        Sum<CaptureParamAndLocalXAFmt, CaptureParamAndLocalXBFmt>,
        FnSpecMapper<CaptureParamAndLocalXInner, CaptureParamAndLocalXSpec>,
    >,
>;

impl CaptureParamAndLocalXFmt {
    # [doc = "specification constructor for `capture_param_and_local_x`."]
    pub open spec fn spec_inner(
        choice1: AOrBSpec,
        choice2: COrDSpec,
    ) -> CaptureParamAndLocalXFmtSpec {
        Named(
            "capture_param_and_local_x",
            Mapped {
                inner: match choice1 {
                    AOrBSpec::A => L(CaptureParamAndLocalXAFmt::spec(choice2)),
                    AOrBSpec::B => R(CaptureParamAndLocalXBFmt),
                },
                mapper: (
                    |parsed: CaptureParamAndLocalXInner| -> CaptureParamAndLocalXSpec
                        {
                            match parsed {
                                L(v) => CaptureParamAndLocalXSpec::A(v),
                                R(v) => CaptureParamAndLocalXSpec::B(v),
                            }
                        },
                    |value: CaptureParamAndLocalXSpec| -> CaptureParamAndLocalXInner
                        {
                            match value {
                                CaptureParamAndLocalXSpec::A(v) => L(v),
                                CaptureParamAndLocalXSpec::B(v) => R(v),
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

    impl SpecParser for AOrBFmt {
        type PVal = AOrBSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for AOrBFmt {
        type Val = AOrBSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for AOrBFmt {
        type SValue = AOrBSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for AOrBFmt {
        type SVal = AOrBSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for AOrBFmt {
        type T = AOrBSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for COrDFmt {
        type PVal = COrDSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for COrDFmt {
        type Val = COrDSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for COrDFmt {
        type SValue = COrDSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for COrDFmt {
        type SVal = COrDSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for COrDFmt {
        type T = COrDSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for NestedInnerStructFmt {
        type PVal = NestedInnerStructSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for NestedInnerStructFmt {
        type Val = NestedInnerStructSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for NestedInnerStructFmt {
        type SValue = NestedInnerStructSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for NestedInnerStructFmt {
        type SVal = NestedInnerStructSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for NestedInnerStructFmt {
        type T = NestedInnerStructSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for NestedInnerChoiceFmt {
        type PVal = NestedInnerChoiceSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for NestedInnerChoiceFmt {
        type Val = NestedInnerChoiceSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for NestedInnerChoiceFmt {
        type SValue = NestedInnerChoiceSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for NestedInnerChoiceFmt {
        type SVal = NestedInnerChoiceSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for NestedInnerChoiceFmt {
        type T = NestedInnerChoiceSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).byte_len(v)
        }
    }

    impl SpecParser for CaptureOuterAndLocalFmt {
        type PVal = CaptureOuterAndLocalSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureOuterAndLocalFmt {
        type Val = CaptureOuterAndLocalSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureOuterAndLocalFmt {
        type SValue = CaptureOuterAndLocalSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureOuterAndLocalFmt {
        type SVal = CaptureOuterAndLocalSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureOuterAndLocalFmt {
        type T = CaptureOuterAndLocalSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for CaptureLocalInAnonStructFmt {
        type PVal = CaptureLocalInAnonStructSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureLocalInAnonStructFmt {
        type Val = CaptureLocalInAnonStructSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureLocalInAnonStructFmt {
        type SValue = CaptureLocalInAnonStructSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureLocalInAnonStructFmt {
        type SVal = CaptureLocalInAnonStructSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureLocalInAnonStructFmt {
        type T = CaptureLocalInAnonStructSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for CaptureParamAndLocalFmt {
        type PVal = CaptureParamAndLocalSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureParamAndLocalFmt {
        type Val = CaptureParamAndLocalSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureParamAndLocalFmt {
        type SValue = CaptureParamAndLocalSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureParamAndLocalFmt {
        type SVal = CaptureParamAndLocalSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureParamAndLocalFmt {
        type T = CaptureParamAndLocalSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).byte_len(v)
        }
    }

    impl SpecParser for NestedInnerStructValFmt {
        type PVal = NestedInnerStructValSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for NestedInnerStructValFmt {
        type Val = NestedInnerStructValSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for NestedInnerStructValFmt {
        type SValue = NestedInnerStructValSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for NestedInnerStructValFmt {
        type SVal = NestedInnerStructValSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for NestedInnerStructValFmt {
        type T = NestedInnerStructValSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for NestedInnerChoiceXAFmt {
        type PVal = NestedInnerChoiceXASpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.choice2_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for NestedInnerChoiceXAFmt {
        type Val = NestedInnerChoiceXASpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.choice2_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for NestedInnerChoiceXAFmt {
        type SValue = NestedInnerChoiceXASpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.choice2_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for NestedInnerChoiceXAFmt {
        type SVal = NestedInnerChoiceXASpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.choice2_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for NestedInnerChoiceXAFmt {
        type T = NestedInnerChoiceXASpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.choice2_spec()).byte_len(v)
        }
    }

    impl SpecParser for NestedInnerChoiceXFmt {
        type PVal = NestedInnerChoiceXSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for NestedInnerChoiceXFmt {
        type Val = NestedInnerChoiceXSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for NestedInnerChoiceXFmt {
        type SValue = NestedInnerChoiceXSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for NestedInnerChoiceXFmt {
        type SVal = NestedInnerChoiceXSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for NestedInnerChoiceXFmt {
        type T = NestedInnerChoiceXSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).byte_len(v)
        }
    }

    impl SpecParser for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        type PVal = CaptureOuterAndLocalPayloadBodyChoice1Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        type Val = CaptureOuterAndLocalPayloadBodyChoice1Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        type SValue = CaptureOuterAndLocalPayloadBodyChoice1Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        type SVal = CaptureOuterAndLocalPayloadBodyChoice1Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        type T = CaptureOuterAndLocalPayloadBodyChoice1Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for CaptureOuterAndLocalPayloadBodyFmt {
        type PVal = CaptureOuterAndLocalPayloadBodySpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.frame_len_spec(), self.tag_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureOuterAndLocalPayloadBodyFmt {
        type Val = CaptureOuterAndLocalPayloadBodySpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.frame_len_spec(), self.tag_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureOuterAndLocalPayloadBodyFmt {
        type SValue = CaptureOuterAndLocalPayloadBodySpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.frame_len_spec(), self.tag_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureOuterAndLocalPayloadBodyFmt {
        type SVal = CaptureOuterAndLocalPayloadBodySpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.frame_len_spec(), self.tag_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureOuterAndLocalPayloadBodyFmt {
        type T = CaptureOuterAndLocalPayloadBodySpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.frame_len_spec(), self.tag_spec()).byte_len(v)
        }
    }

    impl SpecParser for CaptureOuterAndLocalPayloadFmt {
        type PVal = CaptureOuterAndLocalPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.frame_len_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureOuterAndLocalPayloadFmt {
        type Val = CaptureOuterAndLocalPayloadSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.frame_len_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureOuterAndLocalPayloadFmt {
        type SValue = CaptureOuterAndLocalPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.frame_len_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureOuterAndLocalPayloadFmt {
        type SVal = CaptureOuterAndLocalPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.frame_len_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureOuterAndLocalPayloadFmt {
        type T = CaptureOuterAndLocalPayloadSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.frame_len_spec()).byte_len(v)
        }
    }

    impl SpecParser for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        type PVal = CaptureLocalInAnonStructWrapperValueChoice0Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        type Val = CaptureLocalInAnonStructWrapperValueChoice0Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        type SValue = CaptureLocalInAnonStructWrapperValueChoice0Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        type SVal = CaptureLocalInAnonStructWrapperValueChoice0Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        type T = CaptureLocalInAnonStructWrapperValueChoice0Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for CaptureLocalInAnonStructWrapperValueFmt {
        type PVal = CaptureLocalInAnonStructWrapperValueSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.tag_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureLocalInAnonStructWrapperValueFmt {
        type Val = CaptureLocalInAnonStructWrapperValueSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.tag_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureLocalInAnonStructWrapperValueFmt {
        type SValue = CaptureLocalInAnonStructWrapperValueSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureLocalInAnonStructWrapperValueFmt {
        type SVal = CaptureLocalInAnonStructWrapperValueSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureLocalInAnonStructWrapperValueFmt {
        type T = CaptureLocalInAnonStructWrapperValueSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.tag_spec()).byte_len(v)
        }
    }

    impl SpecParser for CaptureLocalInAnonStructWrapperFmt {
        type PVal = CaptureLocalInAnonStructWrapperSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureLocalInAnonStructWrapperFmt {
        type Val = CaptureLocalInAnonStructWrapperSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureLocalInAnonStructWrapperFmt {
        type SValue = CaptureLocalInAnonStructWrapperSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureLocalInAnonStructWrapperFmt {
        type SVal = CaptureLocalInAnonStructWrapperSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureLocalInAnonStructWrapperFmt {
        type T = CaptureLocalInAnonStructWrapperSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for CaptureParamAndLocalXAPayloadFmt {
        type PVal = CaptureParamAndLocalXAPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.choice2_spec(), self.len_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureParamAndLocalXAPayloadFmt {
        type Val = CaptureParamAndLocalXAPayloadSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.choice2_spec(), self.len_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureParamAndLocalXAPayloadFmt {
        type SValue = CaptureParamAndLocalXAPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.choice2_spec(), self.len_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureParamAndLocalXAPayloadFmt {
        type SVal = CaptureParamAndLocalXAPayloadSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.choice2_spec(), self.len_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureParamAndLocalXAPayloadFmt {
        type T = CaptureParamAndLocalXAPayloadSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.choice2_spec(), self.len_spec()).byte_len(v)
        }
    }

    impl SpecParser for CaptureParamAndLocalXAFmt {
        type PVal = CaptureParamAndLocalXASpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.choice2_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureParamAndLocalXAFmt {
        type Val = CaptureParamAndLocalXASpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.choice2_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureParamAndLocalXAFmt {
        type SValue = CaptureParamAndLocalXASpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.choice2_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureParamAndLocalXAFmt {
        type SVal = CaptureParamAndLocalXASpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.choice2_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureParamAndLocalXAFmt {
        type T = CaptureParamAndLocalXASpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.choice2_spec()).byte_len(v)
        }
    }

    impl SpecParser for CaptureParamAndLocalXBYFmt {
        type PVal = CaptureParamAndLocalXBYSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.tag_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureParamAndLocalXBYFmt {
        type Val = CaptureParamAndLocalXBYSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.tag_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureParamAndLocalXBYFmt {
        type SValue = CaptureParamAndLocalXBYSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureParamAndLocalXBYFmt {
        type SVal = CaptureParamAndLocalXBYSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.tag_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureParamAndLocalXBYFmt {
        type T = CaptureParamAndLocalXBYSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.tag_spec()).byte_len(v)
        }
    }

    impl SpecParser for CaptureParamAndLocalXBFmt {
        type PVal = CaptureParamAndLocalXBSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureParamAndLocalXBFmt {
        type Val = CaptureParamAndLocalXBSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureParamAndLocalXBFmt {
        type SValue = CaptureParamAndLocalXBSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureParamAndLocalXBFmt {
        type SVal = CaptureParamAndLocalXBSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureParamAndLocalXBFmt {
        type T = CaptureParamAndLocalXBSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for CaptureParamAndLocalXFmt {
        type PVal = CaptureParamAndLocalXSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for CaptureParamAndLocalXFmt {
        type Val = CaptureParamAndLocalXSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for CaptureParamAndLocalXFmt {
        type SValue = CaptureParamAndLocalXSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for CaptureParamAndLocalXFmt {
        type SVal = CaptureParamAndLocalXSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for CaptureParamAndLocalXFmt {
        type T = CaptureParamAndLocalXSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).byte_len(v)
        }
    }

}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;

    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;

    impl SafeParser for AOrBFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<AOrBFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for AOrBFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<AOrBFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for AOrBFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<AOrBFmt as SpecParser>::spec_parse);
            reveal(<AOrBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AOrBFmt as SpecParser>::spec_parse);
            reveal(<AOrBFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for AOrBFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AOrBFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<AOrBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AOrBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for AOrBFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<AOrBFmt as SpecSerializer>::spec_serialize);
            reveal(<AOrBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for AOrBFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<AOrBFmt as SpecParser>::spec_parse);
            reveal(<AOrBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AOrBFmt as Consistency>::consistent);
            reveal(<AOrBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AOrBFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AOrBFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for AOrBFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<AOrBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AOrBFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for AOrBFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<AOrBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<AOrBFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for COrDFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<COrDFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for COrDFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<COrDFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for COrDFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<COrDFmt as SpecParser>::spec_parse);
            reveal(<COrDFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<COrDFmt as SpecParser>::spec_parse);
            reveal(<COrDFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for COrDFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<COrDFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<COrDFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<COrDFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for COrDFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<COrDFmt as SpecSerializer>::spec_serialize);
            reveal(<COrDFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for COrDFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<COrDFmt as SpecParser>::spec_parse);
            reveal(<COrDFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<COrDFmt as Consistency>::consistent);
            reveal(<COrDFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for COrDFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<COrDFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for COrDFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<COrDFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<COrDFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for COrDFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<COrDFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<COrDFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for NestedInnerStructFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for NestedInnerStructFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for NestedInnerStructFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerStructFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerStructFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for NestedInnerStructFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerStructFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for NestedInnerStructFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<NestedInnerStructFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedInnerStructFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for NestedInnerStructFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerStructFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerStructFmt as Consistency>::consistent);
            reveal(<NestedInnerStructFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedInnerStructFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for NestedInnerStructFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerStructFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for NestedInnerStructFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<NestedInnerStructFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerStructFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for NestedInnerChoiceFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for NestedInnerChoiceFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for NestedInnerChoiceFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for NestedInnerChoiceFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for NestedInnerChoiceFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<NestedInnerChoiceFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedInnerChoiceFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for NestedInnerChoiceFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceFmt as Consistency>::consistent);
            reveal(<NestedInnerChoiceFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedInnerChoiceFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for NestedInnerChoiceFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for NestedInnerChoiceFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<NestedInnerChoiceFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureOuterAndLocalFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureOuterAndLocalFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureOuterAndLocalFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureOuterAndLocalFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureOuterAndLocalFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureOuterAndLocalFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureOuterAndLocalFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureOuterAndLocalFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalFmt as Consistency>::consistent);
            reveal(<CaptureOuterAndLocalFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureOuterAndLocalFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureOuterAndLocalFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureOuterAndLocalFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureOuterAndLocalFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureLocalInAnonStructFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureLocalInAnonStructFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureLocalInAnonStructFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureLocalInAnonStructFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureLocalInAnonStructFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureLocalInAnonStructFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureLocalInAnonStructFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureLocalInAnonStructFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureLocalInAnonStructFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureLocalInAnonStructFmt as Consistency>::consistent);
            reveal(<CaptureLocalInAnonStructFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureLocalInAnonStructFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureLocalInAnonStructFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureLocalInAnonStructFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureLocalInAnonStructFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureLocalInAnonStructFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureLocalInAnonStructFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureParamAndLocalFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureParamAndLocalFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureParamAndLocalFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureParamAndLocalFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureParamAndLocalFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureParamAndLocalFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalFmt as Consistency>::consistent);
            reveal(<CaptureParamAndLocalFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureParamAndLocalFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureParamAndLocalFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for NestedInnerStructValFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerStructValFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for NestedInnerStructValFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<NestedInnerStructValFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for NestedInnerStructValFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerStructValFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerStructValFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerStructValFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerStructValFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for NestedInnerStructValFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<NestedInnerStructValFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedInnerStructValFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for NestedInnerStructValFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<NestedInnerStructValFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerStructValFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerStructValFmt as Consistency>::consistent);
            reveal(<NestedInnerStructValFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedInnerStructValFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedInnerStructValFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for NestedInnerStructValFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<NestedInnerStructValFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerStructValFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for NestedInnerChoiceXAFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.choice2_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for NestedInnerChoiceXAFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.choice2_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for NestedInnerChoiceXAFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceXAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceXAFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for NestedInnerChoiceXAFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceXAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for NestedInnerChoiceXAFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<NestedInnerChoiceXAFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedInnerChoiceXAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for NestedInnerChoiceXAFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceXAFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceXAFmt as Consistency>::consistent);
            reveal(<NestedInnerChoiceXAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedInnerChoiceXAFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for NestedInnerChoiceXAFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceXAFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for NestedInnerChoiceXAFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<NestedInnerChoiceXAFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceXAFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for NestedInnerChoiceXFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for NestedInnerChoiceXFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for NestedInnerChoiceXFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceXFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceXFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for NestedInnerChoiceXFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceXFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for NestedInnerChoiceXFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<NestedInnerChoiceXFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedInnerChoiceXFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for NestedInnerChoiceXFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceXFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceXFmt as Consistency>::consistent);
            reveal(<NestedInnerChoiceXFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedInnerChoiceXFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for NestedInnerChoiceXFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceXFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for NestedInnerChoiceXFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<NestedInnerChoiceXFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<NestedInnerChoiceXFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(
                <CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecSerializerDps>::spec_serialize_dps,
            );
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(
                <CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecParser>::spec_parse);
            reveal(
                <CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as Consistency>::consistent);
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(
                <CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(
                <CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureOuterAndLocalPayloadBodyFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.frame_len_spec(), self.tag_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureOuterAndLocalPayloadBodyFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.frame_len_spec(), self.tag_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureOuterAndLocalPayloadBodyFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureOuterAndLocalPayloadBodyFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureOuterAndLocalPayloadBodyFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureOuterAndLocalPayloadBodyFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as Consistency>::consistent);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureOuterAndLocalPayloadBodyFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureOuterAndLocalPayloadBodyFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureOuterAndLocalPayloadBodyFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureOuterAndLocalPayloadFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.frame_len_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureOuterAndLocalPayloadFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.frame_len_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureOuterAndLocalPayloadFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureOuterAndLocalPayloadFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureOuterAndLocalPayloadFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureOuterAndLocalPayloadFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalPayloadFmt as Consistency>::consistent);
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureOuterAndLocalPayloadFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureOuterAndLocalPayloadFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureOuterAndLocalPayloadFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(
                <CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializerDps>::spec_serialize_dps,
            );
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(
                <CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(
                <CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializer>::spec_serialize,
            );
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser>::spec_parse);
            reveal(
                <CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as Consistency>::consistent);
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(
                <CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(
                <CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializer>::spec_serialize,
            );
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(
                <CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(
                <CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializer>::spec_serialize,
            );
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureLocalInAnonStructWrapperValueFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.tag_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureLocalInAnonStructWrapperValueFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.tag_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureLocalInAnonStructWrapperValueFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureLocalInAnonStructWrapperValueFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(
                <CaptureLocalInAnonStructWrapperValueFmt as SpecSerializerDps>::spec_serialize_dps,
            );
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(
                <CaptureLocalInAnonStructWrapperValueFmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureLocalInAnonStructWrapperValueFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureLocalInAnonStructWrapperValueFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecParser>::spec_parse);
            reveal(
                <CaptureLocalInAnonStructWrapperValueFmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as Consistency>::consistent);
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureLocalInAnonStructWrapperValueFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureLocalInAnonStructWrapperValueFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(
                <CaptureLocalInAnonStructWrapperValueFmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureLocalInAnonStructWrapperValueFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(
                <CaptureLocalInAnonStructWrapperValueFmt as SpecSerializerDps>::spec_serialize_dps,
            );
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureLocalInAnonStructWrapperFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureLocalInAnonStructWrapperFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureLocalInAnonStructWrapperFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureLocalInAnonStructWrapperFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureLocalInAnonStructWrapperFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureLocalInAnonStructWrapperFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureLocalInAnonStructWrapperFmt as Consistency>::consistent);
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureLocalInAnonStructWrapperFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureLocalInAnonStructWrapperFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureLocalInAnonStructWrapperFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureParamAndLocalXAPayloadFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.choice2_spec(), self.len_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureParamAndLocalXAPayloadFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.choice2_spec(), self.len_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureParamAndLocalXAPayloadFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXAPayloadFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureParamAndLocalXAPayloadFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureParamAndLocalXAPayloadFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureParamAndLocalXAPayloadFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXAPayloadFmt as Consistency>::consistent);
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalXAPayloadFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureParamAndLocalXAPayloadFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureParamAndLocalXAPayloadFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureParamAndLocalXAFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.choice2_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureParamAndLocalXAFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.choice2_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureParamAndLocalXAFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXAFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureParamAndLocalXAFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureParamAndLocalXAFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalXAFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalXAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureParamAndLocalXAFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXAFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXAFmt as Consistency>::consistent);
            reveal(<CaptureParamAndLocalXAFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalXAFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureParamAndLocalXAFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXAFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureParamAndLocalXAFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalXAFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXAFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureParamAndLocalXBYFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.tag_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureParamAndLocalXBYFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.tag_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureParamAndLocalXBYFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXBYFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXBYFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureParamAndLocalXBYFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXBYFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureParamAndLocalXBYFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalXBYFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureParamAndLocalXBYFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXBYFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXBYFmt as Consistency>::consistent);
            reveal(<CaptureParamAndLocalXBYFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalXBYFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureParamAndLocalXBYFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXBYFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureParamAndLocalXBYFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXBYFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.tag_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureParamAndLocalXBFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureParamAndLocalXBFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureParamAndLocalXBFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXBFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureParamAndLocalXBFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureParamAndLocalXBFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalXBFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalXBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureParamAndLocalXBFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXBFmt as Consistency>::consistent);
            reveal(<CaptureParamAndLocalXBFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalXBFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureParamAndLocalXBFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXBFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureParamAndLocalXBFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalXBFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXBFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for CaptureParamAndLocalXFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for CaptureParamAndLocalXFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.choice1_spec(), self.choice2_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for CaptureParamAndLocalXFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for CaptureParamAndLocalXFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for CaptureParamAndLocalXFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalXFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalXFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for CaptureParamAndLocalXFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXFmt as Consistency>::consistent);
            reveal(<CaptureParamAndLocalXFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalXFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for CaptureParamAndLocalXFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for CaptureParamAndLocalXFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<CaptureParamAndLocalXFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<CaptureParamAndLocalXFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
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

    impl<'i> Parser<&'i [u8]> for AOrBFmt {
        type PT = AOrB;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<AOrBFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                1 => AOrB::A,
                2 => AOrB::B,
                _ => return Err(ParseError::invalid_tag()),
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
            Ok((n, enum_val))
        }
    }

    impl<'i> Serializer<AOrB> for AOrBFmt {
        fn serialize(&self, v: &AOrB, obuf: &mut Vec<u8>) {
            reveal(<AOrBFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                AOrB::A => 1,
                AOrB::B => 2,
            };
            U8.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<AOrB> for AOrBFmt {
        fn prepare(&self, v: &AOrB) -> Result<usize, PreSerializeError> {
            reveal(<AOrBFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                AOrB::A => 1,
                AOrB::B => 2,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for COrDFmt {
        type PT = COrD;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<COrDFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                1 => COrD::C,
                2 => COrD::D,
                _ => return Err(ParseError::invalid_tag()),
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
            Ok((n, enum_val))
        }
    }

    impl<'i> Serializer<COrD> for COrDFmt {
        fn serialize(&self, v: &COrD, obuf: &mut Vec<u8>) {
            reveal(<COrDFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                COrD::C => 1,
                COrD::D => 2,
            };
            U8.serialize(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<COrD> for COrDFmt {
        fn prepare(&self, v: &COrD) -> Result<usize, PreSerializeError> {
            reveal(<COrDFmt as SpecByteLen>::byte_len);
            let tag = match *v {
                COrD::C => 1,
                COrD::D => 2,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }

    impl<'i> Parser<&'i [u8]> for NestedInnerStructFmt {
        type PT = NestedInnerStruct<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NestedInnerStructFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, len) = (U32Le).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, val) = (ExactLen(
                len,
                Named("nested_inner_struct_val", NestedInnerStructValFmt),
            )).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = NestedInnerStruct { len, val };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<NestedInnerStruct<'i>> for NestedInnerStructFmt {
        fn serialize(&self, v: &NestedInnerStruct<'i>, obuf: &mut Vec<u8>) {
            reveal(<NestedInnerStructFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let NestedInnerStruct { len, val } = v;
            U32Le.serialize(len, obuf);
            ExactLen(len, NestedInnerStructValFmt).serialize(val, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedInnerStruct<'i>> for NestedInnerStructFmt {
        fn prepare(&self, v: &NestedInnerStruct<'i>) -> Result<usize, PreSerializeError> {
            reveal(<NestedInnerStructFmt as SpecByteLen>::byte_len);
            let NestedInnerStruct { len, val } = v;
            let l1 = (U32Le).prepare(len)?;
            let l2 = (ExactLen(
                len,
                Named("nested_inner_struct_val", NestedInnerStructValFmt),
            )).prepare(val)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for NestedInnerChoiceFmt {
        type PT = NestedInnerChoice;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NestedInnerChoiceFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, x) = (Named(
                "nested_inner_choice_x",
                NestedInnerChoiceXFmt { choice1: self.choice1, choice2: self.choice2 },
            )).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = NestedInnerChoice { x };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<NestedInnerChoice> for NestedInnerChoiceFmt {
        fn serialize(&self, v: &NestedInnerChoice, obuf: &mut Vec<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let NestedInnerChoice { x } = v;
            NestedInnerChoiceXFmt { choice1: self.choice1, choice2: self.choice2 }.serialize(
                x,
                obuf,
            );

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedInnerChoice> for NestedInnerChoiceFmt {
        fn prepare(&self, v: &NestedInnerChoice) -> Result<usize, PreSerializeError> {
            reveal(<NestedInnerChoiceFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let NestedInnerChoice { x } = v;
            let l1 = (Named(
                "nested_inner_choice_x",
                NestedInnerChoiceXFmt { choice1: self.choice1, choice2: self.choice2 },
            )).prepare(x)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureOuterAndLocalFmt {
        type PT = CaptureOuterAndLocal<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureOuterAndLocalFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, frame_len) = (U8).parse(&rest)?;
            if !(frame_len >= 1) {
                return Err(ParseError::predicate_failed());
            }
            let rest = rest.skip(n1);
            let (n2, payload) = (ExactLen(
                frame_len,
                Named(
                    "capture_outer_and_local_payload",
                    CaptureOuterAndLocalPayloadFmt { frame_len: frame_len },
                ),
            )).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = CaptureOuterAndLocal { frame_len, payload };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<CaptureOuterAndLocal<'i>> for CaptureOuterAndLocalFmt {
        fn serialize(&self, v: &CaptureOuterAndLocal<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let CaptureOuterAndLocal { frame_len, payload } = v;
            U8.serialize(frame_len, obuf);
            ExactLen(frame_len, CaptureOuterAndLocalPayloadFmt { frame_len: *frame_len }).serialize(
                payload,
                obuf,
            );

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureOuterAndLocal<'i>> for CaptureOuterAndLocalFmt {
        fn prepare(&self, v: &CaptureOuterAndLocal<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureOuterAndLocalFmt as SpecByteLen>::byte_len);
            let CaptureOuterAndLocal { frame_len, payload } = v;
            let l1 = {
                if !(*frame_len >= 1) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (U8).prepare(frame_len)
                }
            }?;
            let l2 = (ExactLen(
                frame_len,
                Named(
                    "capture_outer_and_local_payload",
                    CaptureOuterAndLocalPayloadFmt { frame_len: *frame_len },
                ),
            )).prepare(payload)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureLocalInAnonStructFmt {
        type PT = CaptureLocalInAnonStruct<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureLocalInAnonStructFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, wrapper) = (Named(
                "capture_local_in_anon_struct_wrapper",
                CaptureLocalInAnonStructWrapperFmt,
            )).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = CaptureLocalInAnonStruct { wrapper };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<CaptureLocalInAnonStruct<'i>> for CaptureLocalInAnonStructFmt {
        fn serialize(&self, v: &CaptureLocalInAnonStruct<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let CaptureLocalInAnonStruct { wrapper } = v;
            CaptureLocalInAnonStructWrapperFmt.serialize(wrapper, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureLocalInAnonStruct<'i>> for CaptureLocalInAnonStructFmt {
        fn prepare(&self, v: &CaptureLocalInAnonStruct<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureLocalInAnonStructFmt as SpecByteLen>::byte_len);
            let CaptureLocalInAnonStruct { wrapper } = v;
            let l1 = (Named(
                "capture_local_in_anon_struct_wrapper",
                CaptureLocalInAnonStructWrapperFmt,
            )).prepare(wrapper)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureParamAndLocalFmt {
        type PT = CaptureParamAndLocal<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureParamAndLocalFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, x) = (Named(
                "capture_param_and_local_x",
                CaptureParamAndLocalXFmt { choice1: self.choice1, choice2: self.choice2 },
            )).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = CaptureParamAndLocal { x };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<CaptureParamAndLocal<'i>> for CaptureParamAndLocalFmt {
        fn serialize(&self, v: &CaptureParamAndLocal<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let CaptureParamAndLocal { x } = v;
            CaptureParamAndLocalXFmt { choice1: self.choice1, choice2: self.choice2 }.serialize(
                x,
                obuf,
            );

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocal<'i>> for CaptureParamAndLocalFmt {
        fn prepare(&self, v: &CaptureParamAndLocal<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureParamAndLocalFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let CaptureParamAndLocal { x } = v;
            let l1 = (Named(
                "capture_param_and_local_x",
                CaptureParamAndLocalXFmt { choice1: self.choice1, choice2: self.choice2 },
            )).prepare(x)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for NestedInnerStructValFmt {
        type PT = NestedInnerStructVal<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NestedInnerStructValFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, x) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, y) = (Tail).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = NestedInnerStructVal { x, y };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<NestedInnerStructVal<'i>> for NestedInnerStructValFmt {
        fn serialize(&self, v: &NestedInnerStructVal<'i>, obuf: &mut Vec<u8>) {
            reveal(<NestedInnerStructValFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let NestedInnerStructVal { x, y } = v;
            U8.serialize(x, obuf);
            Tail.serialize(y, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedInnerStructVal<'i>> for NestedInnerStructValFmt {
        fn prepare(&self, v: &NestedInnerStructVal<'i>) -> Result<usize, PreSerializeError> {
            reveal(<NestedInnerStructValFmt as SpecByteLen>::byte_len);
            let NestedInnerStructVal { x, y } = v;
            let l1 = (U8).prepare(x)?;
            let l2 = (Tail).prepare(y)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for NestedInnerChoiceXAFmt {
        type PT = NestedInnerChoiceXA;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<NestedInnerChoiceXAFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.choice2 {
                COrD::C => {
                    let (n, v) = (U8).parse(&rest)?;
                    (n, NestedInnerChoiceXA::C(v))
                },
                COrD::D => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, NestedInnerChoiceXA::D(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<NestedInnerChoiceXA> for NestedInnerChoiceXAFmt {
        fn serialize(&self, v: &NestedInnerChoiceXA, obuf: &mut Vec<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.choice2, v) {
                (COrD::C, NestedInnerChoiceXA::C(v)) => {
                    (U8).serialize(v, obuf);
                },
                (COrD::D, NestedInnerChoiceXA::D(v)) => {
                    (U16Le).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedInnerChoiceXA> for NestedInnerChoiceXAFmt {
        fn prepare(&self, v: &NestedInnerChoiceXA) -> Result<usize, PreSerializeError> {
            reveal(<NestedInnerChoiceXAFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.choice2, v) {
                (COrD::C, NestedInnerChoiceXA::C(v)) => (U8).prepare(v),
                (COrD::D, NestedInnerChoiceXA::D(v)) => (U16Le).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for NestedInnerChoiceXFmt {
        type PT = NestedInnerChoiceX;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<NestedInnerChoiceXFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.choice1 {
                AOrB::A => {
                    let (n, v) = (Named(
                        "nested_inner_choice_x_a",
                        NestedInnerChoiceXAFmt { choice2: self.choice2 },
                    )).parse(&rest)?;
                    (n, NestedInnerChoiceX::A(v))
                },
                AOrB::B => {
                    let (n, v) = (U32Le).parse(&rest)?;
                    (n, NestedInnerChoiceX::B(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<NestedInnerChoiceX> for NestedInnerChoiceXFmt {
        fn serialize(&self, v: &NestedInnerChoiceX, obuf: &mut Vec<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.choice1, v) {
                (AOrB::A, NestedInnerChoiceX::A(v)) => {
                    (NestedInnerChoiceXAFmt { choice2: self.choice2 }).serialize(v, obuf);
                },
                (AOrB::B, NestedInnerChoiceX::B(v)) => {
                    (U32Le).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedInnerChoiceX> for NestedInnerChoiceXFmt {
        fn prepare(&self, v: &NestedInnerChoiceX) -> Result<usize, PreSerializeError> {
            reveal(<NestedInnerChoiceXFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.choice1, v) {
                (AOrB::A, NestedInnerChoiceX::A(v)) => (Named(
                    "nested_inner_choice_x_a",
                    NestedInnerChoiceXAFmt { choice2: self.choice2 },
                )).prepare(v),
                (AOrB::B, NestedInnerChoiceX::B(v)) => (U32Le).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        type PT = CaptureOuterAndLocalPayloadBodyChoice1<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, count) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, items) = (Varied(count)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = CaptureOuterAndLocalPayloadBodyChoice1 { count, items };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<
        CaptureOuterAndLocalPayloadBodyChoice1<'i>,
    > for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        fn serialize(&self, v: &CaptureOuterAndLocalPayloadBodyChoice1<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let CaptureOuterAndLocalPayloadBodyChoice1 { count, items } = v;
            U8.serialize(count, obuf);
            Varied(count).serialize(items, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<
        CaptureOuterAndLocalPayloadBodyChoice1<'i>,
    > for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        fn prepare(&self, v: &CaptureOuterAndLocalPayloadBodyChoice1<'i>) -> Result<
            usize,
            PreSerializeError,
        > {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecByteLen>::byte_len);
            let CaptureOuterAndLocalPayloadBodyChoice1 { count, items } = v;
            let l1 = (U8).prepare(count)?;
            let l2 = (Varied(count)).prepare(items)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureOuterAndLocalPayloadBodyFmt {
        type PT = CaptureOuterAndLocalPayloadBody<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.tag {
                0 => {
                    let (n, v) = (Varied((self.frame_len - 1))).parse(&rest)?;
                    (n, CaptureOuterAndLocalPayloadBody::Variant1(v))
                },
                _ => {
                    let (n, v) = (Named(
                        "capture_outer_and_local_payload_body_choice1",
                        CaptureOuterAndLocalPayloadBodyChoice1Fmt,
                    )).parse(&rest)?;
                    (n, CaptureOuterAndLocalPayloadBody::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<
        CaptureOuterAndLocalPayloadBody<'i>,
    > for CaptureOuterAndLocalPayloadBodyFmt {
        fn serialize(&self, v: &CaptureOuterAndLocalPayloadBody<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (0, CaptureOuterAndLocalPayloadBody::Variant1(v)) => {
                    (Varied((self.frame_len - 1))).serialize(v, obuf);
                },
                (_, CaptureOuterAndLocalPayloadBody::Default(v)) => {
                    (CaptureOuterAndLocalPayloadBodyChoice1Fmt).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureOuterAndLocalPayloadBody<'i>> for CaptureOuterAndLocalPayloadBodyFmt {
        fn prepare(&self, v: &CaptureOuterAndLocalPayloadBody<'i>) -> Result<
            usize,
            PreSerializeError,
        > {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.tag, v) {
                (0, CaptureOuterAndLocalPayloadBody::Variant1(v)) => (Varied(
                    (self.frame_len - 1),
                )).prepare(v),
                (x, CaptureOuterAndLocalPayloadBody::Default(v)) if !(x == 0) => (Named(
                    "capture_outer_and_local_payload_body_choice1",
                    CaptureOuterAndLocalPayloadBodyChoice1Fmt,
                )).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureOuterAndLocalPayloadFmt {
        type PT = CaptureOuterAndLocalPayload<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureOuterAndLocalPayloadFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, tag) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, body) = (Named(
                "capture_outer_and_local_payload_body",
                CaptureOuterAndLocalPayloadBodyFmt { frame_len: self.frame_len, tag: tag },
            )).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = CaptureOuterAndLocalPayload { tag, body };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<CaptureOuterAndLocalPayload<'i>> for CaptureOuterAndLocalPayloadFmt {
        fn serialize(&self, v: &CaptureOuterAndLocalPayload<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let CaptureOuterAndLocalPayload { tag, body } = v;
            U8.serialize(tag, obuf);
            CaptureOuterAndLocalPayloadBodyFmt { frame_len: self.frame_len, tag: *tag }.serialize(
                body,
                obuf,
            );

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureOuterAndLocalPayload<'i>> for CaptureOuterAndLocalPayloadFmt {
        fn prepare(&self, v: &CaptureOuterAndLocalPayload<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let CaptureOuterAndLocalPayload { tag, body } = v;
            let l1 = (U8).prepare(tag)?;
            let l2 = (Named(
                "capture_outer_and_local_payload_body",
                CaptureOuterAndLocalPayloadBodyFmt { frame_len: self.frame_len, tag: *tag },
            )).prepare(body)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        type PT = CaptureLocalInAnonStructWrapperValueChoice0<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, len) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, bytes) = (Varied(len)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = CaptureLocalInAnonStructWrapperValueChoice0 { len, bytes };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<
        CaptureLocalInAnonStructWrapperValueChoice0<'i>,
    > for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        fn serialize(
            &self,
            v: &CaptureLocalInAnonStructWrapperValueChoice0<'i>,
            obuf: &mut Vec<u8>,
        ) {
            reveal(
                <CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializer>::spec_serialize,
            );
            let ghost old_obuf = obuf@;

            let CaptureLocalInAnonStructWrapperValueChoice0 { len, bytes } = v;
            U8.serialize(len, obuf);
            Varied(len).serialize(bytes, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<
        CaptureLocalInAnonStructWrapperValueChoice0<'i>,
    > for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        fn prepare(&self, v: &CaptureLocalInAnonStructWrapperValueChoice0<'i>) -> Result<
            usize,
            PreSerializeError,
        > {
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecByteLen>::byte_len);
            let CaptureLocalInAnonStructWrapperValueChoice0 { len, bytes } = v;
            let l1 = (U8).prepare(len)?;
            let l2 = (Varied(len)).prepare(bytes)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureLocalInAnonStructWrapperValueFmt {
        type PT = CaptureLocalInAnonStructWrapperValue<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.tag {
                0 => {
                    let (n, v) = (Named(
                        "capture_local_in_anon_struct_wrapper_value_choice0",
                        CaptureLocalInAnonStructWrapperValueChoice0Fmt,
                    )).parse(&rest)?;
                    (n, CaptureLocalInAnonStructWrapperValue::Variant1(v))
                },
                _ => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, CaptureLocalInAnonStructWrapperValue::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<
        CaptureLocalInAnonStructWrapperValue<'i>,
    > for CaptureLocalInAnonStructWrapperValueFmt {
        fn serialize(&self, v: &CaptureLocalInAnonStructWrapperValue<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (0, CaptureLocalInAnonStructWrapperValue::Variant1(v)) => {
                    (CaptureLocalInAnonStructWrapperValueChoice0Fmt).serialize(v, obuf);
                },
                (_, CaptureLocalInAnonStructWrapperValue::Default(v)) => {
                    (U16Le).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<
        CaptureLocalInAnonStructWrapperValue<'i>,
    > for CaptureLocalInAnonStructWrapperValueFmt {
        fn prepare(&self, v: &CaptureLocalInAnonStructWrapperValue<'i>) -> Result<
            usize,
            PreSerializeError,
        > {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.tag, v) {
                (0, CaptureLocalInAnonStructWrapperValue::Variant1(v)) => (Named(
                    "capture_local_in_anon_struct_wrapper_value_choice0",
                    CaptureLocalInAnonStructWrapperValueChoice0Fmt,
                )).prepare(v),
                (x, CaptureLocalInAnonStructWrapperValue::Default(v)) if !(x == 0) => (
                U16Le).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureLocalInAnonStructWrapperFmt {
        type PT = CaptureLocalInAnonStructWrapper<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, tag) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, value) = (Named(
                "capture_local_in_anon_struct_wrapper_value",
                CaptureLocalInAnonStructWrapperValueFmt { tag: tag },
            )).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = CaptureLocalInAnonStructWrapper { tag, value };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<
        CaptureLocalInAnonStructWrapper<'i>,
    > for CaptureLocalInAnonStructWrapperFmt {
        fn serialize(&self, v: &CaptureLocalInAnonStructWrapper<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let CaptureLocalInAnonStructWrapper { tag, value } = v;
            U8.serialize(tag, obuf);
            CaptureLocalInAnonStructWrapperValueFmt { tag: *tag }.serialize(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureLocalInAnonStructWrapper<'i>> for CaptureLocalInAnonStructWrapperFmt {
        fn prepare(&self, v: &CaptureLocalInAnonStructWrapper<'i>) -> Result<
            usize,
            PreSerializeError,
        > {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecByteLen>::byte_len);
            let CaptureLocalInAnonStructWrapper { tag, value } = v;
            let l1 = (U8).prepare(tag)?;
            let l2 = (Named(
                "capture_local_in_anon_struct_wrapper_value",
                CaptureLocalInAnonStructWrapperValueFmt { tag: *tag },
            )).prepare(value)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureParamAndLocalXAPayloadFmt {
        type PT = CaptureParamAndLocalXAPayload<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.choice2 {
                COrD::C => {
                    let (n, v) = (Varied(self.len)).parse(&rest)?;
                    (n, CaptureParamAndLocalXAPayload::C(v))
                },
                COrD::D => {
                    let (n, v) = (Varied(self.len)).parse(&rest)?;
                    (n, CaptureParamAndLocalXAPayload::D(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<CaptureParamAndLocalXAPayload<'i>> for CaptureParamAndLocalXAPayloadFmt {
        fn serialize(&self, v: &CaptureParamAndLocalXAPayload<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.choice2, v) {
                (COrD::C, CaptureParamAndLocalXAPayload::C(v)) => {
                    (Varied(self.len)).serialize(v, obuf);
                },
                (COrD::D, CaptureParamAndLocalXAPayload::D(v)) => {
                    (Varied(self.len)).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocalXAPayload<'i>> for CaptureParamAndLocalXAPayloadFmt {
        fn prepare(&self, v: &CaptureParamAndLocalXAPayload<'i>) -> Result<
            usize,
            PreSerializeError,
        > {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.choice2, v) {
                (COrD::C, CaptureParamAndLocalXAPayload::C(v)) => (Varied(self.len)).prepare(v),
                (COrD::D, CaptureParamAndLocalXAPayload::D(v)) => (Varied(self.len)).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureParamAndLocalXAFmt {
        type PT = CaptureParamAndLocalXA<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureParamAndLocalXAFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n1, len) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, payload) = (Named(
                "capture_param_and_local_x_a_payload",
                CaptureParamAndLocalXAPayloadFmt { choice2: self.choice2, len: len },
            )).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = CaptureParamAndLocalXA { len, payload };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<CaptureParamAndLocalXA<'i>> for CaptureParamAndLocalXAFmt {
        fn serialize(&self, v: &CaptureParamAndLocalXA<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let CaptureParamAndLocalXA { len, payload } = v;
            U8.serialize(len, obuf);
            CaptureParamAndLocalXAPayloadFmt { choice2: self.choice2, len: *len }.serialize(
                payload,
                obuf,
            );

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocalXA<'i>> for CaptureParamAndLocalXAFmt {
        fn prepare(&self, v: &CaptureParamAndLocalXA<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureParamAndLocalXAFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            let CaptureParamAndLocalXA { len, payload } = v;
            let l1 = (U8).prepare(len)?;
            let l2 = (Named(
                "capture_param_and_local_x_a_payload",
                CaptureParamAndLocalXAPayloadFmt { choice2: self.choice2, len: *len },
            )).prepare(payload)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureParamAndLocalXBYFmt {
        type PT = CaptureParamAndLocalXBY;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<CaptureParamAndLocalXBYFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.tag {
                0 => {
                    let (n, v) = (U8).parse(&rest)?;
                    (n, CaptureParamAndLocalXBY::Variant1(v))
                },
                _ => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, CaptureParamAndLocalXBY::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<CaptureParamAndLocalXBY> for CaptureParamAndLocalXBYFmt {
        fn serialize(&self, v: &CaptureParamAndLocalXBY, obuf: &mut Vec<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (0, CaptureParamAndLocalXBY::Variant1(v)) => {
                    (U8).serialize(v, obuf);
                },
                (_, CaptureParamAndLocalXBY::Default(v)) => {
                    (U16Le).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocalXBY> for CaptureParamAndLocalXBYFmt {
        fn prepare(&self, v: &CaptureParamAndLocalXBY) -> Result<usize, PreSerializeError> {
            reveal(<CaptureParamAndLocalXBYFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.tag, v) {
                (0, CaptureParamAndLocalXBY::Variant1(v)) => (U8).prepare(v),
                (x, CaptureParamAndLocalXBY::Default(v)) if !(x == 0) => (U16Le).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureParamAndLocalXBFmt {
        type PT = CaptureParamAndLocalXB;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureParamAndLocalXBFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, tag) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, y) = (Named(
                "capture_param_and_local_x_b_y",
                CaptureParamAndLocalXBYFmt { tag: tag },
            )).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = CaptureParamAndLocalXB { tag, y };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<'i> Serializer<CaptureParamAndLocalXB> for CaptureParamAndLocalXBFmt {
        fn serialize(&self, v: &CaptureParamAndLocalXB, obuf: &mut Vec<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecSerializer>::spec_serialize);
            let ghost old_obuf = obuf@;

            let CaptureParamAndLocalXB { tag, y } = v;
            U8.serialize(tag, obuf);
            CaptureParamAndLocalXBYFmt { tag: *tag }.serialize(y, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocalXB> for CaptureParamAndLocalXBFmt {
        fn prepare(&self, v: &CaptureParamAndLocalXB) -> Result<usize, PreSerializeError> {
            reveal(<CaptureParamAndLocalXBFmt as SpecByteLen>::byte_len);
            let CaptureParamAndLocalXB { tag, y } = v;
            let l1 = (U8).prepare(tag)?;
            let l2 = (Named(
                "capture_param_and_local_x_b_y",
                CaptureParamAndLocalXBYFmt { tag: *tag },
            )).prepare(y)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureParamAndLocalXFmt {
        type PT = CaptureParamAndLocalX<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<CaptureParamAndLocalXFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.choice1 {
                AOrB::A => {
                    let (n, v) = (Named(
                        "capture_param_and_local_x_a",
                        CaptureParamAndLocalXAFmt { choice2: self.choice2 },
                    )).parse(&rest)?;
                    (n, CaptureParamAndLocalX::A(v))
                },
                AOrB::B => {
                    let (n, v) = (Named(
                        "capture_param_and_local_x_b",
                        CaptureParamAndLocalXBFmt,
                    )).parse(&rest)?;
                    (n, CaptureParamAndLocalX::B(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<'i> Serializer<CaptureParamAndLocalX<'i>> for CaptureParamAndLocalXFmt {
        fn serialize(&self, v: &CaptureParamAndLocalX<'i>, obuf: &mut Vec<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecSerializer>::spec_serialize);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.choice1, v) {
                (AOrB::A, CaptureParamAndLocalX::A(v)) => {
                    (CaptureParamAndLocalXAFmt { choice2: self.choice2 }).serialize(v, obuf);
                },
                (AOrB::B, CaptureParamAndLocalX::B(v)) => {
                    (CaptureParamAndLocalXBFmt).serialize(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocalX<'i>> for CaptureParamAndLocalXFmt {
        fn prepare(&self, v: &CaptureParamAndLocalX<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureParamAndLocalXFmt as SpecByteLen>::byte_len);
            proof {
                use_type_invariant(self);
            }

            match (self.choice1, v) {
                (AOrB::A, CaptureParamAndLocalX::A(v)) => (Named(
                    "capture_param_and_local_x_a",
                    CaptureParamAndLocalXAFmt { choice2: self.choice2 },
                )).prepare(v),
                (AOrB::B, CaptureParamAndLocalX::B(v)) => (Named(
                    "capture_param_and_local_x_b",
                    CaptureParamAndLocalXBFmt,
                )).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}

} // verus!
