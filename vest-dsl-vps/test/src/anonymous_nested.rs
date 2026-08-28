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

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl AOrB {
    pub proof fn lemma_deep_view(&self)
        ensures
            self.deep_view() == *self,
    {
        reveal(<AOrB as DeepView>::deep_view);
    }

    pub open spec fn structural_valid(input: AOrBInner) -> bool {
        {
            let x = input;
            x == 1 || x == 2
        }
    }

    # [verifier::opaque]
    pub open spec fn from_structural(input: AOrBInner) -> Self {
        match input {
            1 => Self::A,
            2 => Self::B,
            _ => arbitrary(),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> AOrBInner {
        match self {
            Self::A => 1,
            Self::B => 2,
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(AOrB::from_structural);
        reveal(AOrB::into_structural);
        match self {
            Self::A => {},
            Self::B => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: AOrBInner)
        requires
            Self::structural_valid(input),
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(AOrB::from_structural);
        reveal(AOrB::into_structural);
        match input {
            1 => {},
            2 => {},
            _ => {
                assert(false);
            },
        }
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct AOrBForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct AOrBReverse;

impl SpecMap for AOrBForward {
    type Input = AOrBInner;

    type Output = AOrBSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        AOrB::from_structural(input)
    }
}

impl SpecMap for AOrBReverse {
    type Input = AOrBSpec;

    type Output = AOrBInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        *self
    }
}

impl COrD {
    pub proof fn lemma_deep_view(&self)
        ensures
            self.deep_view() == *self,
    {
        reveal(<COrD as DeepView>::deep_view);
    }

    pub open spec fn structural_valid(input: COrDInner) -> bool {
        {
            let x = input;
            x == 1 || x == 2
        }
    }

    # [verifier::opaque]
    pub open spec fn from_structural(input: COrDInner) -> Self {
        match input {
            1 => Self::C,
            2 => Self::D,
            _ => arbitrary(),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> COrDInner {
        match self {
            Self::C => 1,
            Self::D => 2,
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(COrD::from_structural);
        reveal(COrD::into_structural);
        match self {
            Self::C => {},
            Self::D => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: COrDInner)
        requires
            Self::structural_valid(input),
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(COrD::from_structural);
        reveal(COrD::into_structural);
        match input {
            1 => {},
            2 => {},
            _ => {
                assert(false);
            },
        }
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct COrDForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct COrDReverse;

impl SpecMap for COrDForward {
    type Input = COrDInner;

    type Output = COrDSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        COrD::from_structural(input)
    }
}

impl SpecMap for COrDReverse {
    type Input = COrDSpec;

    type Output = COrDInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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
pub struct NestedInnerStructSpec<T0 = u32, T1 = NestedInnerStructValSpec> {
    pub len: T0,
    pub val: T1,
}

pub type NestedInnerStructInner = (u32, NestedInnerStructValSpec);

impl<'i> DeepView for NestedInnerStruct<'i> {
    type V = NestedInnerStructSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        NestedInnerStructSpec { len: self.len.deep_view(), val: self.val.deep_view() }
    }
}

impl<'i> NestedInnerStruct<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().len == self.len.deep_view(),
            self.deep_view().val == self.val.deep_view(),
    {
        reveal(<NestedInnerStruct as DeepView>::deep_view);
    }
}

impl<T0, T1> NestedInnerStructSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (len, val) = input;
        Self { len, val }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { len, val } = self;
        (len, val)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(NestedInnerStructSpec::from_structural);
        reveal(NestedInnerStructSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(NestedInnerStructSpec::from_structural);
        reveal(NestedInnerStructSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { len, val } => (len, val),
            },
    {
        reveal(NestedInnerStructSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedInnerStructForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedInnerStructReverse;

impl SpecMap for NestedInnerStructForward {
    type Input = NestedInnerStructInner;

    type Output = NestedInnerStructSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        NestedInnerStructSpec::from_structural(input)
    }
}

impl SpecMap for NestedInnerStructReverse {
    type Input = NestedInnerStructSpec;

    type Output = NestedInnerStructInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nested_inner_choice`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct NestedInnerChoice {
    pub x: NestedInnerChoiceX,
}

# [verifier::ext_equal]
pub struct NestedInnerChoiceSpec<T0 = NestedInnerChoiceXSpec> {
    pub x: T0,
}

pub type NestedInnerChoiceInner = NestedInnerChoiceXSpec;

impl DeepView for NestedInnerChoice {
    type V = NestedInnerChoiceSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        NestedInnerChoiceSpec { x: self.x.deep_view() }
    }
}

impl NestedInnerChoice {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().x == self.x.deep_view(),
    {
        reveal(<NestedInnerChoice as DeepView>::deep_view);
    }
}

impl<T0> NestedInnerChoiceSpec<T0> {
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
        reveal(NestedInnerChoiceSpec::from_structural);
        reveal(NestedInnerChoiceSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(NestedInnerChoiceSpec::from_structural);
        reveal(NestedInnerChoiceSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { x } => x,
            },
    {
        reveal(NestedInnerChoiceSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedInnerChoiceForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedInnerChoiceReverse;

impl SpecMap for NestedInnerChoiceForward {
    type Input = NestedInnerChoiceInner;

    type Output = NestedInnerChoiceSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        NestedInnerChoiceSpec::from_structural(input)
    }
}

impl SpecMap for NestedInnerChoiceReverse {
    type Input = NestedInnerChoiceSpec;

    type Output = NestedInnerChoiceInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_outer_and_local`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureOuterAndLocal<'i> {
    pub frame_len: u8,
    pub payload: CaptureOuterAndLocalPayload<'i>,
}

# [verifier::ext_equal]
pub struct CaptureOuterAndLocalSpec<T0 = u8, T1 = CaptureOuterAndLocalPayloadSpec> {
    pub frame_len: T0,
    pub payload: T1,
}

pub type CaptureOuterAndLocalInner = (u8, CaptureOuterAndLocalPayloadSpec);

impl<'i> DeepView for CaptureOuterAndLocal<'i> {
    type V = CaptureOuterAndLocalSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CaptureOuterAndLocalSpec {
            frame_len: self.frame_len.deep_view(),
            payload: self.payload.deep_view(),
        }
    }
}

impl<'i> CaptureOuterAndLocal<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().frame_len == self.frame_len.deep_view(),
            self.deep_view().payload == self.payload.deep_view(),
    {
        reveal(<CaptureOuterAndLocal as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureOuterAndLocalSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (frame_len, payload) = input;
        Self { frame_len, payload }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { frame_len, payload } = self;
        (frame_len, payload)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CaptureOuterAndLocalSpec::from_structural);
        reveal(CaptureOuterAndLocalSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureOuterAndLocalSpec::from_structural);
        reveal(CaptureOuterAndLocalSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { frame_len, payload } => (frame_len, payload),
            },
    {
        reveal(CaptureOuterAndLocalSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureOuterAndLocalForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureOuterAndLocalReverse;

impl SpecMap for CaptureOuterAndLocalForward {
    type Input = CaptureOuterAndLocalInner;

    type Output = CaptureOuterAndLocalSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureOuterAndLocalSpec::from_structural(input)
    }
}

impl SpecMap for CaptureOuterAndLocalReverse {
    type Input = CaptureOuterAndLocalSpec;

    type Output = CaptureOuterAndLocalInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_local_in_anon_struct`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureLocalInAnonStruct<'i> {
    pub wrapper: CaptureLocalInAnonStructWrapper<'i>,
}

# [verifier::ext_equal]
pub struct CaptureLocalInAnonStructSpec<T0 = CaptureLocalInAnonStructWrapperSpec> {
    pub wrapper: T0,
}

pub type CaptureLocalInAnonStructInner = CaptureLocalInAnonStructWrapperSpec;

impl<'i> DeepView for CaptureLocalInAnonStruct<'i> {
    type V = CaptureLocalInAnonStructSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CaptureLocalInAnonStructSpec { wrapper: self.wrapper.deep_view() }
    }
}

impl<'i> CaptureLocalInAnonStruct<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().wrapper == self.wrapper.deep_view(),
    {
        reveal(<CaptureLocalInAnonStruct as DeepView>::deep_view);
    }
}

impl<T0> CaptureLocalInAnonStructSpec<T0> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let wrapper = input;
        Self { wrapper }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { wrapper } = self;
        wrapper
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CaptureLocalInAnonStructSpec::from_structural);
        reveal(CaptureLocalInAnonStructSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureLocalInAnonStructSpec::from_structural);
        reveal(CaptureLocalInAnonStructSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { wrapper } => wrapper,
            },
    {
        reveal(CaptureLocalInAnonStructSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureLocalInAnonStructForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureLocalInAnonStructReverse;

impl SpecMap for CaptureLocalInAnonStructForward {
    type Input = CaptureLocalInAnonStructInner;

    type Output = CaptureLocalInAnonStructSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureLocalInAnonStructSpec::from_structural(input)
    }
}

impl SpecMap for CaptureLocalInAnonStructReverse {
    type Input = CaptureLocalInAnonStructSpec;

    type Output = CaptureLocalInAnonStructInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_param_and_local`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureParamAndLocal<'i> {
    pub x: CaptureParamAndLocalX<'i>,
}

# [verifier::ext_equal]
pub struct CaptureParamAndLocalSpec<T0 = CaptureParamAndLocalXSpec> {
    pub x: T0,
}

pub type CaptureParamAndLocalInner = CaptureParamAndLocalXSpec;

impl<'i> DeepView for CaptureParamAndLocal<'i> {
    type V = CaptureParamAndLocalSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CaptureParamAndLocalSpec { x: self.x.deep_view() }
    }
}

impl<'i> CaptureParamAndLocal<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().x == self.x.deep_view(),
    {
        reveal(<CaptureParamAndLocal as DeepView>::deep_view);
    }
}

impl<T0> CaptureParamAndLocalSpec<T0> {
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
        reveal(CaptureParamAndLocalSpec::from_structural);
        reveal(CaptureParamAndLocalSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureParamAndLocalSpec::from_structural);
        reveal(CaptureParamAndLocalSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { x } => x,
            },
    {
        reveal(CaptureParamAndLocalSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalReverse;

impl SpecMap for CaptureParamAndLocalForward {
    type Input = CaptureParamAndLocalInner;

    type Output = CaptureParamAndLocalSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureParamAndLocalSpec::from_structural(input)
    }
}

impl SpecMap for CaptureParamAndLocalReverse {
    type Input = CaptureParamAndLocalSpec;

    type Output = CaptureParamAndLocalInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nested_inner_struct_val`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct NestedInnerStructVal<'i> {
    pub x: u8,
    pub y: &'i [u8],
}

# [verifier::ext_equal]
pub struct NestedInnerStructValSpec<T0 = u8, T1 = Seq<u8>> {
    pub x: T0,
    pub y: T1,
}

pub type NestedInnerStructValInner = (u8, Seq<u8>);

impl<'i> DeepView for NestedInnerStructVal<'i> {
    type V = NestedInnerStructValSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        NestedInnerStructValSpec { x: self.x.deep_view(), y: self.y.deep_view() }
    }
}

impl<'i> NestedInnerStructVal<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().x == self.x.deep_view(),
            self.deep_view().y == self.y.deep_view(),
    {
        reveal(<NestedInnerStructVal as DeepView>::deep_view);
    }
}

impl<T0, T1> NestedInnerStructValSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (x, y) = input;
        Self { x, y }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { x, y } = self;
        (x, y)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(NestedInnerStructValSpec::from_structural);
        reveal(NestedInnerStructValSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(NestedInnerStructValSpec::from_structural);
        reveal(NestedInnerStructValSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { x, y } => (x, y),
            },
    {
        reveal(NestedInnerStructValSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedInnerStructValForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedInnerStructValReverse;

impl SpecMap for NestedInnerStructValForward {
    type Input = NestedInnerStructValInner;

    type Output = NestedInnerStructValSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        NestedInnerStructValSpec::from_structural(input)
    }
}

impl SpecMap for NestedInnerStructValReverse {
    type Input = NestedInnerStructValSpec;

    type Output = NestedInnerStructValInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nested_inner_choice_x_a`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum NestedInnerChoiceXA {
    C(u8),
    D(u16),
}

# [verifier::ext_equal]
pub enum NestedInnerChoiceXASpec<T0 = u8, T1 = u16> {
    C(T0),
    D(T1),
}

pub type NestedInnerChoiceXAInner = Sum<u8, u16>;

impl DeepView for NestedInnerChoiceXA {
    type V = NestedInnerChoiceXASpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            NestedInnerChoiceXA::C(v) => NestedInnerChoiceXASpec::C(v.deep_view()),
            NestedInnerChoiceXA::D(v) => NestedInnerChoiceXASpec::D(v.deep_view()),
        }
    }
}

impl NestedInnerChoiceXA {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                NestedInnerChoiceXA::C(v) => NestedInnerChoiceXASpec::C(v.deep_view()),
                NestedInnerChoiceXA::D(v) => NestedInnerChoiceXASpec::D(v.deep_view()),
            },
    {
        reveal(<NestedInnerChoiceXA as DeepView>::deep_view);
    }
}

impl<T0, T1> NestedInnerChoiceXASpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, T1>) -> Self {
        match input {
            L(value) => Self::C(value),
            R(value) => Self::D(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, T1> {
        match self {
            Self::C(value) => L(value),
            Self::D(value) => R(value),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(NestedInnerChoiceXASpec::from_structural);
        reveal(NestedInnerChoiceXASpec::into_structural);
        match self {
            Self::C(_) => {},
            Self::D(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(NestedInnerChoiceXASpec::from_structural);
        reveal(NestedInnerChoiceXASpec::into_structural);
        match input {
            L(_) => {},
            R(_) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::C(value) => L(value),
                Self::D(value) => R(value),
            },
    {
        reveal(NestedInnerChoiceXASpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedInnerChoiceXAForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedInnerChoiceXAReverse;

impl SpecMap for NestedInnerChoiceXAForward {
    type Input = NestedInnerChoiceXAInner;

    type Output = NestedInnerChoiceXASpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        NestedInnerChoiceXASpec::from_structural(input)
    }
}

impl SpecMap for NestedInnerChoiceXAReverse {
    type Input = NestedInnerChoiceXASpec;

    type Output = NestedInnerChoiceXAInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nested_inner_choice_x`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum NestedInnerChoiceX {
    A(NestedInnerChoiceXA),
    B(u32),
}

# [verifier::ext_equal]
pub enum NestedInnerChoiceXSpec<T0 = NestedInnerChoiceXASpec, T1 = u32> {
    A(T0),
    B(T1),
}

pub type NestedInnerChoiceXInner = Sum<NestedInnerChoiceXASpec, u32>;

impl DeepView for NestedInnerChoiceX {
    type V = NestedInnerChoiceXSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            NestedInnerChoiceX::A(v) => NestedInnerChoiceXSpec::A(v.deep_view()),
            NestedInnerChoiceX::B(v) => NestedInnerChoiceXSpec::B(v.deep_view()),
        }
    }
}

impl NestedInnerChoiceX {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                NestedInnerChoiceX::A(v) => NestedInnerChoiceXSpec::A(v.deep_view()),
                NestedInnerChoiceX::B(v) => NestedInnerChoiceXSpec::B(v.deep_view()),
            },
    {
        reveal(<NestedInnerChoiceX as DeepView>::deep_view);
    }
}

impl<T0, T1> NestedInnerChoiceXSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, T1>) -> Self {
        match input {
            L(value) => Self::A(value),
            R(value) => Self::B(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, T1> {
        match self {
            Self::A(value) => L(value),
            Self::B(value) => R(value),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(NestedInnerChoiceXSpec::from_structural);
        reveal(NestedInnerChoiceXSpec::into_structural);
        match self {
            Self::A(_) => {},
            Self::B(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(NestedInnerChoiceXSpec::from_structural);
        reveal(NestedInnerChoiceXSpec::into_structural);
        match input {
            L(_) => {},
            R(_) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::A(value) => L(value),
                Self::B(value) => R(value),
            },
    {
        reveal(NestedInnerChoiceXSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedInnerChoiceXForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct NestedInnerChoiceXReverse;

impl SpecMap for NestedInnerChoiceXForward {
    type Input = NestedInnerChoiceXInner;

    type Output = NestedInnerChoiceXSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        NestedInnerChoiceXSpec::from_structural(input)
    }
}

impl SpecMap for NestedInnerChoiceXReverse {
    type Input = NestedInnerChoiceXSpec;

    type Output = NestedInnerChoiceXInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_outer_and_local_payload_body_choice1`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureOuterAndLocalPayloadBodyChoice1<'i> {
    pub count: u8,
    pub items: &'i [u8],
}

# [verifier::ext_equal]
pub struct CaptureOuterAndLocalPayloadBodyChoice1Spec<T0 = u8, T1 = Seq<u8>> {
    pub count: T0,
    pub items: T1,
}

pub type CaptureOuterAndLocalPayloadBodyChoice1Inner = (u8, Seq<u8>);

impl<'i> DeepView for CaptureOuterAndLocalPayloadBodyChoice1<'i> {
    type V = CaptureOuterAndLocalPayloadBodyChoice1Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CaptureOuterAndLocalPayloadBodyChoice1Spec {
            count: self.count.deep_view(),
            items: self.items.deep_view(),
        }
    }
}

impl<'i> CaptureOuterAndLocalPayloadBodyChoice1<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().count == self.count.deep_view(),
            self.deep_view().items == self.items.deep_view(),
    {
        reveal(<CaptureOuterAndLocalPayloadBodyChoice1 as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureOuterAndLocalPayloadBodyChoice1Spec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (count, items) = input;
        Self { count, items }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { count, items } = self;
        (count, items)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CaptureOuterAndLocalPayloadBodyChoice1Spec::from_structural);
        reveal(CaptureOuterAndLocalPayloadBodyChoice1Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureOuterAndLocalPayloadBodyChoice1Spec::from_structural);
        reveal(CaptureOuterAndLocalPayloadBodyChoice1Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { count, items } => (count, items),
            },
    {
        reveal(CaptureOuterAndLocalPayloadBodyChoice1Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureOuterAndLocalPayloadBodyChoice1Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureOuterAndLocalPayloadBodyChoice1Reverse;

impl SpecMap for CaptureOuterAndLocalPayloadBodyChoice1Forward {
    type Input = CaptureOuterAndLocalPayloadBodyChoice1Inner;

    type Output = CaptureOuterAndLocalPayloadBodyChoice1Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureOuterAndLocalPayloadBodyChoice1Spec::from_structural(input)
    }
}

impl SpecMap for CaptureOuterAndLocalPayloadBodyChoice1Reverse {
    type Input = CaptureOuterAndLocalPayloadBodyChoice1Spec;

    type Output = CaptureOuterAndLocalPayloadBodyChoice1Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_outer_and_local_payload_body`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum CaptureOuterAndLocalPayloadBody<'i> {
    Variant1(&'i [u8]),
    Default(CaptureOuterAndLocalPayloadBodyChoice1<'i>),
}

# [verifier::ext_equal]
pub enum CaptureOuterAndLocalPayloadBodySpec<
    T0 = Seq<u8>,
    T1 = CaptureOuterAndLocalPayloadBodyChoice1Spec,
> {
    Variant1(T0),
    Default(T1),
}

pub type CaptureOuterAndLocalPayloadBodyInner = Sum<
    Seq<u8>,
    CaptureOuterAndLocalPayloadBodyChoice1Spec,
>;

impl<'i> DeepView for CaptureOuterAndLocalPayloadBody<'i> {
    type V = CaptureOuterAndLocalPayloadBodySpec;

    # [verifier::opaque]
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

impl<'i> CaptureOuterAndLocalPayloadBody<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                CaptureOuterAndLocalPayloadBody::Variant1(
                    v,
                ) => CaptureOuterAndLocalPayloadBodySpec::Variant1(v.deep_view()),
                CaptureOuterAndLocalPayloadBody::Default(
                    v,
                ) => CaptureOuterAndLocalPayloadBodySpec::Default(v.deep_view()),
            },
    {
        reveal(<CaptureOuterAndLocalPayloadBody as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureOuterAndLocalPayloadBodySpec<T0, T1> {
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
        reveal(CaptureOuterAndLocalPayloadBodySpec::from_structural);
        reveal(CaptureOuterAndLocalPayloadBodySpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureOuterAndLocalPayloadBodySpec::from_structural);
        reveal(CaptureOuterAndLocalPayloadBodySpec::into_structural);
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
        reveal(CaptureOuterAndLocalPayloadBodySpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureOuterAndLocalPayloadBodyForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureOuterAndLocalPayloadBodyReverse;

impl SpecMap for CaptureOuterAndLocalPayloadBodyForward {
    type Input = CaptureOuterAndLocalPayloadBodyInner;

    type Output = CaptureOuterAndLocalPayloadBodySpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureOuterAndLocalPayloadBodySpec::from_structural(input)
    }
}

impl SpecMap for CaptureOuterAndLocalPayloadBodyReverse {
    type Input = CaptureOuterAndLocalPayloadBodySpec;

    type Output = CaptureOuterAndLocalPayloadBodyInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_outer_and_local_payload`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureOuterAndLocalPayload<'i> {
    pub tag: u8,
    pub body: CaptureOuterAndLocalPayloadBody<'i>,
}

# [verifier::ext_equal]
pub struct CaptureOuterAndLocalPayloadSpec<T0 = u8, T1 = CaptureOuterAndLocalPayloadBodySpec> {
    pub tag: T0,
    pub body: T1,
}

pub type CaptureOuterAndLocalPayloadInner = (u8, CaptureOuterAndLocalPayloadBodySpec);

impl<'i> DeepView for CaptureOuterAndLocalPayload<'i> {
    type V = CaptureOuterAndLocalPayloadSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CaptureOuterAndLocalPayloadSpec { tag: self.tag.deep_view(), body: self.body.deep_view() }
    }
}

impl<'i> CaptureOuterAndLocalPayload<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().tag == self.tag.deep_view(),
            self.deep_view().body == self.body.deep_view(),
    {
        reveal(<CaptureOuterAndLocalPayload as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureOuterAndLocalPayloadSpec<T0, T1> {
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
        reveal(CaptureOuterAndLocalPayloadSpec::from_structural);
        reveal(CaptureOuterAndLocalPayloadSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureOuterAndLocalPayloadSpec::from_structural);
        reveal(CaptureOuterAndLocalPayloadSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { tag, body } => (tag, body),
            },
    {
        reveal(CaptureOuterAndLocalPayloadSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureOuterAndLocalPayloadForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureOuterAndLocalPayloadReverse;

impl SpecMap for CaptureOuterAndLocalPayloadForward {
    type Input = CaptureOuterAndLocalPayloadInner;

    type Output = CaptureOuterAndLocalPayloadSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureOuterAndLocalPayloadSpec::from_structural(input)
    }
}

impl SpecMap for CaptureOuterAndLocalPayloadReverse {
    type Input = CaptureOuterAndLocalPayloadSpec;

    type Output = CaptureOuterAndLocalPayloadInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_local_in_anon_struct_wrapper_value_choice0`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureLocalInAnonStructWrapperValueChoice0<'i> {
    pub len: u8,
    pub bytes: &'i [u8],
}

# [verifier::ext_equal]
pub struct CaptureLocalInAnonStructWrapperValueChoice0Spec<T0 = u8, T1 = Seq<u8>> {
    pub len: T0,
    pub bytes: T1,
}

pub type CaptureLocalInAnonStructWrapperValueChoice0Inner = (u8, Seq<u8>);

impl<'i> DeepView for CaptureLocalInAnonStructWrapperValueChoice0<'i> {
    type V = CaptureLocalInAnonStructWrapperValueChoice0Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CaptureLocalInAnonStructWrapperValueChoice0Spec {
            len: self.len.deep_view(),
            bytes: self.bytes.deep_view(),
        }
    }
}

impl<'i> CaptureLocalInAnonStructWrapperValueChoice0<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().len == self.len.deep_view(),
            self.deep_view().bytes == self.bytes.deep_view(),
    {
        reveal(<CaptureLocalInAnonStructWrapperValueChoice0 as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureLocalInAnonStructWrapperValueChoice0Spec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (len, bytes) = input;
        Self { len, bytes }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { len, bytes } = self;
        (len, bytes)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CaptureLocalInAnonStructWrapperValueChoice0Spec::from_structural);
        reveal(CaptureLocalInAnonStructWrapperValueChoice0Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureLocalInAnonStructWrapperValueChoice0Spec::from_structural);
        reveal(CaptureLocalInAnonStructWrapperValueChoice0Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { len, bytes } => (len, bytes),
            },
    {
        reveal(CaptureLocalInAnonStructWrapperValueChoice0Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureLocalInAnonStructWrapperValueChoice0Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureLocalInAnonStructWrapperValueChoice0Reverse;

impl SpecMap for CaptureLocalInAnonStructWrapperValueChoice0Forward {
    type Input = CaptureLocalInAnonStructWrapperValueChoice0Inner;

    type Output = CaptureLocalInAnonStructWrapperValueChoice0Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureLocalInAnonStructWrapperValueChoice0Spec::from_structural(input)
    }
}

impl SpecMap for CaptureLocalInAnonStructWrapperValueChoice0Reverse {
    type Input = CaptureLocalInAnonStructWrapperValueChoice0Spec;

    type Output = CaptureLocalInAnonStructWrapperValueChoice0Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_local_in_anon_struct_wrapper_value`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum CaptureLocalInAnonStructWrapperValue<'i> {
    Variant1(CaptureLocalInAnonStructWrapperValueChoice0<'i>),
    Default(u16),
}

# [verifier::ext_equal]
pub enum CaptureLocalInAnonStructWrapperValueSpec<
    T0 = CaptureLocalInAnonStructWrapperValueChoice0Spec,
    T1 = u16,
> {
    Variant1(T0),
    Default(T1),
}

pub type CaptureLocalInAnonStructWrapperValueInner = Sum<
    CaptureLocalInAnonStructWrapperValueChoice0Spec,
    u16,
>;

impl<'i> DeepView for CaptureLocalInAnonStructWrapperValue<'i> {
    type V = CaptureLocalInAnonStructWrapperValueSpec;

    # [verifier::opaque]
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

impl<'i> CaptureLocalInAnonStructWrapperValue<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                CaptureLocalInAnonStructWrapperValue::Variant1(
                    v,
                ) => CaptureLocalInAnonStructWrapperValueSpec::Variant1(v.deep_view()),
                CaptureLocalInAnonStructWrapperValue::Default(
                    v,
                ) => CaptureLocalInAnonStructWrapperValueSpec::Default(v.deep_view()),
            },
    {
        reveal(<CaptureLocalInAnonStructWrapperValue as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureLocalInAnonStructWrapperValueSpec<T0, T1> {
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
        reveal(CaptureLocalInAnonStructWrapperValueSpec::from_structural);
        reveal(CaptureLocalInAnonStructWrapperValueSpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureLocalInAnonStructWrapperValueSpec::from_structural);
        reveal(CaptureLocalInAnonStructWrapperValueSpec::into_structural);
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
        reveal(CaptureLocalInAnonStructWrapperValueSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureLocalInAnonStructWrapperValueForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureLocalInAnonStructWrapperValueReverse;

impl SpecMap for CaptureLocalInAnonStructWrapperValueForward {
    type Input = CaptureLocalInAnonStructWrapperValueInner;

    type Output = CaptureLocalInAnonStructWrapperValueSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureLocalInAnonStructWrapperValueSpec::from_structural(input)
    }
}

impl SpecMap for CaptureLocalInAnonStructWrapperValueReverse {
    type Input = CaptureLocalInAnonStructWrapperValueSpec;

    type Output = CaptureLocalInAnonStructWrapperValueInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_local_in_anon_struct_wrapper`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureLocalInAnonStructWrapper<'i> {
    pub tag: u8,
    pub value: CaptureLocalInAnonStructWrapperValue<'i>,
}

# [verifier::ext_equal]
pub struct CaptureLocalInAnonStructWrapperSpec<
    T0 = u8,
    T1 = CaptureLocalInAnonStructWrapperValueSpec,
> {
    pub tag: T0,
    pub value: T1,
}

pub type CaptureLocalInAnonStructWrapperInner = (u8, CaptureLocalInAnonStructWrapperValueSpec);

impl<'i> DeepView for CaptureLocalInAnonStructWrapper<'i> {
    type V = CaptureLocalInAnonStructWrapperSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CaptureLocalInAnonStructWrapperSpec {
            tag: self.tag.deep_view(),
            value: self.value.deep_view(),
        }
    }
}

impl<'i> CaptureLocalInAnonStructWrapper<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().tag == self.tag.deep_view(),
            self.deep_view().value == self.value.deep_view(),
    {
        reveal(<CaptureLocalInAnonStructWrapper as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureLocalInAnonStructWrapperSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (tag, value) = input;
        Self { tag, value }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { tag, value } = self;
        (tag, value)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CaptureLocalInAnonStructWrapperSpec::from_structural);
        reveal(CaptureLocalInAnonStructWrapperSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureLocalInAnonStructWrapperSpec::from_structural);
        reveal(CaptureLocalInAnonStructWrapperSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { tag, value } => (tag, value),
            },
    {
        reveal(CaptureLocalInAnonStructWrapperSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureLocalInAnonStructWrapperForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureLocalInAnonStructWrapperReverse;

impl SpecMap for CaptureLocalInAnonStructWrapperForward {
    type Input = CaptureLocalInAnonStructWrapperInner;

    type Output = CaptureLocalInAnonStructWrapperSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureLocalInAnonStructWrapperSpec::from_structural(input)
    }
}

impl SpecMap for CaptureLocalInAnonStructWrapperReverse {
    type Input = CaptureLocalInAnonStructWrapperSpec;

    type Output = CaptureLocalInAnonStructWrapperInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_param_and_local_x_a_payload`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum CaptureParamAndLocalXAPayload<'i> {
    C(&'i [u8]),
    D(&'i [u8]),
}

# [verifier::ext_equal]
pub enum CaptureParamAndLocalXAPayloadSpec<T0 = Seq<u8>, T1 = Seq<u8>> {
    C(T0),
    D(T1),
}

pub type CaptureParamAndLocalXAPayloadInner = Sum<Seq<u8>, Seq<u8>>;

impl<'i> DeepView for CaptureParamAndLocalXAPayload<'i> {
    type V = CaptureParamAndLocalXAPayloadSpec;

    # [verifier::opaque]
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

impl<'i> CaptureParamAndLocalXAPayload<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                CaptureParamAndLocalXAPayload::C(v) => CaptureParamAndLocalXAPayloadSpec::C(
                    v.deep_view(),
                ),
                CaptureParamAndLocalXAPayload::D(v) => CaptureParamAndLocalXAPayloadSpec::D(
                    v.deep_view(),
                ),
            },
    {
        reveal(<CaptureParamAndLocalXAPayload as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureParamAndLocalXAPayloadSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, T1>) -> Self {
        match input {
            L(value) => Self::C(value),
            R(value) => Self::D(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, T1> {
        match self {
            Self::C(value) => L(value),
            Self::D(value) => R(value),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CaptureParamAndLocalXAPayloadSpec::from_structural);
        reveal(CaptureParamAndLocalXAPayloadSpec::into_structural);
        match self {
            Self::C(_) => {},
            Self::D(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureParamAndLocalXAPayloadSpec::from_structural);
        reveal(CaptureParamAndLocalXAPayloadSpec::into_structural);
        match input {
            L(_) => {},
            R(_) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::C(value) => L(value),
                Self::D(value) => R(value),
            },
    {
        reveal(CaptureParamAndLocalXAPayloadSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalXAPayloadForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalXAPayloadReverse;

impl SpecMap for CaptureParamAndLocalXAPayloadForward {
    type Input = CaptureParamAndLocalXAPayloadInner;

    type Output = CaptureParamAndLocalXAPayloadSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureParamAndLocalXAPayloadSpec::from_structural(input)
    }
}

impl SpecMap for CaptureParamAndLocalXAPayloadReverse {
    type Input = CaptureParamAndLocalXAPayloadSpec;

    type Output = CaptureParamAndLocalXAPayloadInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_param_and_local_x_a`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureParamAndLocalXA<'i> {
    pub len: u8,
    pub payload: CaptureParamAndLocalXAPayload<'i>,
}

# [verifier::ext_equal]
pub struct CaptureParamAndLocalXASpec<T0 = u8, T1 = CaptureParamAndLocalXAPayloadSpec> {
    pub len: T0,
    pub payload: T1,
}

pub type CaptureParamAndLocalXAInner = (u8, CaptureParamAndLocalXAPayloadSpec);

impl<'i> DeepView for CaptureParamAndLocalXA<'i> {
    type V = CaptureParamAndLocalXASpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CaptureParamAndLocalXASpec { len: self.len.deep_view(), payload: self.payload.deep_view() }
    }
}

impl<'i> CaptureParamAndLocalXA<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().len == self.len.deep_view(),
            self.deep_view().payload == self.payload.deep_view(),
    {
        reveal(<CaptureParamAndLocalXA as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureParamAndLocalXASpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (len, payload) = input;
        Self { len, payload }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { len, payload } = self;
        (len, payload)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CaptureParamAndLocalXASpec::from_structural);
        reveal(CaptureParamAndLocalXASpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureParamAndLocalXASpec::from_structural);
        reveal(CaptureParamAndLocalXASpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { len, payload } => (len, payload),
            },
    {
        reveal(CaptureParamAndLocalXASpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalXAForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalXAReverse;

impl SpecMap for CaptureParamAndLocalXAForward {
    type Input = CaptureParamAndLocalXAInner;

    type Output = CaptureParamAndLocalXASpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureParamAndLocalXASpec::from_structural(input)
    }
}

impl SpecMap for CaptureParamAndLocalXAReverse {
    type Input = CaptureParamAndLocalXASpec;

    type Output = CaptureParamAndLocalXAInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_param_and_local_x_b_y`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum CaptureParamAndLocalXBY {
    Variant1(u8),
    Default(u16),
}

# [verifier::ext_equal]
pub enum CaptureParamAndLocalXBYSpec<T0 = u8, T1 = u16> {
    Variant1(T0),
    Default(T1),
}

pub type CaptureParamAndLocalXBYInner = Sum<u8, u16>;

impl DeepView for CaptureParamAndLocalXBY {
    type V = CaptureParamAndLocalXBYSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            CaptureParamAndLocalXBY::Variant1(v) => CaptureParamAndLocalXBYSpec::Variant1(
                v.deep_view(),
            ),
            CaptureParamAndLocalXBY::Default(v) => CaptureParamAndLocalXBYSpec::Default(
                v.deep_view(),
            ),
        }
    }
}

impl CaptureParamAndLocalXBY {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                CaptureParamAndLocalXBY::Variant1(v) => CaptureParamAndLocalXBYSpec::Variant1(
                    v.deep_view(),
                ),
                CaptureParamAndLocalXBY::Default(v) => CaptureParamAndLocalXBYSpec::Default(
                    v.deep_view(),
                ),
            },
    {
        reveal(<CaptureParamAndLocalXBY as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureParamAndLocalXBYSpec<T0, T1> {
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
        reveal(CaptureParamAndLocalXBYSpec::from_structural);
        reveal(CaptureParamAndLocalXBYSpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureParamAndLocalXBYSpec::from_structural);
        reveal(CaptureParamAndLocalXBYSpec::into_structural);
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
        reveal(CaptureParamAndLocalXBYSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalXBYForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalXBYReverse;

impl SpecMap for CaptureParamAndLocalXBYForward {
    type Input = CaptureParamAndLocalXBYInner;

    type Output = CaptureParamAndLocalXBYSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureParamAndLocalXBYSpec::from_structural(input)
    }
}

impl SpecMap for CaptureParamAndLocalXBYReverse {
    type Input = CaptureParamAndLocalXBYSpec;

    type Output = CaptureParamAndLocalXBYInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_param_and_local_x_b`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct CaptureParamAndLocalXB {
    pub tag: u8,
    pub y: CaptureParamAndLocalXBY,
}

# [verifier::ext_equal]
pub struct CaptureParamAndLocalXBSpec<T0 = u8, T1 = CaptureParamAndLocalXBYSpec> {
    pub tag: T0,
    pub y: T1,
}

pub type CaptureParamAndLocalXBInner = (u8, CaptureParamAndLocalXBYSpec);

impl DeepView for CaptureParamAndLocalXB {
    type V = CaptureParamAndLocalXBSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        CaptureParamAndLocalXBSpec { tag: self.tag.deep_view(), y: self.y.deep_view() }
    }
}

impl CaptureParamAndLocalXB {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().tag == self.tag.deep_view(),
            self.deep_view().y == self.y.deep_view(),
    {
        reveal(<CaptureParamAndLocalXB as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureParamAndLocalXBSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (tag, y) = input;
        Self { tag, y }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { tag, y } = self;
        (tag, y)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CaptureParamAndLocalXBSpec::from_structural);
        reveal(CaptureParamAndLocalXBSpec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureParamAndLocalXBSpec::from_structural);
        reveal(CaptureParamAndLocalXBSpec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { tag, y } => (tag, y),
            },
    {
        reveal(CaptureParamAndLocalXBSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalXBForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalXBReverse;

impl SpecMap for CaptureParamAndLocalXBForward {
    type Input = CaptureParamAndLocalXBInner;

    type Output = CaptureParamAndLocalXBSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureParamAndLocalXBSpec::from_structural(input)
    }
}

impl SpecMap for CaptureParamAndLocalXBReverse {
    type Input = CaptureParamAndLocalXBSpec;

    type Output = CaptureParamAndLocalXBInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `capture_param_and_local_x`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum CaptureParamAndLocalX<'i> {
    A(CaptureParamAndLocalXA<'i>),
    B(CaptureParamAndLocalXB),
}

# [verifier::ext_equal]
pub enum CaptureParamAndLocalXSpec<
    T0 = CaptureParamAndLocalXASpec,
    T1 = CaptureParamAndLocalXBSpec,
> {
    A(T0),
    B(T1),
}

pub type CaptureParamAndLocalXInner = Sum<CaptureParamAndLocalXASpec, CaptureParamAndLocalXBSpec>;

impl<'i> DeepView for CaptureParamAndLocalX<'i> {
    type V = CaptureParamAndLocalXSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            CaptureParamAndLocalX::A(v) => CaptureParamAndLocalXSpec::A(v.deep_view()),
            CaptureParamAndLocalX::B(v) => CaptureParamAndLocalXSpec::B(v.deep_view()),
        }
    }
}

impl<'i> CaptureParamAndLocalX<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                CaptureParamAndLocalX::A(v) => CaptureParamAndLocalXSpec::A(v.deep_view()),
                CaptureParamAndLocalX::B(v) => CaptureParamAndLocalXSpec::B(v.deep_view()),
            },
    {
        reveal(<CaptureParamAndLocalX as DeepView>::deep_view);
    }
}

impl<T0, T1> CaptureParamAndLocalXSpec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<T0, T1>) -> Self {
        match input {
            L(value) => Self::A(value),
            R(value) => Self::B(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<T0, T1> {
        match self {
            Self::A(value) => L(value),
            Self::B(value) => R(value),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(CaptureParamAndLocalXSpec::from_structural);
        reveal(CaptureParamAndLocalXSpec::into_structural);
        match self {
            Self::A(_) => {},
            Self::B(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(CaptureParamAndLocalXSpec::from_structural);
        reveal(CaptureParamAndLocalXSpec::into_structural);
        match input {
            L(_) => {},
            R(_) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::A(value) => L(value),
                Self::B(value) => R(value),
            },
    {
        reveal(CaptureParamAndLocalXSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalXForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct CaptureParamAndLocalXReverse;

impl SpecMap for CaptureParamAndLocalXForward {
    type Input = CaptureParamAndLocalXInner;

    type Output = CaptureParamAndLocalXSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        CaptureParamAndLocalXSpec::from_structural(input)
    }
}

impl SpecMap for CaptureParamAndLocalXReverse {
    type Input = CaptureParamAndLocalXSpec;

    type Output = CaptureParamAndLocalXInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `a_or_b`."]
# [derive (Clone, Copy)]
pub struct AOrBFmt;

pub type AOrBFmtSpec = Named<Mapped<Refined<U8, PredFnSpec<u8>>, BiMap<AOrBForward, AOrBReverse>>>;

impl AOrBFmt {
    # [doc = "specification constructor for `a_or_b`."]
    pub open spec fn spec_inner() -> AOrBFmtSpec {
        Named(
            "a_or_b",
            Mapped {
                inner: Refined(U8, |x: u8| (x == 1) || (x == 2)),
                mapper: BiMap(AOrBForward, AOrBReverse),
            },
        )
    }
}

# [doc = "named format combinator for `c_or_d`."]
# [derive (Clone, Copy)]
pub struct COrDFmt;

pub type COrDFmtSpec = Named<Mapped<Refined<U8, PredFnSpec<u8>>, BiMap<COrDForward, COrDReverse>>>;

impl COrDFmt {
    # [doc = "specification constructor for `c_or_d`."]
    pub open spec fn spec_inner() -> COrDFmtSpec {
        Named(
            "c_or_d",
            Mapped {
                inner: Refined(U8, |x: u8| (x == 1) || (x == 2)),
                mapper: BiMap(COrDForward, COrDReverse),
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
        BiMap<NestedInnerStructForward, NestedInnerStructReverse>,
    >,
>;

impl NestedInnerStructFmt {
    # [doc = "specification constructor for `nested_inner_struct`."]
    pub open spec fn spec_inner() -> NestedInnerStructFmtSpec {
        Named(
            "nested_inner_struct",
            Mapped {
                inner: Bind(U32Le, |len: u32| ExactLen(len, NestedInnerStructValFmt)),
                mapper: BiMap(NestedInnerStructForward, NestedInnerStructReverse),
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
    Mapped<NestedInnerChoiceXFmt, BiMap<NestedInnerChoiceForward, NestedInnerChoiceReverse>>,
>;

impl NestedInnerChoiceFmt {
    # [doc = "specification constructor for `nested_inner_choice`."]
    pub open spec fn spec_inner(choice1: AOrBSpec, choice2: COrDSpec) -> NestedInnerChoiceFmtSpec {
        Named(
            "nested_inner_choice",
            Mapped {
                inner: NestedInnerChoiceXFmt::spec(choice1, choice2),
                mapper: BiMap(NestedInnerChoiceForward, NestedInnerChoiceReverse),
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
        BiMap<CaptureOuterAndLocalForward, CaptureOuterAndLocalReverse>,
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
                mapper: BiMap(CaptureOuterAndLocalForward, CaptureOuterAndLocalReverse),
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
        BiMap<CaptureLocalInAnonStructForward, CaptureLocalInAnonStructReverse>,
    >,
>;

impl CaptureLocalInAnonStructFmt {
    # [doc = "specification constructor for `capture_local_in_anon_struct`."]
    pub open spec fn spec_inner() -> CaptureLocalInAnonStructFmtSpec {
        Named(
            "capture_local_in_anon_struct",
            Mapped {
                inner: CaptureLocalInAnonStructWrapperFmt,
                mapper: BiMap(CaptureLocalInAnonStructForward, CaptureLocalInAnonStructReverse),
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
        BiMap<CaptureParamAndLocalForward, CaptureParamAndLocalReverse>,
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
                mapper: BiMap(CaptureParamAndLocalForward, CaptureParamAndLocalReverse),
            },
        )
    }
}

# [doc = "named format combinator for `nested_inner_struct_val`."]
# [derive (Clone, Copy)]
pub struct NestedInnerStructValFmt;

pub type NestedInnerStructValFmtSpec = Named<
    Mapped<Pair<U8, Tail>, BiMap<NestedInnerStructValForward, NestedInnerStructValReverse>>,
>;

impl NestedInnerStructValFmt {
    # [doc = "specification constructor for `nested_inner_struct_val`."]
    pub open spec fn spec_inner() -> NestedInnerStructValFmtSpec {
        Named(
            "nested_inner_struct_val",
            Mapped {
                inner: Pair(U8, Tail),
                mapper: BiMap(NestedInnerStructValForward, NestedInnerStructValReverse),
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
    Mapped<Sum<U8, U16Le>, BiMap<NestedInnerChoiceXAForward, NestedInnerChoiceXAReverse>>,
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
                mapper: BiMap(NestedInnerChoiceXAForward, NestedInnerChoiceXAReverse),
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
        BiMap<NestedInnerChoiceXForward, NestedInnerChoiceXReverse>,
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
                mapper: BiMap(NestedInnerChoiceXForward, NestedInnerChoiceXReverse),
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
        BiMap<
            CaptureOuterAndLocalPayloadBodyChoice1Forward,
            CaptureOuterAndLocalPayloadBodyChoice1Reverse,
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
                mapper: BiMap(
                    CaptureOuterAndLocalPayloadBodyChoice1Forward,
                    CaptureOuterAndLocalPayloadBodyChoice1Reverse,
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
        BiMap<CaptureOuterAndLocalPayloadBodyForward, CaptureOuterAndLocalPayloadBodyReverse>,
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
                mapper: BiMap(
                    CaptureOuterAndLocalPayloadBodyForward,
                    CaptureOuterAndLocalPayloadBodyReverse,
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
        BiMap<CaptureOuterAndLocalPayloadForward, CaptureOuterAndLocalPayloadReverse>,
    >,
>;

impl CaptureOuterAndLocalPayloadFmt {
    # [doc = "specification constructor for `capture_outer_and_local_payload`."]
    pub open spec fn spec_inner(frame_len: u8) -> CaptureOuterAndLocalPayloadFmtSpec {
        Named(
            "capture_outer_and_local_payload",
            Mapped {
                inner: Bind(U8, |tag: u8| CaptureOuterAndLocalPayloadBodyFmt::spec(frame_len, tag)),
                mapper: BiMap(
                    CaptureOuterAndLocalPayloadForward,
                    CaptureOuterAndLocalPayloadReverse,
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
        BiMap<
            CaptureLocalInAnonStructWrapperValueChoice0Forward,
            CaptureLocalInAnonStructWrapperValueChoice0Reverse,
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
                mapper: BiMap(
                    CaptureLocalInAnonStructWrapperValueChoice0Forward,
                    CaptureLocalInAnonStructWrapperValueChoice0Reverse,
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
        BiMap<
            CaptureLocalInAnonStructWrapperValueForward,
            CaptureLocalInAnonStructWrapperValueReverse,
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
                mapper: BiMap(
                    CaptureLocalInAnonStructWrapperValueForward,
                    CaptureLocalInAnonStructWrapperValueReverse,
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
        BiMap<CaptureLocalInAnonStructWrapperForward, CaptureLocalInAnonStructWrapperReverse>,
    >,
>;

impl CaptureLocalInAnonStructWrapperFmt {
    # [doc = "specification constructor for `capture_local_in_anon_struct_wrapper`."]
    pub open spec fn spec_inner() -> CaptureLocalInAnonStructWrapperFmtSpec {
        Named(
            "capture_local_in_anon_struct_wrapper",
            Mapped {
                inner: Bind(U8, |tag: u8| CaptureLocalInAnonStructWrapperValueFmt::spec(tag)),
                mapper: BiMap(
                    CaptureLocalInAnonStructWrapperForward,
                    CaptureLocalInAnonStructWrapperReverse,
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
        BiMap<CaptureParamAndLocalXAPayloadForward, CaptureParamAndLocalXAPayloadReverse>,
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
                mapper: BiMap(
                    CaptureParamAndLocalXAPayloadForward,
                    CaptureParamAndLocalXAPayloadReverse,
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
        BiMap<CaptureParamAndLocalXAForward, CaptureParamAndLocalXAReverse>,
    >,
>;

impl CaptureParamAndLocalXAFmt {
    # [doc = "specification constructor for `capture_param_and_local_x_a`."]
    pub open spec fn spec_inner(choice2: COrDSpec) -> CaptureParamAndLocalXAFmtSpec {
        Named(
            "capture_param_and_local_x_a",
            Mapped {
                inner: Bind(U8, |len: u8| CaptureParamAndLocalXAPayloadFmt::spec(choice2, len)),
                mapper: BiMap(CaptureParamAndLocalXAForward, CaptureParamAndLocalXAReverse),
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
    Mapped<Sum<U8, U16Le>, BiMap<CaptureParamAndLocalXBYForward, CaptureParamAndLocalXBYReverse>>,
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
                mapper: BiMap(CaptureParamAndLocalXBYForward, CaptureParamAndLocalXBYReverse),
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
        BiMap<CaptureParamAndLocalXBForward, CaptureParamAndLocalXBReverse>,
    >,
>;

impl CaptureParamAndLocalXBFmt {
    # [doc = "specification constructor for `capture_param_and_local_x_b`."]
    pub open spec fn spec_inner() -> CaptureParamAndLocalXBFmtSpec {
        Named(
            "capture_param_and_local_x_b",
            Mapped {
                inner: Bind(U8, |tag: u8| CaptureParamAndLocalXBYFmt::spec(tag)),
                mapper: BiMap(CaptureParamAndLocalXBForward, CaptureParamAndLocalXBReverse),
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
        BiMap<CaptureParamAndLocalXForward, CaptureParamAndLocalXReverse>,
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
                mapper: BiMap(CaptureParamAndLocalXForward, CaptureParamAndLocalXReverse),
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

    broadcast use {
        vps_lib::combinators::disjoint::disjointness_lemmas,
        AOrB::lemma_from_into,
        AOrB::lemma_into_from,
        COrD::lemma_from_into,
        COrD::lemma_into_from,
        NestedInnerStructSpec::lemma_from_into,
        NestedInnerStructSpec::lemma_into_from,
        NestedInnerChoiceSpec::lemma_from_into,
        NestedInnerChoiceSpec::lemma_into_from,
        CaptureOuterAndLocalSpec::lemma_from_into,
        CaptureOuterAndLocalSpec::lemma_into_from,
        CaptureLocalInAnonStructSpec::lemma_from_into,
        CaptureLocalInAnonStructSpec::lemma_into_from,
        CaptureParamAndLocalSpec::lemma_from_into,
        CaptureParamAndLocalSpec::lemma_into_from,
        NestedInnerStructValSpec::lemma_from_into,
        NestedInnerStructValSpec::lemma_into_from,
        NestedInnerChoiceXASpec::lemma_from_into,
        NestedInnerChoiceXASpec::lemma_into_from,
        NestedInnerChoiceXSpec::lemma_from_into,
        NestedInnerChoiceXSpec::lemma_into_from,
        CaptureOuterAndLocalPayloadBodyChoice1Spec::lemma_from_into,
        CaptureOuterAndLocalPayloadBodyChoice1Spec::lemma_into_from,
        CaptureOuterAndLocalPayloadBodySpec::lemma_from_into,
        CaptureOuterAndLocalPayloadBodySpec::lemma_into_from,
        CaptureOuterAndLocalPayloadSpec::lemma_from_into,
        CaptureOuterAndLocalPayloadSpec::lemma_into_from,
        CaptureLocalInAnonStructWrapperValueChoice0Spec::lemma_from_into,
        CaptureLocalInAnonStructWrapperValueChoice0Spec::lemma_into_from,
        CaptureLocalInAnonStructWrapperValueSpec::lemma_from_into,
        CaptureLocalInAnonStructWrapperValueSpec::lemma_into_from,
        CaptureLocalInAnonStructWrapperSpec::lemma_from_into,
        CaptureLocalInAnonStructWrapperSpec::lemma_into_from,
        CaptureParamAndLocalXAPayloadSpec::lemma_from_into,
        CaptureParamAndLocalXAPayloadSpec::lemma_into_from,
        CaptureParamAndLocalXASpec::lemma_from_into,
        CaptureParamAndLocalXASpec::lemma_into_from,
        CaptureParamAndLocalXBYSpec::lemma_from_into,
        CaptureParamAndLocalXBYSpec::lemma_into_from,
        CaptureParamAndLocalXBSpec::lemma_from_into,
        CaptureParamAndLocalXBSpec::lemma_into_from,
        CaptureParamAndLocalXSpec::lemma_from_into,
        CaptureParamAndLocalXSpec::lemma_into_from,
    };

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
            assert forall|input: AOrBInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(AOrB::structural_valid(input));
                AOrB::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<AOrBFmt as SpecParser>::spec_parse);
            reveal(<AOrBFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: AOrBInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(AOrB::structural_valid(input));
                AOrB::lemma_into_from(input);
            }
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
            assert forall|output: AOrBSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                AOrB::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for AOrBFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<AOrBFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: AOrBInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(AOrB::structural_valid(input));
                AOrB::lemma_into_from(input);
            }
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
            assert forall|input: COrDInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(COrD::structural_valid(input));
                COrD::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<COrDFmt as SpecParser>::spec_parse);
            reveal(<COrDFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: COrDInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(COrD::structural_valid(input));
                COrD::lemma_into_from(input);
            }
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
            assert forall|output: COrDSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                COrD::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for COrDFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<COrDFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: COrDInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                assert(COrD::structural_valid(input));
                COrD::lemma_into_from(input);
            }
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
            assert forall|input: NestedInnerStructInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerStructSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerStructFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: NestedInnerStructInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerStructSpec::lemma_into_from(input);
            }
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
            assert forall|output: NestedInnerStructSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                NestedInnerStructSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedInnerStructFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedInnerStructFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: NestedInnerStructInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerStructSpec::lemma_into_from(input);
            }
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
            assert forall|input: NestedInnerChoiceInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerChoiceSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert forall|input: NestedInnerChoiceInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerChoiceSpec::lemma_into_from(input);
            }
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
            assert forall|output: NestedInnerChoiceSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                NestedInnerChoiceSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedInnerChoiceFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedInnerChoiceFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert forall|input: NestedInnerChoiceInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerChoiceSpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureOuterAndLocalInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureOuterAndLocalInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalSpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureOuterAndLocalSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureOuterAndLocalSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureOuterAndLocalFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureOuterAndLocalFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureOuterAndLocalInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalSpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureLocalInAnonStructInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureLocalInAnonStructInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructSpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureLocalInAnonStructSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureLocalInAnonStructSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureLocalInAnonStructFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureLocalInAnonStructInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructSpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureParamAndLocalInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert forall|input: CaptureParamAndLocalInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalSpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureParamAndLocalSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureParamAndLocalSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert forall|input: CaptureParamAndLocalInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalSpec::lemma_into_from(input);
            }
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
            assert forall|input: NestedInnerStructValInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerStructValSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerStructValFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerStructValFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: NestedInnerStructValInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerStructValSpec::lemma_into_from(input);
            }
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
            assert forall|output: NestedInnerStructValSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                NestedInnerStructValSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedInnerStructValFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedInnerStructValFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: NestedInnerStructValInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerStructValSpec::lemma_into_from(input);
            }
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
            assert forall|input: NestedInnerChoiceXAInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerChoiceXASpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceXAFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert forall|input: NestedInnerChoiceXAInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerChoiceXASpec::lemma_into_from(input);
            }
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
            assert forall|output: NestedInnerChoiceXASpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                NestedInnerChoiceXASpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedInnerChoiceXAFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedInnerChoiceXAFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert forall|input: NestedInnerChoiceXAInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerChoiceXASpec::lemma_into_from(input);
            }
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
            assert forall|input: NestedInnerChoiceXInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerChoiceXSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoiceXFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert forall|input: NestedInnerChoiceXInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerChoiceXSpec::lemma_into_from(input);
            }
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
            assert forall|output: NestedInnerChoiceXSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                NestedInnerChoiceXSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for NestedInnerChoiceXFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<NestedInnerChoiceXFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert forall|input: NestedInnerChoiceXInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                NestedInnerChoiceXSpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureOuterAndLocalPayloadBodyChoice1Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalPayloadBodyChoice1Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureOuterAndLocalPayloadBodyChoice1Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalPayloadBodyChoice1Spec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureOuterAndLocalPayloadBodyChoice1Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureOuterAndLocalPayloadBodyChoice1Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureOuterAndLocalPayloadBodyChoice1Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalPayloadBodyChoice1Spec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureOuterAndLocalPayloadBodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalPayloadBodySpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert forall|input: CaptureOuterAndLocalPayloadBodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalPayloadBodySpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureOuterAndLocalPayloadBodySpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureOuterAndLocalPayloadBodySpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureOuterAndLocalPayloadBodyFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.frame_len_spec(), self.tag_spec());
            assert forall|input: CaptureOuterAndLocalPayloadBodyInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalPayloadBodySpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureOuterAndLocalPayloadInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalPayloadSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert forall|input: CaptureOuterAndLocalPayloadInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalPayloadSpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureOuterAndLocalPayloadSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureOuterAndLocalPayloadSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureOuterAndLocalPayloadFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.frame_len_spec());
            assert forall|input: CaptureOuterAndLocalPayloadInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureOuterAndLocalPayloadSpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureLocalInAnonStructWrapperValueChoice0Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructWrapperValueChoice0Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureLocalInAnonStructWrapperValueChoice0Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructWrapperValueChoice0Spec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureLocalInAnonStructWrapperValueChoice0Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureLocalInAnonStructWrapperValueChoice0Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureLocalInAnonStructWrapperValueChoice0Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructWrapperValueChoice0Spec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureLocalInAnonStructWrapperValueInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructWrapperValueSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.tag_spec());
            assert forall|input: CaptureLocalInAnonStructWrapperValueInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructWrapperValueSpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureLocalInAnonStructWrapperValueSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureLocalInAnonStructWrapperValueSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureLocalInAnonStructWrapperValueFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert forall|input: CaptureLocalInAnonStructWrapperValueInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructWrapperValueSpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureLocalInAnonStructWrapperInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructWrapperSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureLocalInAnonStructWrapperInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructWrapperSpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureLocalInAnonStructWrapperSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureLocalInAnonStructWrapperSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureLocalInAnonStructWrapperFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureLocalInAnonStructWrapperInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureLocalInAnonStructWrapperSpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureParamAndLocalXAPayloadInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXAPayloadSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXAPayloadFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert forall|input: CaptureParamAndLocalXAPayloadInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXAPayloadSpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureParamAndLocalXAPayloadSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureParamAndLocalXAPayloadSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalXAPayloadFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice2_spec(), self.len_spec());
            assert forall|input: CaptureParamAndLocalXAPayloadInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXAPayloadSpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureParamAndLocalXAInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXASpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXAFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert forall|input: CaptureParamAndLocalXAInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXASpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureParamAndLocalXASpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureParamAndLocalXASpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalXAFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalXAFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice2_spec());
            assert forall|input: CaptureParamAndLocalXAInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXASpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureParamAndLocalXBYInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXBYSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXBYFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.tag_spec());
            assert forall|input: CaptureParamAndLocalXBYInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXBYSpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureParamAndLocalXBYSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureParamAndLocalXBYSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalXBYFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.tag_spec());
            assert forall|input: CaptureParamAndLocalXBYInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXBYSpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureParamAndLocalXBInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXBSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXBFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureParamAndLocalXBInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXBSpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureParamAndLocalXBSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureParamAndLocalXBSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalXBFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalXBFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: CaptureParamAndLocalXBInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXBSpec::lemma_into_from(input);
            }
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
            assert forall|input: CaptureParamAndLocalXInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert forall|input: CaptureParamAndLocalXInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXSpec::lemma_into_from(input);
            }
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
            assert forall|output: CaptureParamAndLocalXSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                CaptureParamAndLocalXSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for CaptureParamAndLocalXFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<CaptureParamAndLocalXFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.choice1_spec(), self.choice2_spec());
            assert forall|input: CaptureParamAndLocalXInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                CaptureParamAndLocalXSpec::lemma_into_from(input);
            }
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
            reveal(<AOrB as DeepView>::deep_view);
            reveal(AOrB::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, AOrB> for AOrBFmt {
        fn serialize_into(&self, v: &AOrB, obuf: &mut Output) {
            reveal(<AOrBFmt as SpecSerializer>::spec_serialize);
            reveal(<AOrBFmt as SpecByteLen>::byte_len);
            reveal(<AOrB as DeepView>::deep_view);
            reveal(AOrB::into_structural);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                AOrB::A => 1,
                AOrB::B => 2,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<AOrB> for AOrBFmt {
        fn prepare(&self, v: &AOrB) -> Result<usize, PreSerializeError> {
            reveal(<AOrBFmt as SpecByteLen>::byte_len);
            reveal(<AOrB as DeepView>::deep_view);
            reveal(AOrB::into_structural);
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
            reveal(<COrD as DeepView>::deep_view);
            reveal(COrD::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, COrD> for COrDFmt {
        fn serialize_into(&self, v: &COrD, obuf: &mut Output) {
            reveal(<COrDFmt as SpecSerializer>::spec_serialize);
            reveal(<COrDFmt as SpecByteLen>::byte_len);
            reveal(<COrD as DeepView>::deep_view);
            reveal(COrD::into_structural);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                COrD::C => 1,
                COrD::D => 2,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<COrD> for COrDFmt {
        fn prepare(&self, v: &COrD) -> Result<usize, PreSerializeError> {
            reveal(<COrDFmt as SpecByteLen>::byte_len);
            reveal(<COrD as DeepView>::deep_view);
            reveal(COrD::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NestedInnerStructFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerStruct as DeepView>::deep_view);
            reveal(NestedInnerStructSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<Output, NestedInnerStruct<'i>> for NestedInnerStructFmt {
        fn serialize_into(&self, v: &NestedInnerStruct<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<NestedInnerStructFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedInnerStructFmt as SpecByteLen>::byte_len);
            reveal(<NestedInnerStruct as DeepView>::deep_view);
            reveal(NestedInnerStructSpec::into_structural);
            let ghost old_obuf = obuf@;

            let NestedInnerStruct { len, val } = v;
            U32Le.serialize_into(len, obuf);
            ExactLen(*len, NestedInnerStructValFmt).serialize_into(val, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedInnerStruct<'i>> for NestedInnerStructFmt {
        fn prepare(&self, v: &NestedInnerStruct<'i>) -> Result<usize, PreSerializeError> {
            reveal(<NestedInnerStructFmt as SpecByteLen>::byte_len);
            reveal(<NestedInnerStruct as DeepView>::deep_view);
            reveal(NestedInnerStructSpec::into_structural);
            let NestedInnerStruct { len, val } = v;
            let l1 = (U32Le).prepare(len)?;
            let l2 = (ExactLen(
                *len,
                Named("nested_inner_struct_val", NestedInnerStructValFmt),
            )).prepare(val)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for NestedInnerChoiceFmt {
        type PT = NestedInnerChoice;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NestedInnerChoiceFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerChoice as DeepView>::deep_view);
            reveal(NestedInnerChoiceSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
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

    impl<Output: OutputBuf, 'i> Serializer<Output, NestedInnerChoice> for NestedInnerChoiceFmt {
        fn serialize_into(&self, v: &NestedInnerChoice, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<NestedInnerChoiceFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedInnerChoiceFmt as SpecByteLen>::byte_len);
            reveal(<NestedInnerChoice as DeepView>::deep_view);
            reveal(NestedInnerChoiceSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            let NestedInnerChoice { x } = v;
            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            NestedInnerChoiceXFmt { choice1: self.choice1, choice2: self.choice2 }.serialize_into(
                x,
                obuf,
            );

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedInnerChoice> for NestedInnerChoiceFmt {
        fn prepare(&self, v: &NestedInnerChoice) -> Result<usize, PreSerializeError> {
            reveal(<NestedInnerChoiceFmt as SpecByteLen>::byte_len);
            reveal(<NestedInnerChoice as DeepView>::deep_view);
            reveal(NestedInnerChoiceSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            let NestedInnerChoice { x } = v;
            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureOuterAndLocalFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocal as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureOuterAndLocal<'i>,
    > for CaptureOuterAndLocalFmt {
        fn serialize_into(&self, v: &CaptureOuterAndLocal<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<CaptureOuterAndLocalFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureOuterAndLocalFmt as SpecByteLen>::byte_len);
            reveal(<CaptureOuterAndLocal as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalSpec::into_structural);
            let ghost old_obuf = obuf@;

            let CaptureOuterAndLocal { frame_len, payload } = v;
            U8.serialize_into(frame_len, obuf);
            ExactLen(
                *frame_len,
                CaptureOuterAndLocalPayloadFmt { frame_len: *frame_len },
            ).serialize_into(payload, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureOuterAndLocal<'i>> for CaptureOuterAndLocalFmt {
        fn prepare(&self, v: &CaptureOuterAndLocal<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureOuterAndLocalFmt as SpecByteLen>::byte_len);
            reveal(<CaptureOuterAndLocal as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalSpec::into_structural);
            let CaptureOuterAndLocal { frame_len, payload } = v;
            let l1 = {
                if !(*frame_len >= 1) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (U8).prepare(frame_len)
                }
            }?;
            let l2 = (ExactLen(
                *frame_len,
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureLocalInAnonStructFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStruct as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureLocalInAnonStruct<'i>,
    > for CaptureLocalInAnonStructFmt {
        fn serialize_into(&self, v: &CaptureLocalInAnonStruct<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<CaptureLocalInAnonStructFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureLocalInAnonStructFmt as SpecByteLen>::byte_len);
            reveal(<CaptureLocalInAnonStruct as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructSpec::into_structural);
            let ghost old_obuf = obuf@;

            let CaptureLocalInAnonStruct { wrapper } = v;
            CaptureLocalInAnonStructWrapperFmt.serialize_into(wrapper, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureLocalInAnonStruct<'i>> for CaptureLocalInAnonStructFmt {
        fn prepare(&self, v: &CaptureLocalInAnonStruct<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureLocalInAnonStructFmt as SpecByteLen>::byte_len);
            reveal(<CaptureLocalInAnonStruct as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureParamAndLocalFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocal as DeepView>::deep_view);
            reveal(CaptureParamAndLocalSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureParamAndLocal<'i>,
    > for CaptureParamAndLocalFmt {
        fn serialize_into(&self, v: &CaptureParamAndLocal<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<CaptureParamAndLocalFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocal as DeepView>::deep_view);
            reveal(CaptureParamAndLocalSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            let CaptureParamAndLocal { x } = v;
            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            CaptureParamAndLocalXFmt {
                choice1: self.choice1,
                choice2: self.choice2,
            }.serialize_into(x, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocal<'i>> for CaptureParamAndLocalFmt {
        fn prepare(&self, v: &CaptureParamAndLocal<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureParamAndLocalFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocal as DeepView>::deep_view);
            reveal(CaptureParamAndLocalSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            let CaptureParamAndLocal { x } = v;
            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<NestedInnerStructValFmt as SpecParser>::spec_parse);
            reveal(<NestedInnerStructVal as DeepView>::deep_view);
            reveal(NestedInnerStructValSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        NestedInnerStructVal<'i>,
    > for NestedInnerStructValFmt {
        fn serialize_into(&self, v: &NestedInnerStructVal<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<NestedInnerStructValFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedInnerStructValFmt as SpecByteLen>::byte_len);
            reveal(<NestedInnerStructVal as DeepView>::deep_view);
            reveal(NestedInnerStructValSpec::into_structural);
            let ghost old_obuf = obuf@;

            let NestedInnerStructVal { x, y } = v;
            U8.serialize_into(x, obuf);
            Tail.serialize_into(y, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedInnerStructVal<'i>> for NestedInnerStructValFmt {
        fn prepare(&self, v: &NestedInnerStructVal<'i>) -> Result<usize, PreSerializeError> {
            reveal(<NestedInnerStructValFmt as SpecByteLen>::byte_len);
            reveal(<NestedInnerStructVal as DeepView>::deep_view);
            reveal(NestedInnerStructValSpec::into_structural);
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
            reveal(<NestedInnerChoiceXA as DeepView>::deep_view);
            reveal(NestedInnerChoiceXASpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.choice2.lemma_deep_view();
            }

            proof {
                self.choice2.lemma_deep_view();
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

    impl<Output: OutputBuf, 'i> Serializer<Output, NestedInnerChoiceXA> for NestedInnerChoiceXAFmt {
        fn serialize_into(&self, v: &NestedInnerChoiceXA, obuf: &mut Output) {
            reveal(<NestedInnerChoiceXAFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedInnerChoiceXAFmt as SpecByteLen>::byte_len);
            reveal(<NestedInnerChoiceXA as DeepView>::deep_view);
            reveal(NestedInnerChoiceXASpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice2.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            proof {
                self.choice2.lemma_deep_view();
            }

            match (self.choice2, v) {
                (COrD::C, NestedInnerChoiceXA::C(v)) => {
                    (U8).serialize_into(v, obuf);
                },
                (COrD::D, NestedInnerChoiceXA::D(v)) => {
                    (U16Le).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedInnerChoiceXA> for NestedInnerChoiceXAFmt {
        fn prepare(&self, v: &NestedInnerChoiceXA) -> Result<usize, PreSerializeError> {
            reveal(<NestedInnerChoiceXAFmt as SpecByteLen>::byte_len);
            reveal(<NestedInnerChoiceXA as DeepView>::deep_view);
            reveal(NestedInnerChoiceXASpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice2.lemma_deep_view();
            }

            proof {
                self.choice2.lemma_deep_view();
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
            reveal(<NestedInnerChoiceX as DeepView>::deep_view);
            reveal(NestedInnerChoiceXSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
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

    impl<Output: OutputBuf, 'i> Serializer<Output, NestedInnerChoiceX> for NestedInnerChoiceXFmt {
        fn serialize_into(&self, v: &NestedInnerChoiceX, obuf: &mut Output) {
            reveal(<NestedInnerChoiceXFmt as SpecSerializer>::spec_serialize);
            reveal(<NestedInnerChoiceXFmt as SpecByteLen>::byte_len);
            reveal(<NestedInnerChoiceX as DeepView>::deep_view);
            reveal(NestedInnerChoiceXSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            match (self.choice1, v) {
                (AOrB::A, NestedInnerChoiceX::A(v)) => {
                    (NestedInnerChoiceXAFmt { choice2: self.choice2 }).serialize_into(v, obuf);
                },
                (AOrB::B, NestedInnerChoiceX::B(v)) => {
                    (U32Le).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<NestedInnerChoiceX> for NestedInnerChoiceXFmt {
        fn prepare(&self, v: &NestedInnerChoiceX) -> Result<usize, PreSerializeError> {
            reveal(<NestedInnerChoiceXFmt as SpecByteLen>::byte_len);
            reveal(<NestedInnerChoiceX as DeepView>::deep_view);
            reveal(NestedInnerChoiceXSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1 as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalPayloadBodyChoice1Spec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureOuterAndLocalPayloadBodyChoice1<'i>,
    > for CaptureOuterAndLocalPayloadBodyChoice1Fmt {
        fn serialize_into(
            &self,
            v: &CaptureOuterAndLocalPayloadBodyChoice1<'i>,
            obuf: &mut Output,
        ) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1Fmt as SpecByteLen>::byte_len);
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1 as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalPayloadBodyChoice1Spec::into_structural);
            let ghost old_obuf = obuf@;

            let CaptureOuterAndLocalPayloadBodyChoice1 { count, items } = v;
            U8.serialize_into(count, obuf);
            Varied(*count).serialize_into(*items, obuf);

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
            reveal(<CaptureOuterAndLocalPayloadBodyChoice1 as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalPayloadBodyChoice1Spec::into_structural);
            let CaptureOuterAndLocalPayloadBodyChoice1 { count, items } = v;
            let l1 = (U8).prepare(count)?;
            let l2 = (Varied(*count)).prepare(items)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureOuterAndLocalPayloadBodyFmt {
        type PT = CaptureOuterAndLocalPayloadBody<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayloadBody as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalPayloadBodySpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureOuterAndLocalPayloadBody<'i>,
    > for CaptureOuterAndLocalPayloadBodyFmt {
        fn serialize_into(&self, v: &CaptureOuterAndLocalPayloadBody<'i>, obuf: &mut Output) {
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureOuterAndLocalPayloadBodyFmt as SpecByteLen>::byte_len);
            reveal(<CaptureOuterAndLocalPayloadBody as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalPayloadBodySpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (0, CaptureOuterAndLocalPayloadBody::Variant1(v)) => {
                    (Varied((self.frame_len - 1))).serialize_into(*v, obuf);
                },
                (_, CaptureOuterAndLocalPayloadBody::Default(v)) => {
                    (CaptureOuterAndLocalPayloadBodyChoice1Fmt).serialize_into(v, obuf);
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
            reveal(<CaptureOuterAndLocalPayloadBody as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalPayloadBodySpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureOuterAndLocalPayloadFmt as SpecParser>::spec_parse);
            reveal(<CaptureOuterAndLocalPayload as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalPayloadSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureOuterAndLocalPayload<'i>,
    > for CaptureOuterAndLocalPayloadFmt {
        fn serialize_into(&self, v: &CaptureOuterAndLocalPayload<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<CaptureOuterAndLocalPayloadFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecByteLen>::byte_len);
            reveal(<CaptureOuterAndLocalPayload as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalPayloadSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            let CaptureOuterAndLocalPayload { tag, body } = v;
            U8.serialize_into(tag, obuf);
            CaptureOuterAndLocalPayloadBodyFmt {
                frame_len: self.frame_len,
                tag: *tag,
            }.serialize_into(body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureOuterAndLocalPayload<'i>> for CaptureOuterAndLocalPayloadFmt {
        fn prepare(&self, v: &CaptureOuterAndLocalPayload<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureOuterAndLocalPayloadFmt as SpecByteLen>::byte_len);
            reveal(<CaptureOuterAndLocalPayload as DeepView>::deep_view);
            reveal(CaptureOuterAndLocalPayloadSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0 as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructWrapperValueChoice0Spec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureLocalInAnonStructWrapperValueChoice0<'i>,
    > for CaptureLocalInAnonStructWrapperValueChoice0Fmt {
        fn serialize_into(
            &self,
            v: &CaptureLocalInAnonStructWrapperValueChoice0<'i>,
            obuf: &mut Output,
        ) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(
                <CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecSerializer>::spec_serialize,
            );
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0Fmt as SpecByteLen>::byte_len);
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0 as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructWrapperValueChoice0Spec::into_structural);
            let ghost old_obuf = obuf@;

            let CaptureLocalInAnonStructWrapperValueChoice0 { len, bytes } = v;
            U8.serialize_into(len, obuf);
            Varied(*len).serialize_into(*bytes, obuf);

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
            reveal(<CaptureLocalInAnonStructWrapperValueChoice0 as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructWrapperValueChoice0Spec::into_structural);
            let CaptureLocalInAnonStructWrapperValueChoice0 { len, bytes } = v;
            let l1 = (U8).prepare(len)?;
            let l2 = (Varied(*len)).prepare(bytes)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for CaptureLocalInAnonStructWrapperValueFmt {
        type PT = CaptureLocalInAnonStructWrapperValue<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapperValue as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructWrapperValueSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureLocalInAnonStructWrapperValue<'i>,
    > for CaptureLocalInAnonStructWrapperValueFmt {
        fn serialize_into(&self, v: &CaptureLocalInAnonStructWrapperValue<'i>, obuf: &mut Output) {
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureLocalInAnonStructWrapperValueFmt as SpecByteLen>::byte_len);
            reveal(<CaptureLocalInAnonStructWrapperValue as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructWrapperValueSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (0, CaptureLocalInAnonStructWrapperValue::Variant1(v)) => {
                    (CaptureLocalInAnonStructWrapperValueChoice0Fmt).serialize_into(v, obuf);
                },
                (_, CaptureLocalInAnonStructWrapperValue::Default(v)) => {
                    (U16Le).serialize_into(v, obuf);
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
            reveal(<CaptureLocalInAnonStructWrapperValue as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructWrapperValueSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecParser>::spec_parse);
            reveal(<CaptureLocalInAnonStructWrapper as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructWrapperSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureLocalInAnonStructWrapper<'i>,
    > for CaptureLocalInAnonStructWrapperFmt {
        fn serialize_into(&self, v: &CaptureLocalInAnonStructWrapper<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecByteLen>::byte_len);
            reveal(<CaptureLocalInAnonStructWrapper as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructWrapperSpec::into_structural);
            let ghost old_obuf = obuf@;

            let CaptureLocalInAnonStructWrapper { tag, value } = v;
            U8.serialize_into(tag, obuf);
            CaptureLocalInAnonStructWrapperValueFmt { tag: *tag }.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureLocalInAnonStructWrapper<'i>> for CaptureLocalInAnonStructWrapperFmt {
        fn prepare(&self, v: &CaptureLocalInAnonStructWrapper<'i>) -> Result<
            usize,
            PreSerializeError,
        > {
            reveal(<CaptureLocalInAnonStructWrapperFmt as SpecByteLen>::byte_len);
            reveal(<CaptureLocalInAnonStructWrapper as DeepView>::deep_view);
            reveal(CaptureLocalInAnonStructWrapperSpec::into_structural);
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
            reveal(<CaptureParamAndLocalXAPayload as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXAPayloadSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.choice2.lemma_deep_view();
            }

            proof {
                self.choice2.lemma_deep_view();
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureParamAndLocalXAPayload<'i>,
    > for CaptureParamAndLocalXAPayloadFmt {
        fn serialize_into(&self, v: &CaptureParamAndLocalXAPayload<'i>, obuf: &mut Output) {
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalXAPayloadFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocalXAPayload as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXAPayloadSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice2.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            proof {
                self.choice2.lemma_deep_view();
            }

            match (self.choice2, v) {
                (COrD::C, CaptureParamAndLocalXAPayload::C(v)) => {
                    (Varied(self.len)).serialize_into(*v, obuf);
                },
                (COrD::D, CaptureParamAndLocalXAPayload::D(v)) => {
                    (Varied(self.len)).serialize_into(*v, obuf);
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
            reveal(<CaptureParamAndLocalXAPayload as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXAPayloadSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice2.lemma_deep_view();
            }

            proof {
                self.choice2.lemma_deep_view();
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureParamAndLocalXAFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXA as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXASpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.choice2.lemma_deep_view();
            }

            let (n1, len) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            proof {
                self.choice2.lemma_deep_view();
            }

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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureParamAndLocalXA<'i>,
    > for CaptureParamAndLocalXAFmt {
        fn serialize_into(&self, v: &CaptureParamAndLocalXA<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<CaptureParamAndLocalXAFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalXAFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocalXA as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXASpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice2.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            let CaptureParamAndLocalXA { len, payload } = v;
            proof {
                self.choice2.lemma_deep_view();
            }

            U8.serialize_into(len, obuf);
            CaptureParamAndLocalXAPayloadFmt { choice2: self.choice2, len: *len }.serialize_into(
                payload,
                obuf,
            );

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocalXA<'i>> for CaptureParamAndLocalXAFmt {
        fn prepare(&self, v: &CaptureParamAndLocalXA<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureParamAndLocalXAFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocalXA as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXASpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice2.lemma_deep_view();
            }

            let CaptureParamAndLocalXA { len, payload } = v;
            proof {
                self.choice2.lemma_deep_view();
            }

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
            reveal(<CaptureParamAndLocalXBY as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXBYSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureParamAndLocalXBY,
    > for CaptureParamAndLocalXBYFmt {
        fn serialize_into(&self, v: &CaptureParamAndLocalXBY, obuf: &mut Output) {
            reveal(<CaptureParamAndLocalXBYFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalXBYFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocalXBY as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXBYSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.tag, v) {
                (0, CaptureParamAndLocalXBY::Variant1(v)) => {
                    (U8).serialize_into(v, obuf);
                },
                (_, CaptureParamAndLocalXBY::Default(v)) => {
                    (U16Le).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocalXBY> for CaptureParamAndLocalXBYFmt {
        fn prepare(&self, v: &CaptureParamAndLocalXBY) -> Result<usize, PreSerializeError> {
            reveal(<CaptureParamAndLocalXBYFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocalXBY as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXBYSpec::into_structural);
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<CaptureParamAndLocalXBFmt as SpecParser>::spec_parse);
            reveal(<CaptureParamAndLocalXB as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXBSpec::from_structural);
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureParamAndLocalXB,
    > for CaptureParamAndLocalXBFmt {
        fn serialize_into(&self, v: &CaptureParamAndLocalXB, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<CaptureParamAndLocalXBFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalXBFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocalXB as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXBSpec::into_structural);
            let ghost old_obuf = obuf@;

            let CaptureParamAndLocalXB { tag, y } = v;
            U8.serialize_into(tag, obuf);
            CaptureParamAndLocalXBYFmt { tag: *tag }.serialize_into(y, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocalXB> for CaptureParamAndLocalXBFmt {
        fn prepare(&self, v: &CaptureParamAndLocalXB) -> Result<usize, PreSerializeError> {
            reveal(<CaptureParamAndLocalXBFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocalXB as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXBSpec::into_structural);
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
            reveal(<CaptureParamAndLocalX as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
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

    impl<Output: OutputBuf, 'i> Serializer<
        Output,
        CaptureParamAndLocalX<'i>,
    > for CaptureParamAndLocalXFmt {
        fn serialize_into(&self, v: &CaptureParamAndLocalX<'i>, obuf: &mut Output) {
            reveal(<CaptureParamAndLocalXFmt as SpecSerializer>::spec_serialize);
            reveal(<CaptureParamAndLocalXFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocalX as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            match (self.choice1, v) {
                (AOrB::A, CaptureParamAndLocalX::A(v)) => {
                    (CaptureParamAndLocalXAFmt { choice2: self.choice2 }).serialize_into(v, obuf);
                },
                (AOrB::B, CaptureParamAndLocalX::B(v)) => {
                    (CaptureParamAndLocalXBFmt).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<CaptureParamAndLocalX<'i>> for CaptureParamAndLocalXFmt {
        fn prepare(&self, v: &CaptureParamAndLocalX<'i>) -> Result<usize, PreSerializeError> {
            reveal(<CaptureParamAndLocalXFmt as SpecByteLen>::byte_len);
            reveal(<CaptureParamAndLocalX as DeepView>::deep_view);
            reveal(CaptureParamAndLocalXSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
            }

            proof {
                self.choice1.lemma_deep_view();
                self.choice2.lemma_deep_view();
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
