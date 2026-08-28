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
# [doc = "data type for `msg1`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg1<'i> {
    pub b: &'i [u8],
    pub payload: Msg1Payload,
}

# [verifier::ext_equal]
pub struct Msg1Spec<T0 = Seq<u8>, T1 = Msg1PayloadSpec> {
    pub b: T0,
    pub payload: T1,
}

pub type Msg1Inner = (Seq<u8>, Msg1PayloadSpec);

impl<'i> DeepView for Msg1<'i> {
    type V = Msg1Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        Msg1Spec { b: self.b.deep_view(), payload: self.payload.deep_view() }
    }
}

impl<'i> Msg1<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().b == self.b.deep_view(),
            self.deep_view().payload == self.payload.deep_view(),
    {
        reveal(<Msg1 as DeepView>::deep_view);
    }
}

impl<T0, T1> Msg1Spec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (b, payload) = input;
        Self { b, payload }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { b, payload } = self;
        (b, payload)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg1Spec::from_structural);
        reveal(Msg1Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg1Spec::from_structural);
        reveal(Msg1Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { b, payload } => (b, payload),
            },
    {
        reveal(Msg1Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg1Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg1Reverse;

impl SpecMap for Msg1Forward {
    type Input = Msg1Inner;

    type Output = Msg1Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg1Spec::from_structural(input)
    }
}

impl SpecMap for Msg1Reverse {
    type Input = Msg1Spec;

    type Output = Msg1Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `hello_retry_request`."]
pub type HelloRetryRequest = u16;

pub type HelloRetryRequestSpec = u16;

# [doc = "data type for `server_hello`."]
pub type ServerHello = u32;

pub type ServerHelloSpec = u32;

# [doc = "data type for `msg2`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg2<'i> {
    pub b: &'i [u8],
    pub content: Msg2Content,
}

# [verifier::ext_equal]
pub struct Msg2Spec<T0 = Seq<u8>, T1 = Msg2ContentSpec> {
    pub b: T0,
    pub content: T1,
}

pub type Msg2Inner = (Seq<u8>, Msg2ContentSpec);

impl<'i> DeepView for Msg2<'i> {
    type V = Msg2Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        Msg2Spec { b: self.b.deep_view(), content: self.content.deep_view() }
    }
}

impl<'i> Msg2<'i> {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().b == self.b.deep_view(),
            self.deep_view().content == self.content.deep_view(),
    {
        reveal(<Msg2 as DeepView>::deep_view);
    }
}

impl<T0, T1> Msg2Spec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (b, content) = input;
        Self { b, content }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { b, content } = self;
        (b, content)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg2Spec::from_structural);
        reveal(Msg2Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg2Spec::from_structural);
        reveal(Msg2Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { b, content } => (b, content),
            },
    {
        reveal(Msg2Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg2Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg2Reverse;

impl SpecMap for Msg2Forward {
    type Input = Msg2Inner;

    type Output = Msg2Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg2Spec::from_structural(input)
    }
}

impl SpecMap for Msg2Reverse {
    type Input = Msg2Spec;

    type Output = Msg2Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg3`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg3 {
    pub i: u8,
    pub content: Msg3Content,
}

# [verifier::ext_equal]
pub struct Msg3Spec<T0 = u8, T1 = Msg3ContentSpec> {
    pub i: T0,
    pub content: T1,
}

pub type Msg3Inner = (u8, Msg3ContentSpec);

impl DeepView for Msg3 {
    type V = Msg3Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        Msg3Spec { i: self.i.deep_view(), content: self.content.deep_view() }
    }
}

impl Msg3 {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().i == self.i.deep_view(),
            self.deep_view().content == self.content.deep_view(),
    {
        reveal(<Msg3 as DeepView>::deep_view);
    }
}

impl<T0, T1> Msg3Spec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (i, content) = input;
        Self { i, content }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { i, content } = self;
        (i, content)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg3Spec::from_structural);
        reveal(Msg3Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg3Spec::from_structural);
        reveal(Msg3Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { i, content } => (i, content),
            },
    {
        reveal(Msg3Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg3Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg3Reverse;

impl SpecMap for Msg3Forward {
    type Input = Msg3Inner;

    type Output = Msg3Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg3Spec::from_structural(input)
    }
}

impl SpecMap for Msg3Reverse {
    type Input = Msg3Spec;

    type Output = Msg3Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg4`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg4 {
    pub i: u32,
    pub content: Msg4Content,
}

# [verifier::ext_equal]
pub struct Msg4Spec<T0 = u32, T1 = Msg4ContentSpec> {
    pub i: T0,
    pub content: T1,
}

pub type Msg4Inner = (u32, Msg4ContentSpec);

impl DeepView for Msg4 {
    type V = Msg4Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        Msg4Spec { i: self.i.deep_view(), content: self.content.deep_view() }
    }
}

impl Msg4 {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().i == self.i.deep_view(),
            self.deep_view().content == self.content.deep_view(),
    {
        reveal(<Msg4 as DeepView>::deep_view);
    }
}

impl<T0, T1> Msg4Spec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (i, content) = input;
        Self { i, content }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { i, content } = self;
        (i, content)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg4Spec::from_structural);
        reveal(Msg4Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg4Spec::from_structural);
        reveal(Msg4Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { i, content } => (i, content),
            },
    {
        reveal(Msg4Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg4Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg4Reverse;

impl SpecMap for Msg4Forward {
    type Input = Msg4Inner;

    type Output = Msg4Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg4Spec::from_structural(input)
    }
}

impl SpecMap for Msg4Reverse {
    type Input = Msg4Spec;

    type Output = Msg4Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg5`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Msg5 {
    pub i: u64,
    pub content: Msg5Content,
}

# [verifier::ext_equal]
pub struct Msg5Spec<T0 = u64, T1 = Msg5ContentSpec> {
    pub i: T0,
    pub content: T1,
}

pub type Msg5Inner = (u64, Msg5ContentSpec);

impl DeepView for Msg5 {
    type V = Msg5Spec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        Msg5Spec { i: self.i.deep_view(), content: self.content.deep_view() }
    }
}

impl Msg5 {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view().i == self.i.deep_view(),
            self.deep_view().content == self.content.deep_view(),
    {
        reveal(<Msg5 as DeepView>::deep_view);
    }
}

impl<T0, T1> Msg5Spec<T0, T1> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (i, content) = input;
        Self { i, content }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { i, content } = self;
        (i, content)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg5Spec::from_structural);
        reveal(Msg5Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg5Spec::from_structural);
        reveal(Msg5Spec::into_structural);
    }

    pub proof fn lemma_into_structural_fields(self)
        ensures
            Self::into_structural(self) == match self {
                Self { i, content } => (i, content),
            },
    {
        reveal(Msg5Spec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg5Forward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg5Reverse;

impl SpecMap for Msg5Forward {
    type Input = Msg5Inner;

    type Output = Msg5Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg5Spec::from_structural(input)
    }
}

impl SpecMap for Msg5Reverse {
    type Input = Msg5Spec;

    type Output = Msg5Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg1_payload`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum Msg1Payload {
    Variant1(HelloRetryRequest),
    Default(ServerHello),
}

# [verifier::ext_equal]
pub enum Msg1PayloadSpec<T0 = HelloRetryRequestSpec, T1 = ServerHelloSpec> {
    Variant1(T0),
    Default(T1),
}

pub type Msg1PayloadInner = Sum<HelloRetryRequestSpec, ServerHelloSpec>;

impl DeepView for Msg1Payload {
    type V = Msg1PayloadSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Msg1Payload::Variant1(v) => Msg1PayloadSpec::Variant1(v.deep_view()),
            Msg1Payload::Default(v) => Msg1PayloadSpec::Default(v.deep_view()),
        }
    }
}

impl Msg1Payload {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                Msg1Payload::Variant1(v) => Msg1PayloadSpec::Variant1(v.deep_view()),
                Msg1Payload::Default(v) => Msg1PayloadSpec::Default(v.deep_view()),
            },
    {
        reveal(<Msg1Payload as DeepView>::deep_view);
    }
}

impl<T0, T1> Msg1PayloadSpec<T0, T1> {
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
        reveal(Msg1PayloadSpec::from_structural);
        reveal(Msg1PayloadSpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg1PayloadSpec::from_structural);
        reveal(Msg1PayloadSpec::into_structural);
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
        reveal(Msg1PayloadSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg1PayloadForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg1PayloadReverse;

impl SpecMap for Msg1PayloadForward {
    type Input = Msg1PayloadInner;

    type Output = Msg1PayloadSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg1PayloadSpec::from_structural(input)
    }
}

impl SpecMap for Msg1PayloadReverse {
    type Input = Msg1PayloadSpec;

    type Output = Msg1PayloadInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg2_content`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum Msg2Content {
    Variant1(u16),
    Variant2(u32),
    Variant3(u64),
    Default(()),
}

# [verifier::ext_equal]
pub enum Msg2ContentSpec<T0 = u16, T1 = u32, T2 = u64, T3 = ()> {
    Variant1(T0),
    Variant2(T1),
    Variant3(T2),
    Default(T3),
}

pub type Msg2ContentInner = Sum<Sum<u16, u32>, Sum<u64, ()>>;

impl DeepView for Msg2Content {
    type V = Msg2ContentSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Msg2Content::Variant1(v) => Msg2ContentSpec::Variant1(v.deep_view()),
            Msg2Content::Variant2(v) => Msg2ContentSpec::Variant2(v.deep_view()),
            Msg2Content::Variant3(v) => Msg2ContentSpec::Variant3(v.deep_view()),
            Msg2Content::Default(v) => Msg2ContentSpec::Default(v.deep_view()),
        }
    }
}

impl Msg2Content {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                Msg2Content::Variant1(v) => Msg2ContentSpec::Variant1(v.deep_view()),
                Msg2Content::Variant2(v) => Msg2ContentSpec::Variant2(v.deep_view()),
                Msg2Content::Variant3(v) => Msg2ContentSpec::Variant3(v.deep_view()),
                Msg2Content::Default(v) => Msg2ContentSpec::Default(v.deep_view()),
            },
    {
        reveal(<Msg2Content as DeepView>::deep_view);
    }
}

impl<T0, T1, T2, T3> Msg2ContentSpec<T0, T1, T2, T3> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<Sum<T0, T1>, Sum<T2, T3>>) -> Self {
        match input {
            L(L(value)) => Self::Variant1(value),
            L(R(value)) => Self::Variant2(value),
            R(L(value)) => Self::Variant3(value),
            R(R(value)) => Self::Default(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<Sum<T0, T1>, Sum<T2, T3>> {
        match self {
            Self::Variant1(value) => L(L(value)),
            Self::Variant2(value) => L(R(value)),
            Self::Variant3(value) => R(L(value)),
            Self::Default(value) => R(R(value)),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg2ContentSpec::from_structural);
        reveal(Msg2ContentSpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Variant2(_) => {},
            Self::Variant3(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<Sum<T0, T1>, Sum<T2, T3>>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg2ContentSpec::from_structural);
        reveal(Msg2ContentSpec::into_structural);
        match input {
            L(L(_)) => {},
            L(R(_)) => {},
            R(L(_)) => {},
            R(R(_)) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::Variant1(value) => L(L(value)),
                Self::Variant2(value) => L(R(value)),
                Self::Variant3(value) => R(L(value)),
                Self::Default(value) => R(R(value)),
            },
    {
        reveal(Msg2ContentSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg2ContentForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg2ContentReverse;

impl SpecMap for Msg2ContentForward {
    type Input = Msg2ContentInner;

    type Output = Msg2ContentSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg2ContentSpec::from_structural(input)
    }
}

impl SpecMap for Msg2ContentReverse {
    type Input = Msg2ContentSpec;

    type Output = Msg2ContentInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg3_content`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum Msg3Content {
    Variant1(u16),
    Variant2(u32),
    Variant3(u32),
    Default(()),
}

# [verifier::ext_equal]
pub enum Msg3ContentSpec<T0 = u16, T1 = u32, T2 = u32, T3 = ()> {
    Variant1(T0),
    Variant2(T1),
    Variant3(T2),
    Default(T3),
}

pub type Msg3ContentInner = Sum<Sum<u16, u32>, Sum<u32, ()>>;

impl DeepView for Msg3Content {
    type V = Msg3ContentSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Msg3Content::Variant1(v) => Msg3ContentSpec::Variant1(v.deep_view()),
            Msg3Content::Variant2(v) => Msg3ContentSpec::Variant2(v.deep_view()),
            Msg3Content::Variant3(v) => Msg3ContentSpec::Variant3(v.deep_view()),
            Msg3Content::Default(v) => Msg3ContentSpec::Default(v.deep_view()),
        }
    }
}

impl Msg3Content {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                Msg3Content::Variant1(v) => Msg3ContentSpec::Variant1(v.deep_view()),
                Msg3Content::Variant2(v) => Msg3ContentSpec::Variant2(v.deep_view()),
                Msg3Content::Variant3(v) => Msg3ContentSpec::Variant3(v.deep_view()),
                Msg3Content::Default(v) => Msg3ContentSpec::Default(v.deep_view()),
            },
    {
        reveal(<Msg3Content as DeepView>::deep_view);
    }
}

impl<T0, T1, T2, T3> Msg3ContentSpec<T0, T1, T2, T3> {
    # [verifier::opaque]
    pub open spec fn from_structural(input: Sum<Sum<T0, T1>, Sum<T2, T3>>) -> Self {
        match input {
            L(L(value)) => Self::Variant1(value),
            L(R(value)) => Self::Variant2(value),
            R(L(value)) => Self::Variant3(value),
            R(R(value)) => Self::Default(value),
        }
    }

    # [verifier::opaque]
    pub open spec fn into_structural(self) -> Sum<Sum<T0, T1>, Sum<T2, T3>> {
        match self {
            Self::Variant1(value) => L(L(value)),
            Self::Variant2(value) => L(R(value)),
            Self::Variant3(value) => R(L(value)),
            Self::Default(value) => R(R(value)),
        }
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            # [trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(Msg3ContentSpec::from_structural);
        reveal(Msg3ContentSpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Variant2(_) => {},
            Self::Variant3(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<Sum<T0, T1>, Sum<T2, T3>>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg3ContentSpec::from_structural);
        reveal(Msg3ContentSpec::into_structural);
        match input {
            L(L(_)) => {},
            L(R(_)) => {},
            R(L(_)) => {},
            R(R(_)) => {},
        }
    }

    pub proof fn lemma_into_structural_variant(self)
        ensures
            Self::into_structural(self) == match self {
                Self::Variant1(value) => L(L(value)),
                Self::Variant2(value) => L(R(value)),
                Self::Variant3(value) => R(L(value)),
                Self::Default(value) => R(R(value)),
            },
    {
        reveal(Msg3ContentSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg3ContentForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg3ContentReverse;

impl SpecMap for Msg3ContentForward {
    type Input = Msg3ContentInner;

    type Output = Msg3ContentSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg3ContentSpec::from_structural(input)
    }
}

impl SpecMap for Msg3ContentReverse {
    type Input = Msg3ContentSpec;

    type Output = Msg3ContentInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg4_content`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum Msg4Content {
    Variant1(u16),
    Default(Never),
}

# [verifier::ext_equal]
pub enum Msg4ContentSpec<T0 = u16, T1 = Never> {
    Variant1(T0),
    Default(T1),
}

pub type Msg4ContentInner = Sum<u16, Never>;

impl DeepView for Msg4Content {
    type V = Msg4ContentSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Msg4Content::Variant1(v) => Msg4ContentSpec::Variant1(v.deep_view()),
            Msg4Content::Default(v) => Msg4ContentSpec::Default(v.deep_view()),
        }
    }
}

impl Msg4Content {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                Msg4Content::Variant1(v) => Msg4ContentSpec::Variant1(v.deep_view()),
                Msg4Content::Default(v) => Msg4ContentSpec::Default(v.deep_view()),
            },
    {
        reveal(<Msg4Content as DeepView>::deep_view);
    }
}

impl<T0, T1> Msg4ContentSpec<T0, T1> {
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
        reveal(Msg4ContentSpec::from_structural);
        reveal(Msg4ContentSpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg4ContentSpec::from_structural);
        reveal(Msg4ContentSpec::into_structural);
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
        reveal(Msg4ContentSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg4ContentForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg4ContentReverse;

impl SpecMap for Msg4ContentForward {
    type Input = Msg4ContentInner;

    type Output = Msg4ContentSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg4ContentSpec::from_structural(input)
    }
}

impl SpecMap for Msg4ContentReverse {
    type Input = Msg4ContentSpec;

    type Output = Msg4ContentInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `msg5_content`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum Msg5Content {
    Variant1(u16),
    Default(Never),
}

# [verifier::ext_equal]
pub enum Msg5ContentSpec<T0 = u16, T1 = Never> {
    Variant1(T0),
    Default(T1),
}

pub type Msg5ContentInner = Sum<u16, Never>;

impl DeepView for Msg5Content {
    type V = Msg5ContentSpec;

    # [verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Msg5Content::Variant1(v) => Msg5ContentSpec::Variant1(v.deep_view()),
            Msg5Content::Default(v) => Msg5ContentSpec::Default(v.deep_view()),
        }
    }
}

impl Msg5Content {
    pub proof fn lemma_deep_view_fields(&self)
        ensures
            self.deep_view() == match self {
                Msg5Content::Variant1(v) => Msg5ContentSpec::Variant1(v.deep_view()),
                Msg5Content::Default(v) => Msg5ContentSpec::Default(v.deep_view()),
            },
    {
        reveal(<Msg5Content as DeepView>::deep_view);
    }
}

impl<T0, T1> Msg5ContentSpec<T0, T1> {
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
        reveal(Msg5ContentSpec::from_structural);
        reveal(Msg5ContentSpec::into_structural);
        match self {
            Self::Variant1(_) => {},
            Self::Default(_) => {},
        }
    }

    pub broadcast proof fn lemma_into_from(input: Sum<T0, T1>)
        ensures
            # [trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(Msg5ContentSpec::from_structural);
        reveal(Msg5ContentSpec::into_structural);
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
        reveal(Msg5ContentSpec::into_structural);
    }
}

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg5ContentForward;

# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Msg5ContentReverse;

impl SpecMap for Msg5ContentForward {
    type Input = Msg5ContentInner;

    type Output = Msg5ContentSpec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        Msg5ContentSpec::from_structural(input)
    }
}

impl SpecMap for Msg5ContentReverse {
    type Input = Msg5ContentSpec;

    type Output = Msg5ContentInner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
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
        Bind<Fixed<32>, spec_fn(Seq<u8>) -> Msg1PayloadFmtSpec>,
        BiMap<Msg1Forward, Msg1Reverse>,
    >,
>;

impl Msg1Fmt {
    # [doc = "specification constructor for `msg1`."]
    pub open spec fn spec_inner() -> Msg1FmtSpec {
        Named(
            "msg1",
            Mapped {
                inner: Bind(Fixed::<32>, |b: Seq<u8>| Msg1PayloadFmt::spec_inner(b)),
                mapper: BiMap(Msg1Forward, Msg1Reverse),
            },
        )
    }
}

# [doc = "named format combinator for `hello_retry_request`."]
# [derive (Clone, Copy)]
pub struct HelloRetryRequestFmt;

pub type HelloRetryRequestFmtSpec = Named<U16Le>;

impl HelloRetryRequestFmt {
    # [doc = "specification constructor for `hello_retry_request`."]
    pub open spec fn spec_inner() -> HelloRetryRequestFmtSpec {
        Named("hello_retry_request", U16Le)
    }
}

# [doc = "named format combinator for `server_hello`."]
# [derive (Clone, Copy)]
pub struct ServerHelloFmt;

pub type ServerHelloFmtSpec = Named<U32Le>;

impl ServerHelloFmt {
    # [doc = "specification constructor for `server_hello`."]
    pub open spec fn spec_inner() -> ServerHelloFmtSpec {
        Named("server_hello", U32Le)
    }
}

# [doc = "named format combinator for `msg2`."]
# [derive (Clone, Copy)]
pub struct Msg2Fmt;

pub type Msg2FmtSpec = Named<
    Mapped<Bind<Fixed<3>, spec_fn(Seq<u8>) -> Msg2ContentFmtSpec>, BiMap<Msg2Forward, Msg2Reverse>>,
>;

impl Msg2Fmt {
    # [doc = "specification constructor for `msg2`."]
    pub open spec fn spec_inner() -> Msg2FmtSpec {
        Named(
            "msg2",
            Mapped {
                inner: Bind(Fixed::<3>, |b: Seq<u8>| Msg2ContentFmt::spec_inner(b)),
                mapper: BiMap(Msg2Forward, Msg2Reverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg3`."]
# [derive (Clone, Copy)]
pub struct Msg3Fmt;

pub type Msg3FmtSpec = Named<
    Mapped<Bind<U8, spec_fn(u8) -> Msg3ContentFmt>, BiMap<Msg3Forward, Msg3Reverse>>,
>;

impl Msg3Fmt {
    # [doc = "specification constructor for `msg3`."]
    pub open spec fn spec_inner() -> Msg3FmtSpec {
        Named(
            "msg3",
            Mapped {
                inner: Bind(U8, |i: u8| Msg3ContentFmt::spec(i)),
                mapper: BiMap(Msg3Forward, Msg3Reverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg4`."]
# [derive (Clone, Copy)]
pub struct Msg4Fmt;

pub type Msg4FmtSpec = Named<
    Mapped<Bind<U24Le, spec_fn(u32) -> Msg4ContentFmt>, BiMap<Msg4Forward, Msg4Reverse>>,
>;

impl Msg4Fmt {
    # [doc = "specification constructor for `msg4`."]
    pub open spec fn spec_inner() -> Msg4FmtSpec {
        Named(
            "msg4",
            Mapped {
                inner: Bind(U24Le, |i: u32| Msg4ContentFmt::spec(i)),
                mapper: BiMap(Msg4Forward, Msg4Reverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg5`."]
# [derive (Clone, Copy)]
pub struct Msg5Fmt;

pub type Msg5FmtSpec = Named<
    Mapped<Bind<VarInt<true>, spec_fn(u64) -> Msg5ContentFmt>, BiMap<Msg5Forward, Msg5Reverse>>,
>;

impl Msg5Fmt {
    # [doc = "specification constructor for `msg5`."]
    pub open spec fn spec_inner() -> Msg5FmtSpec {
        Named(
            "msg5",
            Mapped {
                inner: Bind(VarInt::<true>, |i: u64| Msg5ContentFmt::spec(i)),
                mapper: BiMap(Msg5Forward, Msg5Reverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg1_payload`."]
# [derive (Clone, Copy)]
pub struct Msg1PayloadFmt<'i> {
    b: &'i [u8],
}

impl<'i> Msg1PayloadFmt<'i> {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn b_spec(&self) -> Seq<u8> {
        self.b.deep_view()
    }

    pub closed spec fn spec(b: &'i [u8]) -> Self {
        Msg1PayloadFmt { b }
    }
}

pub type Msg1PayloadFmtSpec = Named<
    Mapped<
        Sum<HelloRetryRequestFmt, ServerHelloFmt>,
        BiMap<Msg1PayloadForward, Msg1PayloadReverse>,
    >,
>;

impl<'i> Msg1PayloadFmt<'i> {
    # [doc = "specification constructor for `msg1_payload`."]
    pub open spec fn spec_inner(b: Seq<u8>) -> Msg1PayloadFmtSpec {
        Named(
            "msg1_payload",
            Mapped {
                inner: match b {
                    x if x == [
                        0xcfu8,
                        0x21u8,
                        0xadu8,
                        0x74u8,
                        0xe5u8,
                        0x9au8,
                        0x61u8,
                        0x11u8,
                        0xbeu8,
                        0x1du8,
                        0x8cu8,
                        0x02u8,
                        0x1eu8,
                        0x65u8,
                        0xb8u8,
                        0x91u8,
                        0xc2u8,
                        0xa2u8,
                        0x11u8,
                        0x16u8,
                        0x7au8,
                        0xbbu8,
                        0x8cu8,
                        0x5eu8,
                        0x07u8,
                        0x9eu8,
                        0x09u8,
                        0xe2u8,
                        0xc8u8,
                        0xa8u8,
                        0x33u8,
                        0x9cu8,
                    ].deep_view() => L(HelloRetryRequestFmt),
                    _ => R(ServerHelloFmt),
                },
                mapper: BiMap(Msg1PayloadForward, Msg1PayloadReverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg2_content`."]
# [derive (Clone, Copy)]
pub struct Msg2ContentFmt<'i> {
    b: &'i [u8],
}

impl<'i> Msg2ContentFmt<'i> {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn b_spec(&self) -> Seq<u8> {
        self.b.deep_view()
    }

    pub closed spec fn spec(b: &'i [u8]) -> Self {
        Msg2ContentFmt { b }
    }
}

pub type Msg2ContentFmtSpec = Named<
    Mapped<
        Sum<Sum<U16Le, U32Le>, Sum<U64Le, Empty>>,
        BiMap<Msg2ContentForward, Msg2ContentReverse>,
    >,
>;

impl<'i> Msg2ContentFmt<'i> {
    # [doc = "specification constructor for `msg2_content`."]
    pub open spec fn spec_inner(b: Seq<u8>) -> Msg2ContentFmtSpec {
        Named(
            "msg2_content",
            Mapped {
                inner: match b {
                    x if x == [0x16u8, 0x03u8, 0x01u8].deep_view() => L(L(U16Le)),
                    x if x == [0x16u8, 0x03u8, 0x02u8].deep_view() => L(R(U32Le)),
                    x if x == [0x16u8, 0x03u8, 0x03u8].deep_view() => R(L(U64Le)),
                    _ => R(R(Empty)),
                },
                mapper: BiMap(Msg2ContentForward, Msg2ContentReverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg3_content`."]
# [derive (Clone, Copy)]
pub struct Msg3ContentFmt {
    i: u8,
}

impl Msg3ContentFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn i_spec(&self) -> u8 {
        self.i.deep_view()
    }

    pub closed spec fn spec(i: u8) -> Self {
        Msg3ContentFmt { i }
    }
}

pub type Msg3ContentFmtSpec = Named<
    Mapped<
        Sum<Sum<U16Le, U32Le>, Sum<U32Le, Empty>>,
        BiMap<Msg3ContentForward, Msg3ContentReverse>,
    >,
>;

impl Msg3ContentFmt {
    # [doc = "specification constructor for `msg3_content`."]
    pub open spec fn spec_inner(i: u8) -> Msg3ContentFmtSpec {
        Named(
            "msg3_content",
            Mapped {
                inner: match i {
                    1 => L(L(U16Le)),
                    2 => L(R(U32Le)),
                    3 => R(L(U32Le)),
                    _ => R(R(Empty)),
                },
                mapper: BiMap(Msg3ContentForward, Msg3ContentReverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg4_content`."]
# [derive (Clone, Copy)]
pub struct Msg4ContentFmt {
    i: u32,
}

impl Msg4ContentFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn i_spec(&self) -> u32 {
        self.i.deep_view()
    }

    pub closed spec fn spec(i: u32) -> Self {
        Msg4ContentFmt { i }
    }
}

pub type Msg4ContentFmtSpec = Named<
    Mapped<Sum<U16Le, Void>, BiMap<Msg4ContentForward, Msg4ContentReverse>>,
>;

impl Msg4ContentFmt {
    # [doc = "specification constructor for `msg4_content`."]
    pub open spec fn spec_inner(i: u32) -> Msg4ContentFmtSpec {
        Named(
            "msg4_content",
            Mapped {
                inner: match i {
                    1 => L(U16Le),
                    _ => R(Void("i for msg4 can only be 1")),
                },
                mapper: BiMap(Msg4ContentForward, Msg4ContentReverse),
            },
        )
    }
}

# [doc = "named format combinator for `msg5_content`."]
# [derive (Clone, Copy)]
pub struct Msg5ContentFmt {
    i: u64,
}

impl Msg5ContentFmt {
    # [verifier::type_invariant]
    spec fn wf(&self) -> bool {
        true
    }

    pub closed spec fn i_spec(&self) -> u64 {
        self.i.deep_view()
    }

    pub closed spec fn spec(i: u64) -> Self {
        Msg5ContentFmt { i }
    }
}

pub type Msg5ContentFmtSpec = Named<
    Mapped<Sum<U16Le, Void>, BiMap<Msg5ContentForward, Msg5ContentReverse>>,
>;

impl Msg5ContentFmt {
    # [doc = "specification constructor for `msg5_content`."]
    pub open spec fn spec_inner(i: u64) -> Msg5ContentFmtSpec {
        Named(
            "msg5_content",
            Mapped {
                inner: match i {
                    2 => L(U16Le),
                    _ => R(Void("i for msg5 can only be 1")),
                },
                mapper: BiMap(Msg5ContentForward, Msg5ContentReverse),
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

    impl SpecParser for HelloRetryRequestFmt {
        type PVal = HelloRetryRequestSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for HelloRetryRequestFmt {
        type Val = HelloRetryRequestSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for HelloRetryRequestFmt {
        type SValue = HelloRetryRequestSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for HelloRetryRequestFmt {
        type SVal = HelloRetryRequestSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for HelloRetryRequestFmt {
        type T = HelloRetryRequestSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for ServerHelloFmt {
        type PVal = ServerHelloSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for ServerHelloFmt {
        type Val = ServerHelloSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for ServerHelloFmt {
        type SValue = ServerHelloSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for ServerHelloFmt {
        type SVal = ServerHelloSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for ServerHelloFmt {
        type T = ServerHelloSpec;

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

    impl SpecParser for Msg4Fmt {
        type PVal = Msg4Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg4Fmt {
        type Val = Msg4Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg4Fmt {
        type SValue = Msg4Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg4Fmt {
        type SVal = Msg4Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg4Fmt {
        type T = Msg4Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl SpecParser for Msg5Fmt {
        type PVal = Msg5Spec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for Msg5Fmt {
        type Val = Msg5Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().consistent(v)
        }
    }

    impl SpecSerializerDps for Msg5Fmt {
        type SValue = Msg5Spec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg5Fmt {
        type SVal = Msg5Spec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg5Fmt {
        type T = Msg5Spec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().byte_len(v)
        }
    }

    impl<'i> SpecParser for Msg1PayloadFmt<'i> {
        type PVal = Msg1PayloadSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.b_spec()).spec_parse(ibuf)
        }
    }

    impl<'i> Consistency for Msg1PayloadFmt<'i> {
        type Val = Msg1PayloadSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.b_spec()).consistent(v)
        }
    }

    impl<'i> SpecSerializerDps for Msg1PayloadFmt<'i> {
        type SValue = Msg1PayloadSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.b_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl<'i> SpecSerializer for Msg1PayloadFmt<'i> {
        type SVal = Msg1PayloadSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.b_spec()).spec_serialize(v)
        }
    }

    impl<'i> SpecByteLen for Msg1PayloadFmt<'i> {
        type T = Msg1PayloadSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.b_spec()).byte_len(v)
        }
    }

    impl<'i> SpecParser for Msg2ContentFmt<'i> {
        type PVal = Msg2ContentSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.b_spec()).spec_parse(ibuf)
        }
    }

    impl<'i> Consistency for Msg2ContentFmt<'i> {
        type Val = Msg2ContentSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.b_spec()).consistent(v)
        }
    }

    impl<'i> SpecSerializerDps for Msg2ContentFmt<'i> {
        type SValue = Msg2ContentSpec;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.b_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl<'i> SpecSerializer for Msg2ContentFmt<'i> {
        type SVal = Msg2ContentSpec;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.b_spec()).spec_serialize(v)
        }
    }

    impl<'i> SpecByteLen for Msg2ContentFmt<'i> {
        type T = Msg2ContentSpec;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.b_spec()).byte_len(v)
        }
    }

    impl SpecParser for Msg3ContentFmt {
        type PVal = Msg3ContentSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.i_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for Msg3ContentFmt {
        type Val = Msg3ContentSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.i_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for Msg3ContentFmt {
        type SValue = Msg3ContentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.i_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg3ContentFmt {
        type SVal = Msg3ContentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.i_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg3ContentFmt {
        type T = Msg3ContentSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.i_spec()).byte_len(v)
        }
    }

    impl SpecParser for Msg4ContentFmt {
        type PVal = Msg4ContentSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.i_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for Msg4ContentFmt {
        type Val = Msg4ContentSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.i_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for Msg4ContentFmt {
        type SValue = Msg4ContentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.i_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg4ContentFmt {
        type SVal = Msg4ContentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.i_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg4ContentFmt {
        type T = Msg4ContentSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.i_spec()).byte_len(v)
        }
    }

    impl SpecParser for Msg5ContentFmt {
        type PVal = Msg5ContentSpec;

        # [verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner(self.i_spec()).spec_parse(ibuf)
        }
    }

    impl Consistency for Msg5ContentFmt {
        type Val = Msg5ContentSpec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner(self.i_spec()).consistent(v)
        }
    }

    impl SpecSerializerDps for Msg5ContentFmt {
        type SValue = Msg5ContentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner(self.i_spec()).spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for Msg5ContentFmt {
        type SVal = Msg5ContentSpec;

        # [verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner(self.i_spec()).spec_serialize(v)
        }
    }

    impl SpecByteLen for Msg5ContentFmt {
        type T = Msg5ContentSpec;

        # [verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner(self.i_spec()).byte_len(v)
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
        Msg1Spec::lemma_from_into,
        Msg1Spec::lemma_into_from,
        Msg2Spec::lemma_from_into,
        Msg2Spec::lemma_into_from,
        Msg3Spec::lemma_from_into,
        Msg3Spec::lemma_into_from,
        Msg4Spec::lemma_from_into,
        Msg4Spec::lemma_into_from,
        Msg5Spec::lemma_from_into,
        Msg5Spec::lemma_into_from,
        Msg1PayloadSpec::lemma_from_into,
        Msg1PayloadSpec::lemma_into_from,
        Msg2ContentSpec::lemma_from_into,
        Msg2ContentSpec::lemma_into_from,
        Msg3ContentSpec::lemma_from_into,
        Msg3ContentSpec::lemma_into_from,
        Msg4ContentSpec::lemma_from_into,
        Msg4ContentSpec::lemma_into_from,
        Msg5ContentSpec::lemma_from_into,
        Msg5ContentSpec::lemma_into_from,
    };

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
            assert forall|input: Msg1Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg1Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: Msg1Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg1Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg1Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
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
            assert forall|output: Msg1Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg1Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg1Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: Msg1Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg1Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg1Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
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

    impl SafeParser for HelloRetryRequestFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<HelloRetryRequestFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for HelloRetryRequestFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<HelloRetryRequestFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for HelloRetryRequestFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<HelloRetryRequestFmt as SpecParser>::spec_parse);
            reveal(<HelloRetryRequestFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<HelloRetryRequestFmt as SpecParser>::spec_parse);
            reveal(<HelloRetryRequestFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for HelloRetryRequestFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<HelloRetryRequestFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<HelloRetryRequestFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HelloRetryRequestFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for HelloRetryRequestFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<HelloRetryRequestFmt as SpecSerializer>::spec_serialize);
            reveal(<HelloRetryRequestFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for HelloRetryRequestFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<HelloRetryRequestFmt as SpecParser>::spec_parse);
            reveal(<HelloRetryRequestFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HelloRetryRequestFmt as Consistency>::consistent);
            reveal(<HelloRetryRequestFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for HelloRetryRequestFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<HelloRetryRequestFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for HelloRetryRequestFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<HelloRetryRequestFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HelloRetryRequestFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for HelloRetryRequestFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<HelloRetryRequestFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<HelloRetryRequestFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for ServerHelloFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<ServerHelloFmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for ServerHelloFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<ServerHelloFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for ServerHelloFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<ServerHelloFmt as SpecParser>::spec_parse);
            reveal(<ServerHelloFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<ServerHelloFmt as SpecParser>::spec_parse);
            reveal(<ServerHelloFmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for ServerHelloFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ServerHelloFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<ServerHelloFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ServerHelloFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for ServerHelloFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<ServerHelloFmt as SpecSerializer>::spec_serialize);
            reveal(<ServerHelloFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for ServerHelloFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<ServerHelloFmt as SpecParser>::spec_parse);
            reveal(<ServerHelloFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ServerHelloFmt as Consistency>::consistent);
            reveal(<ServerHelloFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for ServerHelloFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<ServerHelloFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for ServerHelloFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<ServerHelloFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ServerHelloFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for ServerHelloFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<ServerHelloFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<ServerHelloFmt as SpecSerializer>::spec_serialize);
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
            assert forall|input: Msg2Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg2Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: Msg2Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg2Spec::lemma_into_from(input);
            }
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
            assert forall|output: Msg2Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg2Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg2Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: Msg2Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg2Spec::lemma_into_from(input);
            }
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
            assert forall|input: Msg3Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg3Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            reveal(<Msg3Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: Msg3Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg3Spec::lemma_into_from(input);
            }
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
            assert forall|output: Msg3Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg3Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg3Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: Msg3Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg3Spec::lemma_into_from(input);
            }
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

    impl SafeParser for Msg4Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg4Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg4Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: Msg4Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            reveal(<Msg4Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: Msg4Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg4Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg4Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg4Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
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
            let fmt = Self::spec_inner();
            assert forall|output: Msg4Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg4Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg4Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: Msg4Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg4Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg4Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg5Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg5Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg5Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg5Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg5Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg5Fmt as SpecParser>::spec_parse);
            reveal(<Msg5Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: Msg5Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg5Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg5Fmt as SpecParser>::spec_parse);
            reveal(<Msg5Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: Msg5Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg5Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg5Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg5Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg5Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg5Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg5Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg5Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg5Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg5Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg5Fmt as SpecParser>::spec_parse);
            reveal(<Msg5Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg5Fmt as Consistency>::consistent);
            reveal(<Msg5Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: Msg5Spec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg5Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg5Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg5Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: Msg5Inner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg5Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg5Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg5Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg5Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg5Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg5Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg5Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<'i> SafeParser for Msg1PayloadFmt<'i> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner(self.b_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl<'i> Productive for Msg1PayloadFmt<'i> {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.b_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl<'i> SoundParser for Msg1PayloadFmt<'i> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert forall|input: Msg1PayloadInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg1PayloadSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert forall|input: Msg1PayloadInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg1PayloadSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<'i> NonTailFmt for Msg1PayloadFmt<'i> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<'i> GoodSerializer for Msg1PayloadFmt<'i> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<'i> SPRoundTripDps for Msg1PayloadFmt<'i> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert forall|output: Msg1PayloadSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg1PayloadSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<'i> NonMalleable for Msg1PayloadFmt<'i> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert forall|input: Msg1PayloadInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg1PayloadSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<'i> EquivSerializersGeneral for Msg1PayloadFmt<'i> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<'i> EquivSerializers for Msg1PayloadFmt<'i> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl<'i> SafeParser for Msg2ContentFmt<'i> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            Self::spec_inner(self.b_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl<'i> Productive for Msg2ContentFmt<'i> {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.b_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl<'i> SoundParser for Msg2ContentFmt<'i> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert forall|input: Msg2ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg2ContentSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert forall|input: Msg2ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg2ContentSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl<'i> NonTailFmt for Msg2ContentFmt<'i> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<'i> GoodSerializer for Msg2ContentFmt<'i> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl<'i> SPRoundTripDps for Msg2ContentFmt<'i> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert forall|output: Msg2ContentSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg2ContentSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<'i> NonMalleable for Msg2ContentFmt<'i> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert forall|input: Msg2ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg2ContentSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<'i> EquivSerializersGeneral for Msg2ContentFmt<'i> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl<'i> EquivSerializers for Msg2ContentFmt<'i> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            let fmt = Self::spec_inner(self.b_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg3ContentFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg3ContentFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.i_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg3ContentFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.i_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg3ContentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg3ContentFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg3ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg3ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|input: Msg3ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg3ContentSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg3ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg3ContentFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|input: Msg3ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg3ContentSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg3ContentFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg3ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg3ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg3ContentFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg3ContentFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg3ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg3ContentFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg3ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg3ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3ContentFmt as Consistency>::consistent);
            reveal(<Msg3ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|output: Msg3ContentSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg3ContentSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg3ContentFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg3ContentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|input: Msg3ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg3ContentSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg3ContentFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg3ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3ContentFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg3ContentFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg3ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg3ContentFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg4ContentFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg4ContentFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.i_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg4ContentFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.i_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg4ContentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg4ContentFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg4ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg4ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|input: Msg4ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4ContentSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg4ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg4ContentFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|input: Msg4ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4ContentSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg4ContentFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg4ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg4ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg4ContentFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg4ContentFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg4ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg4ContentFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg4ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg4ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ContentFmt as Consistency>::consistent);
            reveal(<Msg4ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|output: Msg4ContentSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg4ContentSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg4ContentFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg4ContentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|input: Msg4ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg4ContentSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg4ContentFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg4ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ContentFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg4ContentFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg4ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg4ContentFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Msg5ContentFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<Msg5ContentFmt as SpecParser>::spec_parse);
            Self::spec_inner(self.i_spec()).lemma_parse_safe(ibuf);
        }
    }

    impl Productive for Msg5ContentFmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner(self.i_spec()).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<Msg5ContentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for Msg5ContentFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(<Msg5ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg5ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|input: Msg5ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg5ContentSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(<Msg5ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg5ContentFmt as Consistency>::consistent);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|input: Msg5ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg5ContentSpec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for Msg5ContentFmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg5ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<Msg5ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg5ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for Msg5ContentFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(<Msg5ContentFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg5ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Msg5ContentFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(<Msg5ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg5ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg5ContentFmt as Consistency>::consistent);
            reveal(<Msg5ContentFmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|output: Msg5ContentSpec| # [trigger]
                fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                Msg5ContentSpec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for Msg5ContentFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<Msg5ContentFmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner(self.i_spec());
            assert forall|input: Msg5ContentInner| # [trigger]
                fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                Msg5ContentSpec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for Msg5ContentFmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<Msg5ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg5ContentFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.i_spec());
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for Msg5ContentFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<Msg5ContentFmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<Msg5ContentFmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner(self.i_spec());
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
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg1Fmt as SpecParser>::spec_parse);
            reveal(<Msg1 as DeepView>::deep_view);
            reveal(Msg1Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, b) = (Fixed::<32>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, payload) = (Named("msg1_payload", Msg1PayloadFmt { b: b })).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Msg1 { b, payload };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg1<'i>> for Msg1Fmt {
        fn serialize_into(&self, v: &Msg1<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<Msg1Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            reveal(<Msg1 as DeepView>::deep_view);
            reveal(Msg1Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Msg1 { b, payload } = v;
            Fixed::<32>.serialize_into(*b, obuf);
            Msg1PayloadFmt { b: *b }.serialize_into(payload, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg1<'i>> for Msg1Fmt {
        fn prepare(&self, v: &Msg1<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Msg1Fmt as SpecByteLen>::byte_len);
            reveal(<Msg1 as DeepView>::deep_view);
            reveal(Msg1Spec::into_structural);
            let Msg1 { b, payload } = v;
            let l1 = (Fixed::<32>).prepare(b)?;
            let l2 = (Named("msg1_payload", Msg1PayloadFmt { b: *b })).prepare(payload)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for HelloRetryRequestFmt {
        type PT = HelloRetryRequest;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<HelloRetryRequestFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U16Le.parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, HelloRetryRequest> for HelloRetryRequestFmt {
        fn serialize_into(&self, v: &HelloRetryRequest, obuf: &mut Output) {
            reveal(<HelloRetryRequestFmt as SpecSerializer>::spec_serialize);
            reveal(<HelloRetryRequestFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            U16Le.serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<HelloRetryRequest> for HelloRetryRequestFmt {
        fn prepare(&self, v: &HelloRetryRequest) -> Result<usize, PreSerializeError> {
            reveal(<HelloRetryRequestFmt as SpecByteLen>::byte_len);
            (U16Le).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for ServerHelloFmt {
        type PT = ServerHello;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ServerHelloFmt as SpecParser>::spec_parse);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U32Le.parse(ibuf)?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ServerHello> for ServerHelloFmt {
        fn serialize_into(&self, v: &ServerHello, obuf: &mut Output) {
            reveal(<ServerHelloFmt as SpecSerializer>::spec_serialize);
            reveal(<ServerHelloFmt as SpecByteLen>::byte_len);
            let ghost old_obuf = obuf@;

            U32Le.serialize_into(v, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ServerHello> for ServerHelloFmt {
        fn prepare(&self, v: &ServerHello) -> Result<usize, PreSerializeError> {
            reveal(<ServerHelloFmt as SpecByteLen>::byte_len);
            (U32Le).prepare(v)
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg2Fmt {
        type PT = Msg2<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg2Fmt as SpecParser>::spec_parse);
            reveal(<Msg2 as DeepView>::deep_view);
            reveal(Msg2Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, b) = (Fixed::<3>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, content) = (Named("msg2_content", Msg2ContentFmt { b: b })).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Msg2 { b, content };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg2<'i>> for Msg2Fmt {
        fn serialize_into(&self, v: &Msg2<'i>, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<Msg2Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            reveal(<Msg2 as DeepView>::deep_view);
            reveal(Msg2Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Msg2 { b, content } = v;
            Fixed::<3>.serialize_into(*b, obuf);
            Msg2ContentFmt { b: *b }.serialize_into(content, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg2<'i>> for Msg2Fmt {
        fn prepare(&self, v: &Msg2<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Msg2Fmt as SpecByteLen>::byte_len);
            reveal(<Msg2 as DeepView>::deep_view);
            reveal(Msg2Spec::into_structural);
            let Msg2 { b, content } = v;
            let l1 = (Fixed::<3>).prepare(b)?;
            let l2 = (Named("msg2_content", Msg2ContentFmt { b: *b })).prepare(content)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg3Fmt {
        type PT = Msg3;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg3Fmt as SpecParser>::spec_parse);
            reveal(<Msg3 as DeepView>::deep_view);
            reveal(Msg3Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, i) = (U8).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, content) = (Named("msg3_content", Msg3ContentFmt { i: i })).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Msg3 { i, content };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg3> for Msg3Fmt {
        fn serialize_into(&self, v: &Msg3, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<Msg3Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            reveal(<Msg3 as DeepView>::deep_view);
            reveal(Msg3Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Msg3 { i, content } = v;
            U8.serialize_into(i, obuf);
            Msg3ContentFmt { i: *i }.serialize_into(content, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg3> for Msg3Fmt {
        fn prepare(&self, v: &Msg3) -> Result<usize, PreSerializeError> {
            reveal(<Msg3Fmt as SpecByteLen>::byte_len);
            reveal(<Msg3 as DeepView>::deep_view);
            reveal(Msg3Spec::into_structural);
            let Msg3 { i, content } = v;
            let l1 = (U8).prepare(i)?;
            let l2 = (Named("msg3_content", Msg3ContentFmt { i: *i })).prepare(content)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg4Fmt {
        type PT = Msg4;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg4Fmt as SpecParser>::spec_parse);
            reveal(<Msg4 as DeepView>::deep_view);
            reveal(Msg4Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, i) = (U24Le).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, content) = (Named("msg4_content", Msg4ContentFmt { i: i })).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Msg4 { i, content };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg4> for Msg4Fmt {
        fn serialize_into(&self, v: &Msg4, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<Msg4Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            reveal(<Msg4 as DeepView>::deep_view);
            reveal(Msg4Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Msg4 { i, content } = v;
            U24Le.serialize_into(i, obuf);
            Msg4ContentFmt { i: *i }.serialize_into(content, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg4> for Msg4Fmt {
        fn prepare(&self, v: &Msg4) -> Result<usize, PreSerializeError> {
            reveal(<Msg4Fmt as SpecByteLen>::byte_len);
            reveal(<Msg4 as DeepView>::deep_view);
            reveal(Msg4Spec::into_structural);
            let Msg4 { i, content } = v;
            let l1 = (U24Le).prepare(i)?;
            let l2 = (Named("msg4_content", Msg4ContentFmt { i: *i })).prepare(content)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg5Fmt {
        type PT = Msg5;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Msg5Fmt as SpecParser>::spec_parse);
            reveal(<Msg5 as DeepView>::deep_view);
            reveal(Msg5Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, i) = (VarInt::<true>).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, content) = (Named("msg5_content", Msg5ContentFmt { i: i })).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Msg5 { i, content };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg5> for Msg5Fmt {
        fn serialize_into(&self, v: &Msg5, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;

            reveal(<Msg5Fmt as SpecSerializer>::spec_serialize);
            reveal(<Msg5Fmt as SpecByteLen>::byte_len);
            reveal(<Msg5 as DeepView>::deep_view);
            reveal(Msg5Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Msg5 { i, content } = v;
            VarInt::<true>.serialize_into(i, obuf);
            Msg5ContentFmt { i: *i }.serialize_into(content, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg5> for Msg5Fmt {
        fn prepare(&self, v: &Msg5) -> Result<usize, PreSerializeError> {
            reveal(<Msg5Fmt as SpecByteLen>::byte_len);
            reveal(<Msg5 as DeepView>::deep_view);
            reveal(Msg5Spec::into_structural);
            let Msg5 { i, content } = v;
            let l1 = (VarInt::<true>).prepare(i)?;
            let l2 = (Named("msg5_content", Msg5ContentFmt { i: *i })).prepare(content)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg1PayloadFmt<'i> {
        type PT = Msg1Payload;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<Msg1PayloadFmt as SpecParser>::spec_parse);
            reveal(<Msg1Payload as DeepView>::deep_view);
            reveal(Msg1PayloadSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.b {
                x if bytes_eq(
                    x,
                    &[
                        0xcf,
                        0x21,
                        0xad,
                        0x74,
                        0xe5,
                        0x9a,
                        0x61,
                        0x11,
                        0xbe,
                        0x1d,
                        0x8c,
                        0x02,
                        0x1e,
                        0x65,
                        0xb8,
                        0x91,
                        0xc2,
                        0xa2,
                        0x11,
                        0x16,
                        0x7a,
                        0xbb,
                        0x8c,
                        0x5e,
                        0x07,
                        0x9e,
                        0x09,
                        0xe2,
                        0xc8,
                        0xa8,
                        0x33,
                        0x9c,
                    ],
                ) => {
                    let (n, v) = (Named("hello_retry_request", HelloRetryRequestFmt)).parse(&rest)?;
                    (n, Msg1Payload::Variant1(v))
                },
                _ => {
                    let (n, v) = (Named("server_hello", ServerHelloFmt)).parse(&rest)?;
                    (n, Msg1Payload::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg1Payload> for Msg1PayloadFmt<'i> {
        fn serialize_into(&self, v: &Msg1Payload, obuf: &mut Output) {
            reveal(<Msg1PayloadFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg1PayloadFmt as SpecByteLen>::byte_len);
            reveal(<Msg1Payload as DeepView>::deep_view);
            reveal(Msg1PayloadSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.b, v) {
                (x, Msg1Payload::Variant1(v)) if bytes_eq(
                    x,
                    &[
                        0xcf,
                        0x21,
                        0xad,
                        0x74,
                        0xe5,
                        0x9a,
                        0x61,
                        0x11,
                        0xbe,
                        0x1d,
                        0x8c,
                        0x02,
                        0x1e,
                        0x65,
                        0xb8,
                        0x91,
                        0xc2,
                        0xa2,
                        0x11,
                        0x16,
                        0x7a,
                        0xbb,
                        0x8c,
                        0x5e,
                        0x07,
                        0x9e,
                        0x09,
                        0xe2,
                        0xc8,
                        0xa8,
                        0x33,
                        0x9c,
                    ],
                ) => {
                    (HelloRetryRequestFmt).serialize_into(v, obuf);
                },
                (_, Msg1Payload::Default(v)) => {
                    (ServerHelloFmt).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg1Payload> for Msg1PayloadFmt<'i> {
        fn prepare(&self, v: &Msg1Payload) -> Result<usize, PreSerializeError> {
            reveal(<Msg1PayloadFmt as SpecByteLen>::byte_len);
            reveal(<Msg1Payload as DeepView>::deep_view);
            reveal(Msg1PayloadSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            match (self.b, v) {
                (x, Msg1Payload::Variant1(v)) if bytes_eq(
                    x,
                    &[
                        0xcf,
                        0x21,
                        0xad,
                        0x74,
                        0xe5,
                        0x9a,
                        0x61,
                        0x11,
                        0xbe,
                        0x1d,
                        0x8c,
                        0x02,
                        0x1e,
                        0x65,
                        0xb8,
                        0x91,
                        0xc2,
                        0xa2,
                        0x11,
                        0x16,
                        0x7a,
                        0xbb,
                        0x8c,
                        0x5e,
                        0x07,
                        0x9e,
                        0x09,
                        0xe2,
                        0xc8,
                        0xa8,
                        0x33,
                        0x9c,
                    ],
                ) => (Named("hello_retry_request", HelloRetryRequestFmt)).prepare(v),
                (x, Msg1Payload::Default(v)) if !bytes_eq(
                    x,
                    &[
                        0xcf,
                        0x21,
                        0xad,
                        0x74,
                        0xe5,
                        0x9a,
                        0x61,
                        0x11,
                        0xbe,
                        0x1d,
                        0x8c,
                        0x02,
                        0x1e,
                        0x65,
                        0xb8,
                        0x91,
                        0xc2,
                        0xa2,
                        0x11,
                        0x16,
                        0x7a,
                        0xbb,
                        0x8c,
                        0x5e,
                        0x07,
                        0x9e,
                        0x09,
                        0xe2,
                        0xc8,
                        0xa8,
                        0x33,
                        0x9c,
                    ],
                ) => (Named("server_hello", ServerHelloFmt)).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg2ContentFmt<'i> {
        type PT = Msg2Content;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<Msg2ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg2Content as DeepView>::deep_view);
            reveal(Msg2ContentSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.b {
                x if bytes_eq(x, &[0x16, 0x03, 0x01]) => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, Msg2Content::Variant1(v))
                },
                x if bytes_eq(x, &[0x16, 0x03, 0x02]) => {
                    let (n, v) = (U32Le).parse(&rest)?;
                    (n, Msg2Content::Variant2(v))
                },
                x if bytes_eq(x, &[0x16, 0x03, 0x03]) => {
                    let (n, v) = (U64Le).parse(&rest)?;
                    (n, Msg2Content::Variant3(v))
                },
                _ => {
                    let (n, v) = (Empty).parse(&rest)?;
                    (n, Msg2Content::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg2Content> for Msg2ContentFmt<'i> {
        fn serialize_into(&self, v: &Msg2Content, obuf: &mut Output) {
            reveal(<Msg2ContentFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg2ContentFmt as SpecByteLen>::byte_len);
            reveal(<Msg2Content as DeepView>::deep_view);
            reveal(Msg2ContentSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.b, v) {
                (x, Msg2Content::Variant1(v)) if bytes_eq(x, &[0x16, 0x03, 0x01]) => {
                    (U16Le).serialize_into(v, obuf);
                },
                (x, Msg2Content::Variant2(v)) if bytes_eq(x, &[0x16, 0x03, 0x02]) => {
                    (U32Le).serialize_into(v, obuf);
                },
                (x, Msg2Content::Variant3(v)) if bytes_eq(x, &[0x16, 0x03, 0x03]) => {
                    (U64Le).serialize_into(v, obuf);
                },
                (_, Msg2Content::Default(v)) => {
                    (Empty).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg2Content> for Msg2ContentFmt<'i> {
        fn prepare(&self, v: &Msg2Content) -> Result<usize, PreSerializeError> {
            reveal(<Msg2ContentFmt as SpecByteLen>::byte_len);
            reveal(<Msg2Content as DeepView>::deep_view);
            reveal(Msg2ContentSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            proof {
                let ghost arr0 = [0x16u8, 0x03u8, 0x01u8].deep_view();
                let ghost arr1 = [0x16u8, 0x03u8, 0x02u8].deep_view();
                let ghost arr2 = [0x16u8, 0x03u8, 0x03u8].deep_view();
                assert(arr0 != arr1) by {
                    assert(arr0[2] != arr1[2]);
                };
                assert(arr0 != arr2) by {
                    assert(arr0[2] != arr2[2]);
                };
                assert(arr1 != arr2) by {
                    assert(arr1[2] != arr2[2]);
                };
            }

            match (self.b, v) {
                (x, Msg2Content::Variant1(v)) if bytes_eq(x, &[0x16, 0x03, 0x01]) => (
                U16Le).prepare(v),
                (x, Msg2Content::Variant2(v)) if bytes_eq(x, &[0x16, 0x03, 0x02]) => (
                U32Le).prepare(v),
                (x, Msg2Content::Variant3(v)) if bytes_eq(x, &[0x16, 0x03, 0x03]) => (
                U64Le).prepare(v),
                (x, Msg2Content::Default(v)) if !bytes_eq(x, &[0x16, 0x03, 0x01]) && !bytes_eq(
                    x,
                    &[0x16, 0x03, 0x02],
                ) && !bytes_eq(x, &[0x16, 0x03, 0x03]) => (Empty).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg3ContentFmt {
        type PT = Msg3Content;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<Msg3ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg3Content as DeepView>::deep_view);
            reveal(Msg3ContentSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.i {
                1 => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, Msg3Content::Variant1(v))
                },
                2 => {
                    let (n, v) = (U32Le).parse(&rest)?;
                    (n, Msg3Content::Variant2(v))
                },
                3 => {
                    let (n, v) = (U32Le).parse(&rest)?;
                    (n, Msg3Content::Variant3(v))
                },
                _ => {
                    let (n, v) = (Empty).parse(&rest)?;
                    (n, Msg3Content::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg3Content> for Msg3ContentFmt {
        fn serialize_into(&self, v: &Msg3Content, obuf: &mut Output) {
            reveal(<Msg3ContentFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg3ContentFmt as SpecByteLen>::byte_len);
            reveal(<Msg3Content as DeepView>::deep_view);
            reveal(Msg3ContentSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.i, v) {
                (1, Msg3Content::Variant1(v)) => {
                    (U16Le).serialize_into(v, obuf);
                },
                (2, Msg3Content::Variant2(v)) => {
                    (U32Le).serialize_into(v, obuf);
                },
                (3, Msg3Content::Variant3(v)) => {
                    (U32Le).serialize_into(v, obuf);
                },
                (_, Msg3Content::Default(v)) => {
                    (Empty).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg3Content> for Msg3ContentFmt {
        fn prepare(&self, v: &Msg3Content) -> Result<usize, PreSerializeError> {
            reveal(<Msg3ContentFmt as SpecByteLen>::byte_len);
            reveal(<Msg3Content as DeepView>::deep_view);
            reveal(Msg3ContentSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            match (self.i, v) {
                (1, Msg3Content::Variant1(v)) => (U16Le).prepare(v),
                (2, Msg3Content::Variant2(v)) => (U32Le).prepare(v),
                (3, Msg3Content::Variant3(v)) => (U32Le).prepare(v),
                (x, Msg3Content::Default(v)) if !(x == 1) && !(x == 2) && !(x == 3) => (
                Empty).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg4ContentFmt {
        type PT = Msg4Content;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<Msg4ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg4Content as DeepView>::deep_view);
            reveal(Msg4ContentSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.i {
                1 => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, Msg4Content::Variant1(v))
                },
                _ => {
                    let (n, v) = (Void("i for msg4 can only be 1")).parse(&rest)?;
                    (n, Msg4Content::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg4Content> for Msg4ContentFmt {
        fn serialize_into(&self, v: &Msg4Content, obuf: &mut Output) {
            reveal(<Msg4ContentFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg4ContentFmt as SpecByteLen>::byte_len);
            reveal(<Msg4Content as DeepView>::deep_view);
            reveal(Msg4ContentSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.i, v) {
                (1, Msg4Content::Variant1(v)) => {
                    (U16Le).serialize_into(v, obuf);
                },
                (_, Msg4Content::Default(v)) => {
                    (Void("i for msg4 can only be 1")).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg4Content> for Msg4ContentFmt {
        fn prepare(&self, v: &Msg4Content) -> Result<usize, PreSerializeError> {
            reveal(<Msg4ContentFmt as SpecByteLen>::byte_len);
            reveal(<Msg4Content as DeepView>::deep_view);
            reveal(Msg4ContentSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            match (self.i, v) {
                (1, Msg4Content::Variant1(v)) => (U16Le).prepare(v),
                (x, Msg4Content::Default(v)) if !(x == 1) => (Void(
                    "i for msg4 can only be 1",
                )).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

    impl<'i> Parser<&'i [u8]> for Msg5ContentFmt {
        type PT = Msg5Content;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<Msg5ContentFmt as SpecParser>::spec_parse);
            reveal(<Msg5Content as DeepView>::deep_view);
            reveal(Msg5ContentSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
            }

            let (n, v) = match self.i {
                2 => {
                    let (n, v) = (U16Le).parse(&rest)?;
                    (n, Msg5Content::Variant1(v))
                },
                _ => {
                    let (n, v) = (Void("i for msg5 can only be 1")).parse(&rest)?;
                    (n, Msg5Content::Default(v))
                },
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Msg5Content> for Msg5ContentFmt {
        fn serialize_into(&self, v: &Msg5Content, obuf: &mut Output) {
            reveal(<Msg5ContentFmt as SpecSerializer>::spec_serialize);
            reveal(<Msg5ContentFmt as SpecByteLen>::byte_len);
            reveal(<Msg5Content as DeepView>::deep_view);
            reveal(Msg5ContentSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            let ghost old_obuf = obuf@;

            match (self.i, v) {
                (2, Msg5Content::Variant1(v)) => {
                    (U16Le).serialize_into(v, obuf);
                },
                (_, Msg5Content::Default(v)) => {
                    (Void("i for msg5 can only be 1")).serialize_into(v, obuf);
                },
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Msg5Content> for Msg5ContentFmt {
        fn prepare(&self, v: &Msg5Content) -> Result<usize, PreSerializeError> {
            reveal(<Msg5ContentFmt as SpecByteLen>::byte_len);
            reveal(<Msg5Content as DeepView>::deep_view);
            reveal(Msg5ContentSpec::into_structural);
            proof {
                use_type_invariant(self);
            }

            match (self.i, v) {
                (2, Msg5Content::Variant1(v)) => (U16Le).prepare(v),
                (x, Msg5Content::Default(v)) if !(x == 2) => (Void(
                    "i for msg5 can only be 1",
                )).prepare(v),
                _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}

} // verus!
