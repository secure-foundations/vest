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
/// data type for `dynamic_depth0`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth0<'i> {
    pub length: u16,
    pub payload: &'i [u8],
}

#[verifier::ext_equal]
pub struct DynamicDepth0Spec<T0 = u16, T1 = Seq<u8>> {
    pub length: T0,
    pub payload: T1,
}

pub type DynamicDepth0Inner = (u16, Seq<u8>);

impl<'i> DeepView for DynamicDepth0<'i> {
    type V = DynamicDepth0Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth0Spec { length: self.length.deep_view(), payload: self.payload.deep_view() }
    }
}

/// data type for `dynamic_depth1`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth1<'i> {
    pub value: DynamicDepth0<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth1Spec<T0 = DynamicDepth0Spec> {
    pub value: T0,
}

pub type DynamicDepth1Inner = DynamicDepth0Spec;

impl<'i> DeepView for DynamicDepth1<'i> {
    type V = DynamicDepth1Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth1Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth2`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth2<'i> {
    pub value: DynamicDepth1<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth2Spec<T0 = DynamicDepth1Spec> {
    pub value: T0,
}

pub type DynamicDepth2Inner = DynamicDepth1Spec;

impl<'i> DeepView for DynamicDepth2<'i> {
    type V = DynamicDepth2Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth2Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth3`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth3<'i> {
    pub value: DynamicDepth2<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth3Spec<T0 = DynamicDepth2Spec> {
    pub value: T0,
}

pub type DynamicDepth3Inner = DynamicDepth2Spec;

impl<'i> DeepView for DynamicDepth3<'i> {
    type V = DynamicDepth3Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth3Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth4`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth4<'i> {
    pub value: DynamicDepth3<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth4Spec<T0 = DynamicDepth3Spec> {
    pub value: T0,
}

pub type DynamicDepth4Inner = DynamicDepth3Spec;

impl<'i> DeepView for DynamicDepth4<'i> {
    type V = DynamicDepth4Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth4Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth5`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth5<'i> {
    pub value: DynamicDepth4<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth5Spec<T0 = DynamicDepth4Spec> {
    pub value: T0,
}

pub type DynamicDepth5Inner = DynamicDepth4Spec;

impl<'i> DeepView for DynamicDepth5<'i> {
    type V = DynamicDepth5Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth5Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth6`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth6<'i> {
    pub value: DynamicDepth5<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth6Spec<T0 = DynamicDepth5Spec> {
    pub value: T0,
}

pub type DynamicDepth6Inner = DynamicDepth5Spec;

impl<'i> DeepView for DynamicDepth6<'i> {
    type V = DynamicDepth6Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth6Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth7`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth7<'i> {
    pub value: DynamicDepth6<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth7Spec<T0 = DynamicDepth6Spec> {
    pub value: T0,
}

pub type DynamicDepth7Inner = DynamicDepth6Spec;

impl<'i> DeepView for DynamicDepth7<'i> {
    type V = DynamicDepth7Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth7Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth8`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth8<'i> {
    pub value: DynamicDepth7<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth8Spec<T0 = DynamicDepth7Spec> {
    pub value: T0,
}

pub type DynamicDepth8Inner = DynamicDepth7Spec;

impl<'i> DeepView for DynamicDepth8<'i> {
    type V = DynamicDepth8Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth8Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth9`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth9<'i> {
    pub value: DynamicDepth8<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth9Spec<T0 = DynamicDepth8Spec> {
    pub value: T0,
}

pub type DynamicDepth9Inner = DynamicDepth8Spec;

impl<'i> DeepView for DynamicDepth9<'i> {
    type V = DynamicDepth9Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth9Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth10`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth10<'i> {
    pub value: DynamicDepth9<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth10Spec<T0 = DynamicDepth9Spec> {
    pub value: T0,
}

pub type DynamicDepth10Inner = DynamicDepth9Spec;

impl<'i> DeepView for DynamicDepth10<'i> {
    type V = DynamicDepth10Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth10Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth11`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth11<'i> {
    pub value: DynamicDepth10<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth11Spec<T0 = DynamicDepth10Spec> {
    pub value: T0,
}

pub type DynamicDepth11Inner = DynamicDepth10Spec;

impl<'i> DeepView for DynamicDepth11<'i> {
    type V = DynamicDepth11Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth11Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth12`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth12<'i> {
    pub value: DynamicDepth11<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth12Spec<T0 = DynamicDepth11Spec> {
    pub value: T0,
}

pub type DynamicDepth12Inner = DynamicDepth11Spec;

impl<'i> DeepView for DynamicDepth12<'i> {
    type V = DynamicDepth12Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth12Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth13`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth13<'i> {
    pub value: DynamicDepth12<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth13Spec<T0 = DynamicDepth12Spec> {
    pub value: T0,
}

pub type DynamicDepth13Inner = DynamicDepth12Spec;

impl<'i> DeepView for DynamicDepth13<'i> {
    type V = DynamicDepth13Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth13Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth14`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth14<'i> {
    pub value: DynamicDepth13<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth14Spec<T0 = DynamicDepth13Spec> {
    pub value: T0,
}

pub type DynamicDepth14Inner = DynamicDepth13Spec;

impl<'i> DeepView for DynamicDepth14<'i> {
    type V = DynamicDepth14Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth14Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth15`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth15<'i> {
    pub value: DynamicDepth14<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth15Spec<T0 = DynamicDepth14Spec> {
    pub value: T0,
}

pub type DynamicDepth15Inner = DynamicDepth14Spec;

impl<'i> DeepView for DynamicDepth15<'i> {
    type V = DynamicDepth15Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth15Spec { value: self.value.deep_view() }
    }
}

/// data type for `dynamic_depth16`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct DynamicDepth16<'i> {
    pub value: DynamicDepth15<'i>,
}

#[verifier::ext_equal]
pub struct DynamicDepth16Spec<T0 = DynamicDepth15Spec> {
    pub value: T0,
}

pub type DynamicDepth16Inner = DynamicDepth15Spec;

impl<'i> DeepView for DynamicDepth16<'i> {
    type V = DynamicDepth16Spec;

    #[verifier::opaque]
    open spec fn deep_view(&self) -> Self::V {
        DynamicDepth16Spec { value: self.value.deep_view() }
    }
}

// ============================================================
// Structural Mappers
// ============================================================
impl<T0, T1> DynamicDepth0Spec<T0, T1> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: (T0, T1)) -> Self {
        let (length, payload) = input;
        Self { length, payload }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> (T0, T1) {
        let Self { length, payload } = self;
        (length, payload)
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth0Spec::from_structural);
        reveal(DynamicDepth0Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: (T0, T1))
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth0Spec::from_structural);
        reveal(DynamicDepth0Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth0Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth0Reverse;

impl SpecMap for DynamicDepth0Forward {
    type Input = DynamicDepth0Inner;
    type Output = DynamicDepth0Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth0Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth0Reverse {
    type Input = DynamicDepth0Spec;
    type Output = DynamicDepth0Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth1Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth1Spec::from_structural);
        reveal(DynamicDepth1Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth1Spec::from_structural);
        reveal(DynamicDepth1Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth1Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth1Reverse;

impl SpecMap for DynamicDepth1Forward {
    type Input = DynamicDepth1Inner;
    type Output = DynamicDepth1Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth1Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth1Reverse {
    type Input = DynamicDepth1Spec;
    type Output = DynamicDepth1Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth2Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth2Spec::from_structural);
        reveal(DynamicDepth2Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth2Spec::from_structural);
        reveal(DynamicDepth2Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth2Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth2Reverse;

impl SpecMap for DynamicDepth2Forward {
    type Input = DynamicDepth2Inner;
    type Output = DynamicDepth2Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth2Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth2Reverse {
    type Input = DynamicDepth2Spec;
    type Output = DynamicDepth2Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth3Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth3Spec::from_structural);
        reveal(DynamicDepth3Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth3Spec::from_structural);
        reveal(DynamicDepth3Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth3Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth3Reverse;

impl SpecMap for DynamicDepth3Forward {
    type Input = DynamicDepth3Inner;
    type Output = DynamicDepth3Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth3Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth3Reverse {
    type Input = DynamicDepth3Spec;
    type Output = DynamicDepth3Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth4Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth4Spec::from_structural);
        reveal(DynamicDepth4Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth4Spec::from_structural);
        reveal(DynamicDepth4Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth4Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth4Reverse;

impl SpecMap for DynamicDepth4Forward {
    type Input = DynamicDepth4Inner;
    type Output = DynamicDepth4Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth4Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth4Reverse {
    type Input = DynamicDepth4Spec;
    type Output = DynamicDepth4Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth5Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth5Spec::from_structural);
        reveal(DynamicDepth5Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth5Spec::from_structural);
        reveal(DynamicDepth5Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth5Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth5Reverse;

impl SpecMap for DynamicDepth5Forward {
    type Input = DynamicDepth5Inner;
    type Output = DynamicDepth5Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth5Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth5Reverse {
    type Input = DynamicDepth5Spec;
    type Output = DynamicDepth5Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth6Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth6Spec::from_structural);
        reveal(DynamicDepth6Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth6Spec::from_structural);
        reveal(DynamicDepth6Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth6Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth6Reverse;

impl SpecMap for DynamicDepth6Forward {
    type Input = DynamicDepth6Inner;
    type Output = DynamicDepth6Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth6Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth6Reverse {
    type Input = DynamicDepth6Spec;
    type Output = DynamicDepth6Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth7Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth7Spec::from_structural);
        reveal(DynamicDepth7Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth7Spec::from_structural);
        reveal(DynamicDepth7Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth7Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth7Reverse;

impl SpecMap for DynamicDepth7Forward {
    type Input = DynamicDepth7Inner;
    type Output = DynamicDepth7Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth7Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth7Reverse {
    type Input = DynamicDepth7Spec;
    type Output = DynamicDepth7Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth8Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth8Spec::from_structural);
        reveal(DynamicDepth8Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth8Spec::from_structural);
        reveal(DynamicDepth8Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth8Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth8Reverse;

impl SpecMap for DynamicDepth8Forward {
    type Input = DynamicDepth8Inner;
    type Output = DynamicDepth8Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth8Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth8Reverse {
    type Input = DynamicDepth8Spec;
    type Output = DynamicDepth8Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth9Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth9Spec::from_structural);
        reveal(DynamicDepth9Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth9Spec::from_structural);
        reveal(DynamicDepth9Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth9Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth9Reverse;

impl SpecMap for DynamicDepth9Forward {
    type Input = DynamicDepth9Inner;
    type Output = DynamicDepth9Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth9Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth9Reverse {
    type Input = DynamicDepth9Spec;
    type Output = DynamicDepth9Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth10Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth10Spec::from_structural);
        reveal(DynamicDepth10Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth10Spec::from_structural);
        reveal(DynamicDepth10Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth10Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth10Reverse;

impl SpecMap for DynamicDepth10Forward {
    type Input = DynamicDepth10Inner;
    type Output = DynamicDepth10Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth10Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth10Reverse {
    type Input = DynamicDepth10Spec;
    type Output = DynamicDepth10Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth11Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth11Spec::from_structural);
        reveal(DynamicDepth11Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth11Spec::from_structural);
        reveal(DynamicDepth11Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth11Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth11Reverse;

impl SpecMap for DynamicDepth11Forward {
    type Input = DynamicDepth11Inner;
    type Output = DynamicDepth11Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth11Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth11Reverse {
    type Input = DynamicDepth11Spec;
    type Output = DynamicDepth11Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth12Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth12Spec::from_structural);
        reveal(DynamicDepth12Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth12Spec::from_structural);
        reveal(DynamicDepth12Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth12Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth12Reverse;

impl SpecMap for DynamicDepth12Forward {
    type Input = DynamicDepth12Inner;
    type Output = DynamicDepth12Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth12Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth12Reverse {
    type Input = DynamicDepth12Spec;
    type Output = DynamicDepth12Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth13Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth13Spec::from_structural);
        reveal(DynamicDepth13Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth13Spec::from_structural);
        reveal(DynamicDepth13Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth13Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth13Reverse;

impl SpecMap for DynamicDepth13Forward {
    type Input = DynamicDepth13Inner;
    type Output = DynamicDepth13Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth13Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth13Reverse {
    type Input = DynamicDepth13Spec;
    type Output = DynamicDepth13Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth14Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth14Spec::from_structural);
        reveal(DynamicDepth14Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth14Spec::from_structural);
        reveal(DynamicDepth14Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth14Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth14Reverse;

impl SpecMap for DynamicDepth14Forward {
    type Input = DynamicDepth14Inner;
    type Output = DynamicDepth14Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth14Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth14Reverse {
    type Input = DynamicDepth14Spec;
    type Output = DynamicDepth14Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth15Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth15Spec::from_structural);
        reveal(DynamicDepth15Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth15Spec::from_structural);
        reveal(DynamicDepth15Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth15Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth15Reverse;

impl SpecMap for DynamicDepth15Forward {
    type Input = DynamicDepth15Inner;
    type Output = DynamicDepth15Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth15Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth15Reverse {
    type Input = DynamicDepth15Spec;
    type Output = DynamicDepth15Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

impl<T0> DynamicDepth16Spec<T0> {
    #[verifier::opaque]
    pub open spec fn from_structural(input: T0) -> Self {
        let value = input;
        Self { value }
    }

    #[verifier::opaque]
    pub open spec fn into_structural(self) -> T0 {
        let Self { value } = self;
        value
    }

    pub broadcast proof fn lemma_from_into(self)
        ensures
            #[trigger] Self::from_structural(Self::into_structural(self)) == self,
    {
        reveal(DynamicDepth16Spec::from_structural);
        reveal(DynamicDepth16Spec::into_structural);
    }

    pub broadcast proof fn lemma_into_from(input: T0)
        ensures
            #[trigger] Self::into_structural(Self::from_structural(input)) == input,
    {
        reveal(DynamicDepth16Spec::from_structural);
        reveal(DynamicDepth16Spec::into_structural);
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth16Forward;
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DynamicDepth16Reverse;

impl SpecMap for DynamicDepth16Forward {
    type Input = DynamicDepth16Inner;
    type Output = DynamicDepth16Spec;

    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
        DynamicDepth16Spec::from_structural(input)
    }
}

impl SpecMap for DynamicDepth16Reverse {
    type Input = DynamicDepth16Spec;
    type Output = DynamicDepth16Inner;

    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
/// named format combinator for `dynamic_depth0`.
#[derive(Clone, Copy)]
pub struct DynamicDepth0Fmt;

pub type DynamicDepth0FmtSpec = Named<
    Mapped<
        Bind<U16Le, spec_fn(u16) -> Varied<u16>>,
        BiMap<DynamicDepth0Forward, DynamicDepth0Reverse>,
    >,
>;

impl DynamicDepth0Fmt {
    /// specification constructor for `dynamic_depth0`.
    pub open spec fn spec_inner() -> DynamicDepth0FmtSpec {
        Named(
            "dynamic_depth0",
            Mapped {
                inner: Bind(U16Le, |length: u16| Varied(length)),
                mapper: BiMap(DynamicDepth0Forward, DynamicDepth0Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth1`.
#[derive(Clone, Copy)]
pub struct DynamicDepth1Fmt;

pub type DynamicDepth1FmtSpec = Named<
    Mapped<DynamicDepth0Fmt, BiMap<DynamicDepth1Forward, DynamicDepth1Reverse>>,
>;

impl DynamicDepth1Fmt {
    /// specification constructor for `dynamic_depth1`.
    pub open spec fn spec_inner() -> DynamicDepth1FmtSpec {
        Named(
            "dynamic_depth1",
            Mapped {
                inner: DynamicDepth0Fmt,
                mapper: BiMap(DynamicDepth1Forward, DynamicDepth1Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth2`.
#[derive(Clone, Copy)]
pub struct DynamicDepth2Fmt;

pub type DynamicDepth2FmtSpec = Named<
    Mapped<DynamicDepth1Fmt, BiMap<DynamicDepth2Forward, DynamicDepth2Reverse>>,
>;

impl DynamicDepth2Fmt {
    /// specification constructor for `dynamic_depth2`.
    pub open spec fn spec_inner() -> DynamicDepth2FmtSpec {
        Named(
            "dynamic_depth2",
            Mapped {
                inner: DynamicDepth1Fmt,
                mapper: BiMap(DynamicDepth2Forward, DynamicDepth2Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth3`.
#[derive(Clone, Copy)]
pub struct DynamicDepth3Fmt;

pub type DynamicDepth3FmtSpec = Named<
    Mapped<DynamicDepth2Fmt, BiMap<DynamicDepth3Forward, DynamicDepth3Reverse>>,
>;

impl DynamicDepth3Fmt {
    /// specification constructor for `dynamic_depth3`.
    pub open spec fn spec_inner() -> DynamicDepth3FmtSpec {
        Named(
            "dynamic_depth3",
            Mapped {
                inner: DynamicDepth2Fmt,
                mapper: BiMap(DynamicDepth3Forward, DynamicDepth3Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth4`.
#[derive(Clone, Copy)]
pub struct DynamicDepth4Fmt;

pub type DynamicDepth4FmtSpec = Named<
    Mapped<DynamicDepth3Fmt, BiMap<DynamicDepth4Forward, DynamicDepth4Reverse>>,
>;

impl DynamicDepth4Fmt {
    /// specification constructor for `dynamic_depth4`.
    pub open spec fn spec_inner() -> DynamicDepth4FmtSpec {
        Named(
            "dynamic_depth4",
            Mapped {
                inner: DynamicDepth3Fmt,
                mapper: BiMap(DynamicDepth4Forward, DynamicDepth4Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth5`.
#[derive(Clone, Copy)]
pub struct DynamicDepth5Fmt;

pub type DynamicDepth5FmtSpec = Named<
    Mapped<DynamicDepth4Fmt, BiMap<DynamicDepth5Forward, DynamicDepth5Reverse>>,
>;

impl DynamicDepth5Fmt {
    /// specification constructor for `dynamic_depth5`.
    pub open spec fn spec_inner() -> DynamicDepth5FmtSpec {
        Named(
            "dynamic_depth5",
            Mapped {
                inner: DynamicDepth4Fmt,
                mapper: BiMap(DynamicDepth5Forward, DynamicDepth5Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth6`.
#[derive(Clone, Copy)]
pub struct DynamicDepth6Fmt;

pub type DynamicDepth6FmtSpec = Named<
    Mapped<DynamicDepth5Fmt, BiMap<DynamicDepth6Forward, DynamicDepth6Reverse>>,
>;

impl DynamicDepth6Fmt {
    /// specification constructor for `dynamic_depth6`.
    pub open spec fn spec_inner() -> DynamicDepth6FmtSpec {
        Named(
            "dynamic_depth6",
            Mapped {
                inner: DynamicDepth5Fmt,
                mapper: BiMap(DynamicDepth6Forward, DynamicDepth6Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth7`.
#[derive(Clone, Copy)]
pub struct DynamicDepth7Fmt;

pub type DynamicDepth7FmtSpec = Named<
    Mapped<DynamicDepth6Fmt, BiMap<DynamicDepth7Forward, DynamicDepth7Reverse>>,
>;

impl DynamicDepth7Fmt {
    /// specification constructor for `dynamic_depth7`.
    pub open spec fn spec_inner() -> DynamicDepth7FmtSpec {
        Named(
            "dynamic_depth7",
            Mapped {
                inner: DynamicDepth6Fmt,
                mapper: BiMap(DynamicDepth7Forward, DynamicDepth7Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth8`.
#[derive(Clone, Copy)]
pub struct DynamicDepth8Fmt;

pub type DynamicDepth8FmtSpec = Named<
    Mapped<DynamicDepth7Fmt, BiMap<DynamicDepth8Forward, DynamicDepth8Reverse>>,
>;

impl DynamicDepth8Fmt {
    /// specification constructor for `dynamic_depth8`.
    pub open spec fn spec_inner() -> DynamicDepth8FmtSpec {
        Named(
            "dynamic_depth8",
            Mapped {
                inner: DynamicDepth7Fmt,
                mapper: BiMap(DynamicDepth8Forward, DynamicDepth8Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth9`.
#[derive(Clone, Copy)]
pub struct DynamicDepth9Fmt;

pub type DynamicDepth9FmtSpec = Named<
    Mapped<DynamicDepth8Fmt, BiMap<DynamicDepth9Forward, DynamicDepth9Reverse>>,
>;

impl DynamicDepth9Fmt {
    /// specification constructor for `dynamic_depth9`.
    pub open spec fn spec_inner() -> DynamicDepth9FmtSpec {
        Named(
            "dynamic_depth9",
            Mapped {
                inner: DynamicDepth8Fmt,
                mapper: BiMap(DynamicDepth9Forward, DynamicDepth9Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth10`.
#[derive(Clone, Copy)]
pub struct DynamicDepth10Fmt;

pub type DynamicDepth10FmtSpec = Named<
    Mapped<DynamicDepth9Fmt, BiMap<DynamicDepth10Forward, DynamicDepth10Reverse>>,
>;

impl DynamicDepth10Fmt {
    /// specification constructor for `dynamic_depth10`.
    pub open spec fn spec_inner() -> DynamicDepth10FmtSpec {
        Named(
            "dynamic_depth10",
            Mapped {
                inner: DynamicDepth9Fmt,
                mapper: BiMap(DynamicDepth10Forward, DynamicDepth10Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth11`.
#[derive(Clone, Copy)]
pub struct DynamicDepth11Fmt;

pub type DynamicDepth11FmtSpec = Named<
    Mapped<DynamicDepth10Fmt, BiMap<DynamicDepth11Forward, DynamicDepth11Reverse>>,
>;

impl DynamicDepth11Fmt {
    /// specification constructor for `dynamic_depth11`.
    pub open spec fn spec_inner() -> DynamicDepth11FmtSpec {
        Named(
            "dynamic_depth11",
            Mapped {
                inner: DynamicDepth10Fmt,
                mapper: BiMap(DynamicDepth11Forward, DynamicDepth11Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth12`.
#[derive(Clone, Copy)]
pub struct DynamicDepth12Fmt;

pub type DynamicDepth12FmtSpec = Named<
    Mapped<DynamicDepth11Fmt, BiMap<DynamicDepth12Forward, DynamicDepth12Reverse>>,
>;

impl DynamicDepth12Fmt {
    /// specification constructor for `dynamic_depth12`.
    pub open spec fn spec_inner() -> DynamicDepth12FmtSpec {
        Named(
            "dynamic_depth12",
            Mapped {
                inner: DynamicDepth11Fmt,
                mapper: BiMap(DynamicDepth12Forward, DynamicDepth12Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth13`.
#[derive(Clone, Copy)]
pub struct DynamicDepth13Fmt;

pub type DynamicDepth13FmtSpec = Named<
    Mapped<DynamicDepth12Fmt, BiMap<DynamicDepth13Forward, DynamicDepth13Reverse>>,
>;

impl DynamicDepth13Fmt {
    /// specification constructor for `dynamic_depth13`.
    pub open spec fn spec_inner() -> DynamicDepth13FmtSpec {
        Named(
            "dynamic_depth13",
            Mapped {
                inner: DynamicDepth12Fmt,
                mapper: BiMap(DynamicDepth13Forward, DynamicDepth13Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth14`.
#[derive(Clone, Copy)]
pub struct DynamicDepth14Fmt;

pub type DynamicDepth14FmtSpec = Named<
    Mapped<DynamicDepth13Fmt, BiMap<DynamicDepth14Forward, DynamicDepth14Reverse>>,
>;

impl DynamicDepth14Fmt {
    /// specification constructor for `dynamic_depth14`.
    pub open spec fn spec_inner() -> DynamicDepth14FmtSpec {
        Named(
            "dynamic_depth14",
            Mapped {
                inner: DynamicDepth13Fmt,
                mapper: BiMap(DynamicDepth14Forward, DynamicDepth14Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth15`.
#[derive(Clone, Copy)]
pub struct DynamicDepth15Fmt;

pub type DynamicDepth15FmtSpec = Named<
    Mapped<DynamicDepth14Fmt, BiMap<DynamicDepth15Forward, DynamicDepth15Reverse>>,
>;

impl DynamicDepth15Fmt {
    /// specification constructor for `dynamic_depth15`.
    pub open spec fn spec_inner() -> DynamicDepth15FmtSpec {
        Named(
            "dynamic_depth15",
            Mapped {
                inner: DynamicDepth14Fmt,
                mapper: BiMap(DynamicDepth15Forward, DynamicDepth15Reverse),
            },
        )
    }
}

/// named format combinator for `dynamic_depth16`.
#[derive(Clone, Copy)]
pub struct DynamicDepth16Fmt;

pub type DynamicDepth16FmtSpec = Named<
    Mapped<DynamicDepth15Fmt, BiMap<DynamicDepth16Forward, DynamicDepth16Reverse>>,
>;

impl DynamicDepth16Fmt {
    /// specification constructor for `dynamic_depth16`.
    pub open spec fn spec_inner() -> DynamicDepth16FmtSpec {
        Named(
            "dynamic_depth16",
            Mapped {
                inner: DynamicDepth15Fmt,
                mapper: BiMap(DynamicDepth16Forward, DynamicDepth16Reverse),
            },
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for DynamicDepth0Fmt {
        type PVal = DynamicDepth0Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth0Fmt {
        type Val = DynamicDepth0Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent((v.length, v.payload))
        }
    }

    impl SpecSerializerDps for DynamicDepth0Fmt {
        type SValue = DynamicDepth0Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth0Fmt {
        type SVal = DynamicDepth0Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth0Fmt {
        type T = DynamicDepth0Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len((v.length, v.payload))
        }
    }

    impl SpecParser for DynamicDepth1Fmt {
        type PVal = DynamicDepth1Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth1Fmt {
        type Val = DynamicDepth1Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth1Fmt {
        type SValue = DynamicDepth1Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth1Fmt {
        type SVal = DynamicDepth1Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth1Fmt {
        type T = DynamicDepth1Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth2Fmt {
        type PVal = DynamicDepth2Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth2Fmt {
        type Val = DynamicDepth2Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth2Fmt {
        type SValue = DynamicDepth2Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth2Fmt {
        type SVal = DynamicDepth2Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth2Fmt {
        type T = DynamicDepth2Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth3Fmt {
        type PVal = DynamicDepth3Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth3Fmt {
        type Val = DynamicDepth3Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth3Fmt {
        type SValue = DynamicDepth3Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth3Fmt {
        type SVal = DynamicDepth3Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth3Fmt {
        type T = DynamicDepth3Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth4Fmt {
        type PVal = DynamicDepth4Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth4Fmt {
        type Val = DynamicDepth4Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth4Fmt {
        type SValue = DynamicDepth4Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth4Fmt {
        type SVal = DynamicDepth4Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth4Fmt {
        type T = DynamicDepth4Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth5Fmt {
        type PVal = DynamicDepth5Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth5Fmt {
        type Val = DynamicDepth5Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth5Fmt {
        type SValue = DynamicDepth5Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth5Fmt {
        type SVal = DynamicDepth5Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth5Fmt {
        type T = DynamicDepth5Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth6Fmt {
        type PVal = DynamicDepth6Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth6Fmt {
        type Val = DynamicDepth6Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth6Fmt {
        type SValue = DynamicDepth6Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth6Fmt {
        type SVal = DynamicDepth6Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth6Fmt {
        type T = DynamicDepth6Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth7Fmt {
        type PVal = DynamicDepth7Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth7Fmt {
        type Val = DynamicDepth7Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth7Fmt {
        type SValue = DynamicDepth7Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth7Fmt {
        type SVal = DynamicDepth7Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth7Fmt {
        type T = DynamicDepth7Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth8Fmt {
        type PVal = DynamicDepth8Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth8Fmt {
        type Val = DynamicDepth8Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth8Fmt {
        type SValue = DynamicDepth8Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth8Fmt {
        type SVal = DynamicDepth8Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth8Fmt {
        type T = DynamicDepth8Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth9Fmt {
        type PVal = DynamicDepth9Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth9Fmt {
        type Val = DynamicDepth9Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth9Fmt {
        type SValue = DynamicDepth9Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth9Fmt {
        type SVal = DynamicDepth9Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth9Fmt {
        type T = DynamicDepth9Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth10Fmt {
        type PVal = DynamicDepth10Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth10Fmt {
        type Val = DynamicDepth10Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth10Fmt {
        type SValue = DynamicDepth10Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth10Fmt {
        type SVal = DynamicDepth10Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth10Fmt {
        type T = DynamicDepth10Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth11Fmt {
        type PVal = DynamicDepth11Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth11Fmt {
        type Val = DynamicDepth11Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth11Fmt {
        type SValue = DynamicDepth11Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth11Fmt {
        type SVal = DynamicDepth11Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth11Fmt {
        type T = DynamicDepth11Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth12Fmt {
        type PVal = DynamicDepth12Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth12Fmt {
        type Val = DynamicDepth12Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth12Fmt {
        type SValue = DynamicDepth12Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth12Fmt {
        type SVal = DynamicDepth12Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth12Fmt {
        type T = DynamicDepth12Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth13Fmt {
        type PVal = DynamicDepth13Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth13Fmt {
        type Val = DynamicDepth13Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth13Fmt {
        type SValue = DynamicDepth13Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth13Fmt {
        type SVal = DynamicDepth13Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth13Fmt {
        type T = DynamicDepth13Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth14Fmt {
        type PVal = DynamicDepth14Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth14Fmt {
        type Val = DynamicDepth14Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth14Fmt {
        type SValue = DynamicDepth14Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth14Fmt {
        type SVal = DynamicDepth14Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth14Fmt {
        type T = DynamicDepth14Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth15Fmt {
        type PVal = DynamicDepth15Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth15Fmt {
        type Val = DynamicDepth15Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth15Fmt {
        type SValue = DynamicDepth15Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth15Fmt {
        type SVal = DynamicDepth15Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth15Fmt {
        type T = DynamicDepth15Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
        }
    }

    impl SpecParser for DynamicDepth16Fmt {
        type PVal = DynamicDepth16Spec;

        #[verifier::opaque]
        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            Self::spec_inner().spec_parse(ibuf)
        }
    }

    impl Consistency for DynamicDepth16Fmt {
        type Val = DynamicDepth16Spec;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            Self::spec_inner().1.inner.consistent(v.value)
        }
    }

    impl SpecSerializerDps for DynamicDepth16Fmt {
        type SValue = DynamicDepth16Spec;

        #[verifier::opaque]
        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            Self::spec_inner().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for DynamicDepth16Fmt {
        type SVal = DynamicDepth16Spec;

        #[verifier::opaque]
        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            Self::spec_inner().spec_serialize(v)
        }
    }

    impl SpecByteLen for DynamicDepth16Fmt {
        type T = DynamicDepth16Spec;

        #[verifier::opaque]
        open spec fn byte_len(&self, v: Self::T) -> nat {
            Self::spec_inner().1.inner.byte_len(v.value)
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
        DynamicDepth0Spec::lemma_from_into,
        DynamicDepth0Spec::lemma_into_from,
        DynamicDepth1Spec::lemma_from_into,
        DynamicDepth1Spec::lemma_into_from,
        DynamicDepth2Spec::lemma_from_into,
        DynamicDepth2Spec::lemma_into_from,
        DynamicDepth3Spec::lemma_from_into,
        DynamicDepth3Spec::lemma_into_from,
        DynamicDepth4Spec::lemma_from_into,
        DynamicDepth4Spec::lemma_into_from,
        DynamicDepth5Spec::lemma_from_into,
        DynamicDepth5Spec::lemma_into_from,
        DynamicDepth6Spec::lemma_from_into,
        DynamicDepth6Spec::lemma_into_from,
        DynamicDepth7Spec::lemma_from_into,
        DynamicDepth7Spec::lemma_into_from,
        DynamicDepth8Spec::lemma_from_into,
        DynamicDepth8Spec::lemma_into_from,
        DynamicDepth9Spec::lemma_from_into,
        DynamicDepth9Spec::lemma_into_from,
        DynamicDepth10Spec::lemma_from_into,
        DynamicDepth10Spec::lemma_into_from,
        DynamicDepth11Spec::lemma_from_into,
        DynamicDepth11Spec::lemma_into_from,
        DynamicDepth12Spec::lemma_from_into,
        DynamicDepth12Spec::lemma_into_from,
        DynamicDepth13Spec::lemma_from_into,
        DynamicDepth13Spec::lemma_into_from,
        DynamicDepth14Spec::lemma_from_into,
        DynamicDepth14Spec::lemma_into_from,
        DynamicDepth15Spec::lemma_from_into,
        DynamicDepth15Spec::lemma_into_from,
        DynamicDepth16Spec::lemma_from_into,
        DynamicDepth16Spec::lemma_into_from,
    };

    impl SafeParser for DynamicDepth0Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth0Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth0Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth0Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth0Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth0Spec::into_structural);
            reveal(<DynamicDepth0Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth0Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth0Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth0Spec::into_structural);
            reveal(<DynamicDepth0Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth0Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth0Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth0Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth0Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth0Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth0Spec::into_structural);
            reveal(<DynamicDepth0Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth0Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth0Spec::into_structural);
            reveal(<DynamicDepth0Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth0Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth0Spec::into_structural);
            reveal(<DynamicDepth0Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth0Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth0Fmt as Consistency>::consistent);
            reveal(<DynamicDepth0Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth0Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth0Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth0Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth0Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth0Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth0Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth0Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth0Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth0Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth0Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth0Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth0Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth1Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth1Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth1Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth1Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth1Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth1Spec::into_structural);
            reveal(<DynamicDepth1Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth1Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth1Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth1Spec::into_structural);
            reveal(<DynamicDepth1Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth1Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth1Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth1Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth1Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth1Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth1Spec::into_structural);
            reveal(<DynamicDepth1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth1Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth1Spec::into_structural);
            reveal(<DynamicDepth1Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth1Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth1Spec::into_structural);
            reveal(<DynamicDepth1Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth1Fmt as Consistency>::consistent);
            reveal(<DynamicDepth1Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth1Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth1Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth1Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth1Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth1Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth1Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth1Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth1Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth1Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth1Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth1Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth2Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth2Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth2Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth2Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth2Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth2Spec::into_structural);
            reveal(<DynamicDepth2Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth2Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth2Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth2Spec::into_structural);
            reveal(<DynamicDepth2Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth2Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth2Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth2Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth2Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth2Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth2Spec::into_structural);
            reveal(<DynamicDepth2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth2Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth2Spec::into_structural);
            reveal(<DynamicDepth2Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth2Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth2Spec::into_structural);
            reveal(<DynamicDepth2Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth2Fmt as Consistency>::consistent);
            reveal(<DynamicDepth2Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth2Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth2Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth2Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth2Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth2Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth2Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth2Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth2Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth2Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth2Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth2Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth3Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth3Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth3Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth3Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth3Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth3Spec::into_structural);
            reveal(<DynamicDepth3Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth3Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth3Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth3Spec::into_structural);
            reveal(<DynamicDepth3Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth3Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth3Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth3Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth3Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth3Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth3Spec::into_structural);
            reveal(<DynamicDepth3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth3Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth3Spec::into_structural);
            reveal(<DynamicDepth3Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth3Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth3Spec::into_structural);
            reveal(<DynamicDepth3Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth3Fmt as Consistency>::consistent);
            reveal(<DynamicDepth3Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth3Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth3Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth3Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth3Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth3Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth3Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth3Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth3Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth3Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth3Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth3Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth4Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth4Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth4Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth4Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth4Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth4Spec::into_structural);
            reveal(<DynamicDepth4Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth4Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth4Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth4Spec::into_structural);
            reveal(<DynamicDepth4Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth4Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth4Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth4Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth4Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth4Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth4Spec::into_structural);
            reveal(<DynamicDepth4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth4Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth4Spec::into_structural);
            reveal(<DynamicDepth4Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth4Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth4Spec::into_structural);
            reveal(<DynamicDepth4Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth4Fmt as Consistency>::consistent);
            reveal(<DynamicDepth4Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth4Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth4Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth4Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth4Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth4Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth4Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth4Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth4Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth4Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth4Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth4Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth5Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth5Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth5Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth5Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth5Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth5Spec::into_structural);
            reveal(<DynamicDepth5Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth5Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth5Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth5Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth5Spec::into_structural);
            reveal(<DynamicDepth5Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth5Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth5Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth5Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth5Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth5Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth5Spec::into_structural);
            reveal(<DynamicDepth5Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth5Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth5Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth5Spec::into_structural);
            reveal(<DynamicDepth5Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth5Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth5Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth5Spec::into_structural);
            reveal(<DynamicDepth5Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth5Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth5Fmt as Consistency>::consistent);
            reveal(<DynamicDepth5Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth5Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth5Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth5Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth5Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth5Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth5Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth5Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth5Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth5Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth5Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth5Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth5Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth6Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth6Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth6Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth6Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth6Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth6Spec::into_structural);
            reveal(<DynamicDepth6Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth6Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth6Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth6Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth6Spec::into_structural);
            reveal(<DynamicDepth6Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth6Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth6Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth6Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth6Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth6Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth6Spec::into_structural);
            reveal(<DynamicDepth6Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth6Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth6Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth6Spec::into_structural);
            reveal(<DynamicDepth6Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth6Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth6Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth6Spec::into_structural);
            reveal(<DynamicDepth6Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth6Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth6Fmt as Consistency>::consistent);
            reveal(<DynamicDepth6Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth6Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth6Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth6Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth6Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth6Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth6Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth6Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth6Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth6Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth6Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth6Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth6Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth7Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth7Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth7Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth7Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth7Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth7Spec::into_structural);
            reveal(<DynamicDepth7Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth7Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth7Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth7Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth7Spec::into_structural);
            reveal(<DynamicDepth7Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth7Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth7Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth7Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth7Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth7Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth7Spec::into_structural);
            reveal(<DynamicDepth7Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth7Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth7Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth7Spec::into_structural);
            reveal(<DynamicDepth7Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth7Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth7Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth7Spec::into_structural);
            reveal(<DynamicDepth7Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth7Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth7Fmt as Consistency>::consistent);
            reveal(<DynamicDepth7Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth7Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth7Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth7Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth7Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth7Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth7Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth7Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth7Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth7Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth7Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth7Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth7Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth8Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth8Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth8Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth8Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth8Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth8Spec::into_structural);
            reveal(<DynamicDepth8Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth8Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth8Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth8Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth8Spec::into_structural);
            reveal(<DynamicDepth8Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth8Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth8Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth8Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth8Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth8Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth8Spec::into_structural);
            reveal(<DynamicDepth8Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth8Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth8Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth8Spec::into_structural);
            reveal(<DynamicDepth8Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth8Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth8Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth8Spec::into_structural);
            reveal(<DynamicDepth8Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth8Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth8Fmt as Consistency>::consistent);
            reveal(<DynamicDepth8Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth8Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth8Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth8Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth8Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth8Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth8Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth8Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth8Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth8Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth8Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth8Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth8Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth9Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth9Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth9Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth9Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth9Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth9Spec::into_structural);
            reveal(<DynamicDepth9Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth9Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth9Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth9Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth9Spec::into_structural);
            reveal(<DynamicDepth9Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth9Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth9Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth9Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth9Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth9Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth9Spec::into_structural);
            reveal(<DynamicDepth9Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth9Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth9Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth9Spec::into_structural);
            reveal(<DynamicDepth9Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth9Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth9Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth9Spec::into_structural);
            reveal(<DynamicDepth9Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth9Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth9Fmt as Consistency>::consistent);
            reveal(<DynamicDepth9Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth9Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth9Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth9Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth9Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth9Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth9Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth9Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth9Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth9Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth9Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth9Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth9Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth10Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth10Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth10Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth10Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth10Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth10Spec::into_structural);
            reveal(<DynamicDepth10Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth10Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth10Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth10Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth10Spec::into_structural);
            reveal(<DynamicDepth10Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth10Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth10Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth10Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth10Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth10Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth10Spec::into_structural);
            reveal(<DynamicDepth10Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth10Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth10Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth10Spec::into_structural);
            reveal(<DynamicDepth10Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth10Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth10Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth10Spec::into_structural);
            reveal(<DynamicDepth10Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth10Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth10Fmt as Consistency>::consistent);
            reveal(<DynamicDepth10Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth10Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth10Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth10Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth10Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth10Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth10Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth10Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth10Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth10Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth10Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth10Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth10Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth11Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth11Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth11Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth11Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth11Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth11Spec::into_structural);
            reveal(<DynamicDepth11Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth11Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth11Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth11Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth11Spec::into_structural);
            reveal(<DynamicDepth11Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth11Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth11Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth11Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth11Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth11Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth11Spec::into_structural);
            reveal(<DynamicDepth11Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth11Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth11Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth11Spec::into_structural);
            reveal(<DynamicDepth11Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth11Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth11Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth11Spec::into_structural);
            reveal(<DynamicDepth11Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth11Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth11Fmt as Consistency>::consistent);
            reveal(<DynamicDepth11Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth11Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth11Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth11Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth11Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth11Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth11Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth11Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth11Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth11Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth11Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth11Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth11Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth12Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth12Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth12Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth12Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth12Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth12Spec::into_structural);
            reveal(<DynamicDepth12Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth12Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth12Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth12Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth12Spec::into_structural);
            reveal(<DynamicDepth12Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth12Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth12Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth12Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth12Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth12Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth12Spec::into_structural);
            reveal(<DynamicDepth12Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth12Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth12Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth12Spec::into_structural);
            reveal(<DynamicDepth12Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth12Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth12Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth12Spec::into_structural);
            reveal(<DynamicDepth12Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth12Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth12Fmt as Consistency>::consistent);
            reveal(<DynamicDepth12Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth12Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth12Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth12Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth12Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth12Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth12Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth12Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth12Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth12Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth12Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth12Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth12Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth13Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth13Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth13Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth13Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth13Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth13Spec::into_structural);
            reveal(<DynamicDepth13Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth13Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth13Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth13Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth13Spec::into_structural);
            reveal(<DynamicDepth13Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth13Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth13Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth13Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth13Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth13Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth13Spec::into_structural);
            reveal(<DynamicDepth13Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth13Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth13Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth13Spec::into_structural);
            reveal(<DynamicDepth13Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth13Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth13Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth13Spec::into_structural);
            reveal(<DynamicDepth13Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth13Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth13Fmt as Consistency>::consistent);
            reveal(<DynamicDepth13Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth13Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth13Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth13Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth13Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth13Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth13Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth13Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth13Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth13Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth13Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth13Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth13Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth14Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth14Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth14Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth14Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth14Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth14Spec::into_structural);
            reveal(<DynamicDepth14Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth14Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth14Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth14Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth14Spec::into_structural);
            reveal(<DynamicDepth14Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth14Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth14Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth14Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth14Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth14Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth14Spec::into_structural);
            reveal(<DynamicDepth14Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth14Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth14Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth14Spec::into_structural);
            reveal(<DynamicDepth14Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth14Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth14Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth14Spec::into_structural);
            reveal(<DynamicDepth14Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth14Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth14Fmt as Consistency>::consistent);
            reveal(<DynamicDepth14Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth14Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth14Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth14Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth14Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth14Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth14Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth14Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth14Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth14Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth14Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth14Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth14Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth15Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth15Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth15Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth15Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth15Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth15Spec::into_structural);
            reveal(<DynamicDepth15Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth15Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth15Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth15Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth15Spec::into_structural);
            reveal(<DynamicDepth15Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth15Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth15Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth15Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth15Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth15Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth15Spec::into_structural);
            reveal(<DynamicDepth15Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth15Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth15Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth15Spec::into_structural);
            reveal(<DynamicDepth15Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth15Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth15Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth15Spec::into_structural);
            reveal(<DynamicDepth15Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth15Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth15Fmt as Consistency>::consistent);
            reveal(<DynamicDepth15Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth15Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth15Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth15Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth15Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth15Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth15Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth15Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth15Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth15Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth15Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth15Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth15Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_inv());
            fmt.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for DynamicDepth16Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            reveal(<DynamicDepth16Fmt as SpecParser>::spec_parse);
            Self::spec_inner().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for DynamicDepth16Fmt {
        open spec fn productive_inv(&self) -> bool {
            Self::spec_inner().productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            reveal(<DynamicDepth16Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert(fmt.productive_inv());
            fmt.lemma_productive(s);
        }
    }

    impl SoundParser for DynamicDepth16Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth16Spec::into_structural);
            reveal(<DynamicDepth16Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth16Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth16Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth16Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            reveal(DynamicDepth16Spec::into_structural);
            reveal(<DynamicDepth16Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth16Fmt as Consistency>::consistent);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth16Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth16Spec::lemma_into_from(input);
            }
            assert(fmt.sound_inv());
            fmt.lemma_parse_sound_value(ibuf);
        }
    }

    impl NonTailFmt for DynamicDepth16Fmt {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(<DynamicDepth16Fmt as SpecSerializerDps>::spec_serialize_dps);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            reveal(DynamicDepth16Spec::into_structural);
            reveal(<DynamicDepth16Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth16Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_dps_inv());
            fmt.lemma_serialize_dps_len(v, obuf);
        }
    }

    impl GoodSerializer for DynamicDepth16Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            reveal(DynamicDepth16Spec::into_structural);
            reveal(<DynamicDepth16Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth16Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert(fmt.serialize_inv());
            fmt.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for DynamicDepth16Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            reveal(DynamicDepth16Spec::into_structural);
            reveal(<DynamicDepth16Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth16Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth16Fmt as Consistency>::consistent);
            reveal(<DynamicDepth16Fmt as SpecByteLen>::byte_len);
            let fmt = Self::spec_inner();
            assert forall|output: DynamicDepth16Spec|
                #[trigger] fmt.1.consistent(output) implies fmt.1.mapper.sound(output) by {
                DynamicDepth16Spec::lemma_from_into(output);
            }
            assert(fmt.unambiguous());
            fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for DynamicDepth16Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            reveal(<DynamicDepth16Fmt as SpecParser>::spec_parse);
            let fmt = Self::spec_inner();
            assert forall|input: DynamicDepth16Inner|
                #[trigger] fmt.1.inner.consistent(input) implies fmt.1.mapper.lossless(input) by {
                DynamicDepth16Spec::lemma_into_from(input);
            }
            assert(fmt.nonmal_inv());
            fmt.lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializersGeneral for DynamicDepth16Fmt {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            reveal(<DynamicDepth16Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth16Fmt as SpecSerializer>::spec_serialize);
            let fmt = Self::spec_inner();
            assert(fmt.equiv_general_inv());
            fmt.lemma_serialize_equiv(v, obuf);
        }
    }

    impl EquivSerializers for DynamicDepth16Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            reveal(<DynamicDepth16Fmt as SpecSerializerDps>::spec_serialize_dps);
            reveal(<DynamicDepth16Fmt as SpecSerializer>::spec_serialize);
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

    impl<'i> Parser<&'i [u8]> for DynamicDepth0Fmt {
        type PT = DynamicDepth0<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth0Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth0 as DeepView>::deep_view);
            reveal(DynamicDepth0Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, length) = (U16Le).parse(&rest)?;
            let rest = rest.skip(n1);
            let (n2, payload) = (Varied(length)).parse(&rest)?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;

            let final_v = DynamicDepth0 { length, payload };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth0<'i>> for DynamicDepth0Fmt {
        fn serialize_into(&self, v: &DynamicDepth0<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth0Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth0Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth0 as DeepView>::deep_view);
            reveal(DynamicDepth0Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth0 { length, payload } = v;

            U16Le.serialize_into(length, obuf);
            Varied(*length).serialize_into(*payload, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth0<'i>> for DynamicDepth0Fmt {
        fn prepare(&self, v: &DynamicDepth0<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth0Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth0 as DeepView>::deep_view);
            reveal(DynamicDepth0Spec::into_structural);
            let DynamicDepth0 { length, payload } = v;
            let l1 = (U16Le).prepare(length)?;
            let l2 = (Varied(*length)).prepare(payload)?;
            let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth1Fmt {
        type PT = DynamicDepth1<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth1Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth1 as DeepView>::deep_view);
            reveal(DynamicDepth1Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth0", DynamicDepth0Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth1 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth1<'i>> for DynamicDepth1Fmt {
        fn serialize_into(&self, v: &DynamicDepth1<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth1Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth1Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth1 as DeepView>::deep_view);
            reveal(DynamicDepth1Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth1 { value } = v;

            DynamicDepth0Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth1<'i>> for DynamicDepth1Fmt {
        fn prepare(&self, v: &DynamicDepth1<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth1Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth1 as DeepView>::deep_view);
            reveal(DynamicDepth1Spec::into_structural);
            let DynamicDepth1 { value } = v;
            let l1 = (Named("dynamic_depth0", DynamicDepth0Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth2Fmt {
        type PT = DynamicDepth2<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth2Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth2 as DeepView>::deep_view);
            reveal(DynamicDepth2Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth1", DynamicDepth1Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth2 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth2<'i>> for DynamicDepth2Fmt {
        fn serialize_into(&self, v: &DynamicDepth2<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth2Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth2Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth2 as DeepView>::deep_view);
            reveal(DynamicDepth2Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth2 { value } = v;

            DynamicDepth1Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth2<'i>> for DynamicDepth2Fmt {
        fn prepare(&self, v: &DynamicDepth2<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth2Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth2 as DeepView>::deep_view);
            reveal(DynamicDepth2Spec::into_structural);
            let DynamicDepth2 { value } = v;
            let l1 = (Named("dynamic_depth1", DynamicDepth1Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth3Fmt {
        type PT = DynamicDepth3<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth3Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth3 as DeepView>::deep_view);
            reveal(DynamicDepth3Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth2", DynamicDepth2Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth3 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth3<'i>> for DynamicDepth3Fmt {
        fn serialize_into(&self, v: &DynamicDepth3<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth3Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth3Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth3 as DeepView>::deep_view);
            reveal(DynamicDepth3Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth3 { value } = v;

            DynamicDepth2Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth3<'i>> for DynamicDepth3Fmt {
        fn prepare(&self, v: &DynamicDepth3<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth3Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth3 as DeepView>::deep_view);
            reveal(DynamicDepth3Spec::into_structural);
            let DynamicDepth3 { value } = v;
            let l1 = (Named("dynamic_depth2", DynamicDepth2Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth4Fmt {
        type PT = DynamicDepth4<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth4Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth4 as DeepView>::deep_view);
            reveal(DynamicDepth4Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth3", DynamicDepth3Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth4 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth4<'i>> for DynamicDepth4Fmt {
        fn serialize_into(&self, v: &DynamicDepth4<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth4Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth4Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth4 as DeepView>::deep_view);
            reveal(DynamicDepth4Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth4 { value } = v;

            DynamicDepth3Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth4<'i>> for DynamicDepth4Fmt {
        fn prepare(&self, v: &DynamicDepth4<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth4Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth4 as DeepView>::deep_view);
            reveal(DynamicDepth4Spec::into_structural);
            let DynamicDepth4 { value } = v;
            let l1 = (Named("dynamic_depth3", DynamicDepth3Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth5Fmt {
        type PT = DynamicDepth5<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth5Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth5 as DeepView>::deep_view);
            reveal(DynamicDepth5Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth4", DynamicDepth4Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth5 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth5<'i>> for DynamicDepth5Fmt {
        fn serialize_into(&self, v: &DynamicDepth5<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth5Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth5Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth5 as DeepView>::deep_view);
            reveal(DynamicDepth5Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth5 { value } = v;

            DynamicDepth4Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth5<'i>> for DynamicDepth5Fmt {
        fn prepare(&self, v: &DynamicDepth5<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth5Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth5 as DeepView>::deep_view);
            reveal(DynamicDepth5Spec::into_structural);
            let DynamicDepth5 { value } = v;
            let l1 = (Named("dynamic_depth4", DynamicDepth4Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth6Fmt {
        type PT = DynamicDepth6<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth6Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth6 as DeepView>::deep_view);
            reveal(DynamicDepth6Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth5", DynamicDepth5Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth6 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth6<'i>> for DynamicDepth6Fmt {
        fn serialize_into(&self, v: &DynamicDepth6<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth6Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth6Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth6 as DeepView>::deep_view);
            reveal(DynamicDepth6Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth6 { value } = v;

            DynamicDepth5Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth6<'i>> for DynamicDepth6Fmt {
        fn prepare(&self, v: &DynamicDepth6<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth6Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth6 as DeepView>::deep_view);
            reveal(DynamicDepth6Spec::into_structural);
            let DynamicDepth6 { value } = v;
            let l1 = (Named("dynamic_depth5", DynamicDepth5Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth7Fmt {
        type PT = DynamicDepth7<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth7Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth7 as DeepView>::deep_view);
            reveal(DynamicDepth7Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth6", DynamicDepth6Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth7 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth7<'i>> for DynamicDepth7Fmt {
        fn serialize_into(&self, v: &DynamicDepth7<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth7Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth7Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth7 as DeepView>::deep_view);
            reveal(DynamicDepth7Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth7 { value } = v;

            DynamicDepth6Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth7<'i>> for DynamicDepth7Fmt {
        fn prepare(&self, v: &DynamicDepth7<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth7Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth7 as DeepView>::deep_view);
            reveal(DynamicDepth7Spec::into_structural);
            let DynamicDepth7 { value } = v;
            let l1 = (Named("dynamic_depth6", DynamicDepth6Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth8Fmt {
        type PT = DynamicDepth8<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth8Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth8 as DeepView>::deep_view);
            reveal(DynamicDepth8Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth7", DynamicDepth7Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth8 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth8<'i>> for DynamicDepth8Fmt {
        fn serialize_into(&self, v: &DynamicDepth8<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth8Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth8Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth8 as DeepView>::deep_view);
            reveal(DynamicDepth8Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth8 { value } = v;

            DynamicDepth7Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth8<'i>> for DynamicDepth8Fmt {
        fn prepare(&self, v: &DynamicDepth8<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth8Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth8 as DeepView>::deep_view);
            reveal(DynamicDepth8Spec::into_structural);
            let DynamicDepth8 { value } = v;
            let l1 = (Named("dynamic_depth7", DynamicDepth7Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth9Fmt {
        type PT = DynamicDepth9<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth9Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth9 as DeepView>::deep_view);
            reveal(DynamicDepth9Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth8", DynamicDepth8Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth9 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth9<'i>> for DynamicDepth9Fmt {
        fn serialize_into(&self, v: &DynamicDepth9<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth9Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth9Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth9 as DeepView>::deep_view);
            reveal(DynamicDepth9Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth9 { value } = v;

            DynamicDepth8Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth9<'i>> for DynamicDepth9Fmt {
        fn prepare(&self, v: &DynamicDepth9<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth9Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth9 as DeepView>::deep_view);
            reveal(DynamicDepth9Spec::into_structural);
            let DynamicDepth9 { value } = v;
            let l1 = (Named("dynamic_depth8", DynamicDepth8Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth10Fmt {
        type PT = DynamicDepth10<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth10Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth10 as DeepView>::deep_view);
            reveal(DynamicDepth10Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth9", DynamicDepth9Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth10 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth10<'i>> for DynamicDepth10Fmt {
        fn serialize_into(&self, v: &DynamicDepth10<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth10Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth10Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth10 as DeepView>::deep_view);
            reveal(DynamicDepth10Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth10 { value } = v;

            DynamicDepth9Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth10<'i>> for DynamicDepth10Fmt {
        fn prepare(&self, v: &DynamicDepth10<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth10Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth10 as DeepView>::deep_view);
            reveal(DynamicDepth10Spec::into_structural);
            let DynamicDepth10 { value } = v;
            let l1 = (Named("dynamic_depth9", DynamicDepth9Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth11Fmt {
        type PT = DynamicDepth11<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth11Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth11 as DeepView>::deep_view);
            reveal(DynamicDepth11Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth10", DynamicDepth10Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth11 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth11<'i>> for DynamicDepth11Fmt {
        fn serialize_into(&self, v: &DynamicDepth11<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth11Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth11Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth11 as DeepView>::deep_view);
            reveal(DynamicDepth11Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth11 { value } = v;

            DynamicDepth10Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth11<'i>> for DynamicDepth11Fmt {
        fn prepare(&self, v: &DynamicDepth11<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth11Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth11 as DeepView>::deep_view);
            reveal(DynamicDepth11Spec::into_structural);
            let DynamicDepth11 { value } = v;
            let l1 = (Named("dynamic_depth10", DynamicDepth10Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth12Fmt {
        type PT = DynamicDepth12<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth12Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth12 as DeepView>::deep_view);
            reveal(DynamicDepth12Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth11", DynamicDepth11Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth12 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth12<'i>> for DynamicDepth12Fmt {
        fn serialize_into(&self, v: &DynamicDepth12<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth12Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth12Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth12 as DeepView>::deep_view);
            reveal(DynamicDepth12Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth12 { value } = v;

            DynamicDepth11Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth12<'i>> for DynamicDepth12Fmt {
        fn prepare(&self, v: &DynamicDepth12<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth12Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth12 as DeepView>::deep_view);
            reveal(DynamicDepth12Spec::into_structural);
            let DynamicDepth12 { value } = v;
            let l1 = (Named("dynamic_depth11", DynamicDepth11Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth13Fmt {
        type PT = DynamicDepth13<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth13Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth13 as DeepView>::deep_view);
            reveal(DynamicDepth13Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth12", DynamicDepth12Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth13 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth13<'i>> for DynamicDepth13Fmt {
        fn serialize_into(&self, v: &DynamicDepth13<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth13Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth13Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth13 as DeepView>::deep_view);
            reveal(DynamicDepth13Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth13 { value } = v;

            DynamicDepth12Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth13<'i>> for DynamicDepth13Fmt {
        fn prepare(&self, v: &DynamicDepth13<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth13Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth13 as DeepView>::deep_view);
            reveal(DynamicDepth13Spec::into_structural);
            let DynamicDepth13 { value } = v;
            let l1 = (Named("dynamic_depth12", DynamicDepth12Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth14Fmt {
        type PT = DynamicDepth14<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth14Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth14 as DeepView>::deep_view);
            reveal(DynamicDepth14Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth13", DynamicDepth13Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth14 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth14<'i>> for DynamicDepth14Fmt {
        fn serialize_into(&self, v: &DynamicDepth14<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth14Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth14Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth14 as DeepView>::deep_view);
            reveal(DynamicDepth14Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth14 { value } = v;

            DynamicDepth13Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth14<'i>> for DynamicDepth14Fmt {
        fn prepare(&self, v: &DynamicDepth14<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth14Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth14 as DeepView>::deep_view);
            reveal(DynamicDepth14Spec::into_structural);
            let DynamicDepth14 { value } = v;
            let l1 = (Named("dynamic_depth13", DynamicDepth13Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth15Fmt {
        type PT = DynamicDepth15<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth15Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth15 as DeepView>::deep_view);
            reveal(DynamicDepth15Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth14", DynamicDepth14Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth15 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth15<'i>> for DynamicDepth15Fmt {
        fn serialize_into(&self, v: &DynamicDepth15<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth15Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth15Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth15 as DeepView>::deep_view);
            reveal(DynamicDepth15Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth15 { value } = v;

            DynamicDepth14Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth15<'i>> for DynamicDepth15Fmt {
        fn prepare(&self, v: &DynamicDepth15<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth15Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth15 as DeepView>::deep_view);
            reveal(DynamicDepth15Spec::into_structural);
            let DynamicDepth15 { value } = v;
            let l1 = (Named("dynamic_depth14", DynamicDepth14Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }

    impl<'i> Parser<&'i [u8]> for DynamicDepth16Fmt {
        type PT = DynamicDepth16<'i>;

        fn min_byte_len(&self) -> usize {
            2
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<DynamicDepth16Fmt as SpecParser>::spec_parse);
            reveal(<DynamicDepth16 as DeepView>::deep_view);
            reveal(DynamicDepth16Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named("dynamic_depth15", DynamicDepth15Fmt)).parse(&rest)?;
            let rest = rest.skip(n1);
            let total_n = n1;

            let final_v = DynamicDepth16 { value };

            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, DynamicDepth16<'i>> for DynamicDepth16Fmt {
        fn serialize_into(&self, v: &DynamicDepth16<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<DynamicDepth16Fmt as SpecSerializer>::spec_serialize);
            reveal(<DynamicDepth16Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth16 as DeepView>::deep_view);
            reveal(DynamicDepth16Spec::into_structural);
            let ghost old_obuf = obuf@;

            let DynamicDepth16 { value } = v;

            DynamicDepth15Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<DynamicDepth16<'i>> for DynamicDepth16Fmt {
        fn prepare(&self, v: &DynamicDepth16<'i>) -> Result<usize, PreSerializeError> {
            reveal(<DynamicDepth16Fmt as SpecByteLen>::byte_len);
            reveal(<DynamicDepth16 as DeepView>::deep_view);
            reveal(DynamicDepth16Spec::into_structural);
            let DynamicDepth16 { value } = v;
            let l1 = (Named("dynamic_depth15", DynamicDepth15Fmt)).prepare(value)?;
            let total_len = l1;
            Ok(total_len)
        }
    }
}
}
