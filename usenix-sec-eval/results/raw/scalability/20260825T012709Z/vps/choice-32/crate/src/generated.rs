# ! [allow (warnings)] use vest_lib2::combinators::mapped::spec::* ;
use vest_lib2::combinators::* ;
use vest_lib2::combinators::recursive::* ;
use Sum::Inl as L ;
use Sum::Inr as R ;
use vest_lib2::Never ;
use vest_lib2::core::exec::input::{
    InputBuf,
    InputSlice
}
;
use vest_lib2::core::exec::output::OutputBuf ;
use vest_lib2::core::exec::parser::* ;
use vest_lib2::core::exec::serializer::* ;
use vest_lib2::core::exec::ParseError ;
use vest_lib2::core::exec::bytes_eq ;
use vest_lib2::core::{
    proof::*,
    spec::*
}
;
use vest_lib2::primitives::btcvarint::VarInt ;
use vest_lib2::primitives::leb128::ULeb128 ;
use vstd::prelude::* ;
verus! {
// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `choice_width32`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum ChoiceWidth32 {
    Variant0 (u8),
    Variant1 (u8),
    Variant2 (u8),
    Variant3 (u8),
    Variant4 (u8),
    Variant5 (u8),
    Variant6 (u8),
    Variant7 (u8),
    Variant8 (u8),
    Variant9 (u8),
    Variant10 (u8),
    Variant11 (u8),
    Variant12 (u8),
    Variant13 (u8),
    Variant14 (u8),
    Variant15 (u8),
    Variant16 (u8),
    Variant17 (u8),
    Variant18 (u8),
    Variant19 (u8),
    Variant20 (u8),
    Variant21 (u8),
    Variant22 (u8),
    Variant23 (u8),
    Variant24 (u8),
    Variant25 (u8),
    Variant26 (u8),
    Variant27 (u8),
    Variant28 (u8),
    Variant29 (u8),
    Variant30 (u8),
    Variant31 (u8),
}
# [verifier::ext_equal]
pub enum ChoiceWidth32Spec < T0 = u8, T1 = u8, T2 = u8, T3 = u8, T4 = u8, T5 = u8, T6 = u8, T7 = u8, T8 = u8, T9 = u8, T10 = u8, T11 = u8, T12 = u8, T13 = u8, T14 = u8, T15 = u8, T16 = u8, T17 = u8, T18 = u8, T19 = u8, T20 = u8, T21 = u8, T22 = u8, T23 = u8, T24 = u8, T25 = u8, T26 = u8, T27 = u8, T28 = u8, T29 = u8, T30 = u8, T31 = u8 > {
    Variant0 (T0),
    Variant1 (T1),
    Variant2 (T2),
    Variant3 (T3),
    Variant4 (T4),
    Variant5 (T5),
    Variant6 (T6),
    Variant7 (T7),
    Variant8 (T8),
    Variant9 (T9),
    Variant10 (T10),
    Variant11 (T11),
    Variant12 (T12),
    Variant13 (T13),
    Variant14 (T14),
    Variant15 (T15),
    Variant16 (T16),
    Variant17 (T17),
    Variant18 (T18),
    Variant19 (T19),
    Variant20 (T20),
    Variant21 (T21),
    Variant22 (T22),
    Variant23 (T23),
    Variant24 (T24),
    Variant25 (T25),
    Variant26 (T26),
    Variant27 (T27),
    Variant28 (T28),
    Variant29 (T29),
    Variant30 (T30),
    Variant31 (T31),
}
pub type ChoiceWidth32Inner = Sum < Sum < Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > >, Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > > >, Sum < Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > >, Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > > > > ;
impl DeepView for ChoiceWidth32 {
    type V = ChoiceWidth32Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        match self {
            ChoiceWidth32::Variant0 (v) => ChoiceWidth32Spec::Variant0 (v.deep_view()),
            ChoiceWidth32::Variant1 (v) => ChoiceWidth32Spec::Variant1 (v.deep_view()),
            ChoiceWidth32::Variant2 (v) => ChoiceWidth32Spec::Variant2 (v.deep_view()),
            ChoiceWidth32::Variant3 (v) => ChoiceWidth32Spec::Variant3 (v.deep_view()),
            ChoiceWidth32::Variant4 (v) => ChoiceWidth32Spec::Variant4 (v.deep_view()),
            ChoiceWidth32::Variant5 (v) => ChoiceWidth32Spec::Variant5 (v.deep_view()),
            ChoiceWidth32::Variant6 (v) => ChoiceWidth32Spec::Variant6 (v.deep_view()),
            ChoiceWidth32::Variant7 (v) => ChoiceWidth32Spec::Variant7 (v.deep_view()),
            ChoiceWidth32::Variant8 (v) => ChoiceWidth32Spec::Variant8 (v.deep_view()),
            ChoiceWidth32::Variant9 (v) => ChoiceWidth32Spec::Variant9 (v.deep_view()),
            ChoiceWidth32::Variant10 (v) => ChoiceWidth32Spec::Variant10 (v.deep_view()),
            ChoiceWidth32::Variant11 (v) => ChoiceWidth32Spec::Variant11 (v.deep_view()),
            ChoiceWidth32::Variant12 (v) => ChoiceWidth32Spec::Variant12 (v.deep_view()),
            ChoiceWidth32::Variant13 (v) => ChoiceWidth32Spec::Variant13 (v.deep_view()),
            ChoiceWidth32::Variant14 (v) => ChoiceWidth32Spec::Variant14 (v.deep_view()),
            ChoiceWidth32::Variant15 (v) => ChoiceWidth32Spec::Variant15 (v.deep_view()),
            ChoiceWidth32::Variant16 (v) => ChoiceWidth32Spec::Variant16 (v.deep_view()),
            ChoiceWidth32::Variant17 (v) => ChoiceWidth32Spec::Variant17 (v.deep_view()),
            ChoiceWidth32::Variant18 (v) => ChoiceWidth32Spec::Variant18 (v.deep_view()),
            ChoiceWidth32::Variant19 (v) => ChoiceWidth32Spec::Variant19 (v.deep_view()),
            ChoiceWidth32::Variant20 (v) => ChoiceWidth32Spec::Variant20 (v.deep_view()),
            ChoiceWidth32::Variant21 (v) => ChoiceWidth32Spec::Variant21 (v.deep_view()),
            ChoiceWidth32::Variant22 (v) => ChoiceWidth32Spec::Variant22 (v.deep_view()),
            ChoiceWidth32::Variant23 (v) => ChoiceWidth32Spec::Variant23 (v.deep_view()),
            ChoiceWidth32::Variant24 (v) => ChoiceWidth32Spec::Variant24 (v.deep_view()),
            ChoiceWidth32::Variant25 (v) => ChoiceWidth32Spec::Variant25 (v.deep_view()),
            ChoiceWidth32::Variant26 (v) => ChoiceWidth32Spec::Variant26 (v.deep_view()),
            ChoiceWidth32::Variant27 (v) => ChoiceWidth32Spec::Variant27 (v.deep_view()),
            ChoiceWidth32::Variant28 (v) => ChoiceWidth32Spec::Variant28 (v.deep_view()),
            ChoiceWidth32::Variant29 (v) => ChoiceWidth32Spec::Variant29 (v.deep_view()),
            ChoiceWidth32::Variant30 (v) => ChoiceWidth32Spec::Variant30 (v.deep_view()),
            ChoiceWidth32::Variant31 (v) => ChoiceWidth32Spec::Variant31 (v.deep_view()),
        }
    }
}
impl ChoiceWidth32 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view() == match self {
        ChoiceWidth32::Variant0 (v) => ChoiceWidth32Spec::Variant0 (v.deep_view()),
        ChoiceWidth32::Variant1 (v) => ChoiceWidth32Spec::Variant1 (v.deep_view()),
        ChoiceWidth32::Variant2 (v) => ChoiceWidth32Spec::Variant2 (v.deep_view()),
        ChoiceWidth32::Variant3 (v) => ChoiceWidth32Spec::Variant3 (v.deep_view()),
        ChoiceWidth32::Variant4 (v) => ChoiceWidth32Spec::Variant4 (v.deep_view()),
        ChoiceWidth32::Variant5 (v) => ChoiceWidth32Spec::Variant5 (v.deep_view()),
        ChoiceWidth32::Variant6 (v) => ChoiceWidth32Spec::Variant6 (v.deep_view()),
        ChoiceWidth32::Variant7 (v) => ChoiceWidth32Spec::Variant7 (v.deep_view()),
        ChoiceWidth32::Variant8 (v) => ChoiceWidth32Spec::Variant8 (v.deep_view()),
        ChoiceWidth32::Variant9 (v) => ChoiceWidth32Spec::Variant9 (v.deep_view()),
        ChoiceWidth32::Variant10 (v) => ChoiceWidth32Spec::Variant10 (v.deep_view()),
        ChoiceWidth32::Variant11 (v) => ChoiceWidth32Spec::Variant11 (v.deep_view()),
        ChoiceWidth32::Variant12 (v) => ChoiceWidth32Spec::Variant12 (v.deep_view()),
        ChoiceWidth32::Variant13 (v) => ChoiceWidth32Spec::Variant13 (v.deep_view()),
        ChoiceWidth32::Variant14 (v) => ChoiceWidth32Spec::Variant14 (v.deep_view()),
        ChoiceWidth32::Variant15 (v) => ChoiceWidth32Spec::Variant15 (v.deep_view()),
        ChoiceWidth32::Variant16 (v) => ChoiceWidth32Spec::Variant16 (v.deep_view()),
        ChoiceWidth32::Variant17 (v) => ChoiceWidth32Spec::Variant17 (v.deep_view()),
        ChoiceWidth32::Variant18 (v) => ChoiceWidth32Spec::Variant18 (v.deep_view()),
        ChoiceWidth32::Variant19 (v) => ChoiceWidth32Spec::Variant19 (v.deep_view()),
        ChoiceWidth32::Variant20 (v) => ChoiceWidth32Spec::Variant20 (v.deep_view()),
        ChoiceWidth32::Variant21 (v) => ChoiceWidth32Spec::Variant21 (v.deep_view()),
        ChoiceWidth32::Variant22 (v) => ChoiceWidth32Spec::Variant22 (v.deep_view()),
        ChoiceWidth32::Variant23 (v) => ChoiceWidth32Spec::Variant23 (v.deep_view()),
        ChoiceWidth32::Variant24 (v) => ChoiceWidth32Spec::Variant24 (v.deep_view()),
        ChoiceWidth32::Variant25 (v) => ChoiceWidth32Spec::Variant25 (v.deep_view()),
        ChoiceWidth32::Variant26 (v) => ChoiceWidth32Spec::Variant26 (v.deep_view()),
        ChoiceWidth32::Variant27 (v) => ChoiceWidth32Spec::Variant27 (v.deep_view()),
        ChoiceWidth32::Variant28 (v) => ChoiceWidth32Spec::Variant28 (v.deep_view()),
        ChoiceWidth32::Variant29 (v) => ChoiceWidth32Spec::Variant29 (v.deep_view()),
        ChoiceWidth32::Variant30 (v) => ChoiceWidth32Spec::Variant30 (v.deep_view()),
        ChoiceWidth32::Variant31 (v) => ChoiceWidth32Spec::Variant31 (v.deep_view()),
    }
   ,
    {
        reveal(< ChoiceWidth32 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30, T31 > ChoiceWidth32Spec < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30, T31 > {
    # [verifier::opaque] pub open spec fn from_structural (input: Sum < Sum < Sum < Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >,
    Sum < Sum < T4,
    T5 >,
    Sum < T6,
    T7 > > >,
    Sum < Sum < Sum < T8,
    T9 >,
    Sum < T10,
    T11 > >,
    Sum < Sum < T12,
    T13 >,
    Sum < T14,
    T15 > > > >,
    Sum < Sum < Sum < Sum < T16,
    T17 >,
    Sum < T18,
    T19 > >,
    Sum < Sum < T20,
    T21 >,
    Sum < T22,
    T23 > > >,
    Sum < Sum < Sum < T24,
    T25 >,
    Sum < T26,
    T27 > >,
    Sum < Sum < T28,
    T29 >,
    Sum < T30,
    T31 > > > > >) -> Self {
        match input {
            L (L (L (L (L (value))))) => Self::Variant0 (value),
            L (L (L (L (R (value))))) => Self::Variant1 (value),
            L (L (L (R (L (value))))) => Self::Variant2 (value),
            L (L (L (R (R (value))))) => Self::Variant3 (value),
            L (L (R (L (L (value))))) => Self::Variant4 (value),
            L (L (R (L (R (value))))) => Self::Variant5 (value),
            L (L (R (R (L (value))))) => Self::Variant6 (value),
            L (L (R (R (R (value))))) => Self::Variant7 (value),
            L (R (L (L (L (value))))) => Self::Variant8 (value),
            L (R (L (L (R (value))))) => Self::Variant9 (value),
            L (R (L (R (L (value))))) => Self::Variant10 (value),
            L (R (L (R (R (value))))) => Self::Variant11 (value),
            L (R (R (L (L (value))))) => Self::Variant12 (value),
            L (R (R (L (R (value))))) => Self::Variant13 (value),
            L (R (R (R (L (value))))) => Self::Variant14 (value),
            L (R (R (R (R (value))))) => Self::Variant15 (value),
            R (L (L (L (L (value))))) => Self::Variant16 (value),
            R (L (L (L (R (value))))) => Self::Variant17 (value),
            R (L (L (R (L (value))))) => Self::Variant18 (value),
            R (L (L (R (R (value))))) => Self::Variant19 (value),
            R (L (R (L (L (value))))) => Self::Variant20 (value),
            R (L (R (L (R (value))))) => Self::Variant21 (value),
            R (L (R (R (L (value))))) => Self::Variant22 (value),
            R (L (R (R (R (value))))) => Self::Variant23 (value),
            R (R (L (L (L (value))))) => Self::Variant24 (value),
            R (R (L (L (R (value))))) => Self::Variant25 (value),
            R (R (L (R (L (value))))) => Self::Variant26 (value),
            R (R (L (R (R (value))))) => Self::Variant27 (value),
            R (R (R (L (L (value))))) => Self::Variant28 (value),
            R (R (R (L (R (value))))) => Self::Variant29 (value),
            R (R (R (R (L (value))))) => Self::Variant30 (value),
            R (R (R (R (R (value))))) => Self::Variant31 (value),
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> Sum < Sum < Sum < Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >,
    Sum < Sum < T4,
    T5 >,
    Sum < T6,
    T7 > > >,
    Sum < Sum < Sum < T8,
    T9 >,
    Sum < T10,
    T11 > >,
    Sum < Sum < T12,
    T13 >,
    Sum < T14,
    T15 > > > >,
    Sum < Sum < Sum < Sum < T16,
    T17 >,
    Sum < T18,
    T19 > >,
    Sum < Sum < T20,
    T21 >,
    Sum < T22,
    T23 > > >,
    Sum < Sum < Sum < T24,
    T25 >,
    Sum < T26,
    T27 > >,
    Sum < Sum < T28,
    T29 >,
    Sum < T30,
    T31 > > > > > {
        match self {
            Self::Variant0 (value) => L (L (L (L (L (value))))),
            Self::Variant1 (value) => L (L (L (L (R (value))))),
            Self::Variant2 (value) => L (L (L (R (L (value))))),
            Self::Variant3 (value) => L (L (L (R (R (value))))),
            Self::Variant4 (value) => L (L (R (L (L (value))))),
            Self::Variant5 (value) => L (L (R (L (R (value))))),
            Self::Variant6 (value) => L (L (R (R (L (value))))),
            Self::Variant7 (value) => L (L (R (R (R (value))))),
            Self::Variant8 (value) => L (R (L (L (L (value))))),
            Self::Variant9 (value) => L (R (L (L (R (value))))),
            Self::Variant10 (value) => L (R (L (R (L (value))))),
            Self::Variant11 (value) => L (R (L (R (R (value))))),
            Self::Variant12 (value) => L (R (R (L (L (value))))),
            Self::Variant13 (value) => L (R (R (L (R (value))))),
            Self::Variant14 (value) => L (R (R (R (L (value))))),
            Self::Variant15 (value) => L (R (R (R (R (value))))),
            Self::Variant16 (value) => R (L (L (L (L (value))))),
            Self::Variant17 (value) => R (L (L (L (R (value))))),
            Self::Variant18 (value) => R (L (L (R (L (value))))),
            Self::Variant19 (value) => R (L (L (R (R (value))))),
            Self::Variant20 (value) => R (L (R (L (L (value))))),
            Self::Variant21 (value) => R (L (R (L (R (value))))),
            Self::Variant22 (value) => R (L (R (R (L (value))))),
            Self::Variant23 (value) => R (L (R (R (R (value))))),
            Self::Variant24 (value) => R (R (L (L (L (value))))),
            Self::Variant25 (value) => R (R (L (L (R (value))))),
            Self::Variant26 (value) => R (R (L (R (L (value))))),
            Self::Variant27 (value) => R (R (L (R (R (value))))),
            Self::Variant28 (value) => R (R (R (L (L (value))))),
            Self::Variant29 (value) => R (R (R (L (R (value))))),
            Self::Variant30 (value) => R (R (R (R (L (value))))),
            Self::Variant31 (value) => R (R (R (R (R (value))))),
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(ChoiceWidth32Spec::from_structural) ;
        reveal(ChoiceWidth32Spec::into_structural) ;
        match self {
            Self::Variant0 (_) => {
            }
           ,
            Self::Variant1 (_) => {
            }
           ,
            Self::Variant2 (_) => {
            }
           ,
            Self::Variant3 (_) => {
            }
           ,
            Self::Variant4 (_) => {
            }
           ,
            Self::Variant5 (_) => {
            }
           ,
            Self::Variant6 (_) => {
            }
           ,
            Self::Variant7 (_) => {
            }
           ,
            Self::Variant8 (_) => {
            }
           ,
            Self::Variant9 (_) => {
            }
           ,
            Self::Variant10 (_) => {
            }
           ,
            Self::Variant11 (_) => {
            }
           ,
            Self::Variant12 (_) => {
            }
           ,
            Self::Variant13 (_) => {
            }
           ,
            Self::Variant14 (_) => {
            }
           ,
            Self::Variant15 (_) => {
            }
           ,
            Self::Variant16 (_) => {
            }
           ,
            Self::Variant17 (_) => {
            }
           ,
            Self::Variant18 (_) => {
            }
           ,
            Self::Variant19 (_) => {
            }
           ,
            Self::Variant20 (_) => {
            }
           ,
            Self::Variant21 (_) => {
            }
           ,
            Self::Variant22 (_) => {
            }
           ,
            Self::Variant23 (_) => {
            }
           ,
            Self::Variant24 (_) => {
            }
           ,
            Self::Variant25 (_) => {
            }
           ,
            Self::Variant26 (_) => {
            }
           ,
            Self::Variant27 (_) => {
            }
           ,
            Self::Variant28 (_) => {
            }
           ,
            Self::Variant29 (_) => {
            }
           ,
            Self::Variant30 (_) => {
            }
           ,
            Self::Variant31 (_) => {
            }
           ,
        }
    }
    pub broadcast proof fn lemma_into_from (input: Sum < Sum < Sum < Sum < Sum < T0,
    T1 >,
    Sum < T2,
    T3 > >,
    Sum < Sum < T4,
    T5 >,
    Sum < T6,
    T7 > > >,
    Sum < Sum < Sum < T8,
    T9 >,
    Sum < T10,
    T11 > >,
    Sum < Sum < T12,
    T13 >,
    Sum < T14,
    T15 > > > >,
    Sum < Sum < Sum < Sum < T16,
    T17 >,
    Sum < T18,
    T19 > >,
    Sum < Sum < T20,
    T21 >,
    Sum < T22,
    T23 > > >,
    Sum < Sum < Sum < T24,
    T25 >,
    Sum < T26,
    T27 > >,
    Sum < Sum < T28,
    T29 >,
    Sum < T30,
    T31 > > > > >) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(ChoiceWidth32Spec::from_structural) ;
        reveal(ChoiceWidth32Spec::into_structural) ;
        match input {
            L (L (L (L (L (_))))) => {
            }
           ,
            L (L (L (L (R (_))))) => {
            }
           ,
            L (L (L (R (L (_))))) => {
            }
           ,
            L (L (L (R (R (_))))) => {
            }
           ,
            L (L (R (L (L (_))))) => {
            }
           ,
            L (L (R (L (R (_))))) => {
            }
           ,
            L (L (R (R (L (_))))) => {
            }
           ,
            L (L (R (R (R (_))))) => {
            }
           ,
            L (R (L (L (L (_))))) => {
            }
           ,
            L (R (L (L (R (_))))) => {
            }
           ,
            L (R (L (R (L (_))))) => {
            }
           ,
            L (R (L (R (R (_))))) => {
            }
           ,
            L (R (R (L (L (_))))) => {
            }
           ,
            L (R (R (L (R (_))))) => {
            }
           ,
            L (R (R (R (L (_))))) => {
            }
           ,
            L (R (R (R (R (_))))) => {
            }
           ,
            R (L (L (L (L (_))))) => {
            }
           ,
            R (L (L (L (R (_))))) => {
            }
           ,
            R (L (L (R (L (_))))) => {
            }
           ,
            R (L (L (R (R (_))))) => {
            }
           ,
            R (L (R (L (L (_))))) => {
            }
           ,
            R (L (R (L (R (_))))) => {
            }
           ,
            R (L (R (R (L (_))))) => {
            }
           ,
            R (L (R (R (R (_))))) => {
            }
           ,
            R (R (L (L (L (_))))) => {
            }
           ,
            R (R (L (L (R (_))))) => {
            }
           ,
            R (R (L (R (L (_))))) => {
            }
           ,
            R (R (L (R (R (_))))) => {
            }
           ,
            R (R (R (L (L (_))))) => {
            }
           ,
            R (R (R (L (R (_))))) => {
            }
           ,
            R (R (R (R (L (_))))) => {
            }
           ,
            R (R (R (R (R (_))))) => {
            }
           ,
        }
    }
    pub proof fn lemma_into_structural_variant (self) ensures Self::into_structural (self) == match self {
        Self::Variant0 (value) => L (L (L (L (L (value))))),
        Self::Variant1 (value) => L (L (L (L (R (value))))),
        Self::Variant2 (value) => L (L (L (R (L (value))))),
        Self::Variant3 (value) => L (L (L (R (R (value))))),
        Self::Variant4 (value) => L (L (R (L (L (value))))),
        Self::Variant5 (value) => L (L (R (L (R (value))))),
        Self::Variant6 (value) => L (L (R (R (L (value))))),
        Self::Variant7 (value) => L (L (R (R (R (value))))),
        Self::Variant8 (value) => L (R (L (L (L (value))))),
        Self::Variant9 (value) => L (R (L (L (R (value))))),
        Self::Variant10 (value) => L (R (L (R (L (value))))),
        Self::Variant11 (value) => L (R (L (R (R (value))))),
        Self::Variant12 (value) => L (R (R (L (L (value))))),
        Self::Variant13 (value) => L (R (R (L (R (value))))),
        Self::Variant14 (value) => L (R (R (R (L (value))))),
        Self::Variant15 (value) => L (R (R (R (R (value))))),
        Self::Variant16 (value) => R (L (L (L (L (value))))),
        Self::Variant17 (value) => R (L (L (L (R (value))))),
        Self::Variant18 (value) => R (L (L (R (L (value))))),
        Self::Variant19 (value) => R (L (L (R (R (value))))),
        Self::Variant20 (value) => R (L (R (L (L (value))))),
        Self::Variant21 (value) => R (L (R (L (R (value))))),
        Self::Variant22 (value) => R (L (R (R (L (value))))),
        Self::Variant23 (value) => R (L (R (R (R (value))))),
        Self::Variant24 (value) => R (R (L (L (L (value))))),
        Self::Variant25 (value) => R (R (L (L (R (value))))),
        Self::Variant26 (value) => R (R (L (R (L (value))))),
        Self::Variant27 (value) => R (R (L (R (R (value))))),
        Self::Variant28 (value) => R (R (R (L (L (value))))),
        Self::Variant29 (value) => R (R (R (L (R (value))))),
        Self::Variant30 (value) => R (R (R (R (L (value))))),
        Self::Variant31 (value) => R (R (R (R (R (value))))),
    }
   ,
    {
        reveal(ChoiceWidth32Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth32Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth32Reverse ;
impl SpecMap for ChoiceWidth32Forward {
    type Input = ChoiceWidth32Inner ;
    type Output = ChoiceWidth32Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        ChoiceWidth32Spec::from_structural (input)
    }
}
impl SpecMap for ChoiceWidth32Reverse {
    type Input = ChoiceWidth32Spec ;
    type Output = ChoiceWidth32Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `choice_width32`."]
# [derive (Clone, Copy)]
pub struct ChoiceWidth32Fmt ;

pub type ChoiceWidth32FmtSpec = Named < Mapped < Choice < Choice < Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > >, Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > > >, Choice < Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > >, Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > > > >, BiMap < ChoiceWidth32Forward, ChoiceWidth32Reverse >> > ;

impl ChoiceWidth32Fmt {
    # [doc = "specification constructor for `choice_width32`."] pub open spec fn spec_inner() -> ChoiceWidth32FmtSpec {
        Named ("choice_width32",
        Mapped {
            inner: Choice (Choice (Choice (Choice (Choice (Refined (U8,
            | x: u8 | x == 0),
            Refined (U8,
            | x: u8 | x == 1)),
            Choice (Refined (U8,
            | x: u8 | x == 2),
            Refined (U8,
            | x: u8 | x == 3))),
            Choice (Choice (Refined (U8,
            | x: u8 | x == 4),
            Refined (U8,
            | x: u8 | x == 5)),
            Choice (Refined (U8,
            | x: u8 | x == 6),
            Refined (U8,
            | x: u8 | x == 7)))),
            Choice (Choice (Choice (Refined (U8,
            | x: u8 | x == 8),
            Refined (U8,
            | x: u8 | x == 9)),
            Choice (Refined (U8,
            | x: u8 | x == 10),
            Refined (U8,
            | x: u8 | x == 11))),
            Choice (Choice (Refined (U8,
            | x: u8 | x == 12),
            Refined (U8,
            | x: u8 | x == 13)),
            Choice (Refined (U8,
            | x: u8 | x == 14),
            Refined (U8,
            | x: u8 | x == 15))))),
            Choice (Choice (Choice (Choice (Refined (U8,
            | x: u8 | x == 16),
            Refined (U8,
            | x: u8 | x == 17)),
            Choice (Refined (U8,
            | x: u8 | x == 18),
            Refined (U8,
            | x: u8 | x == 19))),
            Choice (Choice (Refined (U8,
            | x: u8 | x == 20),
            Refined (U8,
            | x: u8 | x == 21)),
            Choice (Refined (U8,
            | x: u8 | x == 22),
            Refined (U8,
            | x: u8 | x == 23)))),
            Choice (Choice (Choice (Refined (U8,
            | x: u8 | x == 24),
            Refined (U8,
            | x: u8 | x == 25)),
            Choice (Refined (U8,
            | x: u8 | x == 26),
            Refined (U8,
            | x: u8 | x == 27))),
            Choice (Choice (Refined (U8,
            | x: u8 | x == 28),
            Refined (U8,
            | x: u8 | x == 29)),
            Choice (Refined (U8,
            | x: u8 | x == 30),
            Refined (U8,
            | x: u8 | x >= 31)))))),
            mapper: BiMap (ChoiceWidth32Forward,
            ChoiceWidth32Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for ChoiceWidth32Fmt {
        type PVal = ChoiceWidth32Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for ChoiceWidth32Fmt {
        type Val = ChoiceWidth32Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for ChoiceWidth32Fmt {
        type SValue = ChoiceWidth32Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for ChoiceWidth32Fmt {
        type SVal = ChoiceWidth32Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for ChoiceWidth32Fmt {
        type T = ChoiceWidth32Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }
}

// ============================================================
// Proven Format Properties
// ============================================================
mod derived_proofs {
    use super::*;
    broadcast use {
        vest_lib2::combinators::disjoint::disjointness_lemmas,
        ChoiceWidth32Spec::lemma_from_into,
        ChoiceWidth32Spec::lemma_into_from,
    };

    impl SafeParser for ChoiceWidth32Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth32Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for ChoiceWidth32Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< ChoiceWidth32Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for ChoiceWidth32Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth32Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth32Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth32Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth32Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth32Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth32Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth32Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth32Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for ChoiceWidth32Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth32Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth32Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth32Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for ChoiceWidth32Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth32Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< ChoiceWidth32Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for ChoiceWidth32Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth32Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth32Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth32Fmt as Consistency>::consistent) ;
            reveal(< ChoiceWidth32Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: ChoiceWidth32Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                ChoiceWidth32Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for ChoiceWidth32Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< ChoiceWidth32Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth32Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth32Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for ChoiceWidth32Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth32Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth32Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for ChoiceWidth32Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth32Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth32Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }
}

// ============================================================
// Executable Implementations
// ============================================================
mod exec_impls {
    use super::*;

    impl<'i> Parser<&'i [u8]> for ChoiceWidth32Fmt {
        type PT = ChoiceWidth32;

        #[verifier::spinoff_prover]
        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ChoiceWidth32Fmt as SpecParser>::spec_parse);
            reveal(<ChoiceWidth32 as DeepView>::deep_view);
            reveal(ChoiceWidth32Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = match (U8).parse (& rest) {
        Ok ((n,
        va)) if va == 0 => {
            Ok ((n,
            ChoiceWidth32::Variant0 (va)))
        }
       ,
        _ => match (U8).parse (& rest) {
            Ok ((n,
            va)) if va == 1 => {
                Ok ((n,
                ChoiceWidth32::Variant1 (va)))
            }
           ,
            _ => match (U8).parse (& rest) {
                Ok ((n,
                va)) if va == 2 => {
                    Ok ((n,
                    ChoiceWidth32::Variant2 (va)))
                }
               ,
                _ => match (U8).parse (& rest) {
                    Ok ((n,
                    va)) if va == 3 => {
                        Ok ((n,
                        ChoiceWidth32::Variant3 (va)))
                    }
                   ,
                    _ => match (U8).parse (& rest) {
                        Ok ((n,
                        va)) if va == 4 => {
                            Ok ((n,
                            ChoiceWidth32::Variant4 (va)))
                        }
                       ,
                        _ => match (U8).parse (& rest) {
                            Ok ((n,
                            va)) if va == 5 => {
                                Ok ((n,
                                ChoiceWidth32::Variant5 (va)))
                            }
                           ,
                            _ => match (U8).parse (& rest) {
                                Ok ((n,
                                va)) if va == 6 => {
                                    Ok ((n,
                                    ChoiceWidth32::Variant6 (va)))
                                }
                               ,
                                _ => match (U8).parse (& rest) {
                                    Ok ((n,
                                    va)) if va == 7 => {
                                        Ok ((n,
                                        ChoiceWidth32::Variant7 (va)))
                                    }
                                   ,
                                    _ => match (U8).parse (& rest) {
                                        Ok ((n,
                                        va)) if va == 8 => {
                                            Ok ((n,
                                            ChoiceWidth32::Variant8 (va)))
                                        }
                                       ,
                                        _ => match (U8).parse (& rest) {
                                            Ok ((n,
                                            va)) if va == 9 => {
                                                Ok ((n,
                                                ChoiceWidth32::Variant9 (va)))
                                            }
                                           ,
                                            _ => match (U8).parse (& rest) {
                                                Ok ((n,
                                                va)) if va == 10 => {
                                                    Ok ((n,
                                                    ChoiceWidth32::Variant10 (va)))
                                                }
                                               ,
                                                _ => match (U8).parse (& rest) {
                                                    Ok ((n,
                                                    va)) if va == 11 => {
                                                        Ok ((n,
                                                        ChoiceWidth32::Variant11 (va)))
                                                    }
                                                   ,
                                                    _ => match (U8).parse (& rest) {
                                                        Ok ((n,
                                                        va)) if va == 12 => {
                                                            Ok ((n,
                                                            ChoiceWidth32::Variant12 (va)))
                                                        }
                                                       ,
                                                        _ => match (U8).parse (& rest) {
                                                            Ok ((n,
                                                            va)) if va == 13 => {
                                                                Ok ((n,
                                                                ChoiceWidth32::Variant13 (va)))
                                                            }
                                                           ,
                                                            _ => match (U8).parse (& rest) {
                                                                Ok ((n,
                                                                va)) if va == 14 => {
                                                                    Ok ((n,
                                                                    ChoiceWidth32::Variant14 (va)))
                                                                }
                                                               ,
                                                                _ => match (U8).parse (& rest) {
                                                                    Ok ((n,
                                                                    va)) if va == 15 => {
                                                                        Ok ((n,
                                                                        ChoiceWidth32::Variant15 (va)))
                                                                    }
                                                                   ,
                                                                    _ => match (U8).parse (& rest) {
                                                                        Ok ((n,
                                                                        va)) if va == 16 => {
                                                                            Ok ((n,
                                                                            ChoiceWidth32::Variant16 (va)))
                                                                        }
                                                                       ,
                                                                        _ => match (U8).parse (& rest) {
                                                                            Ok ((n,
                                                                            va)) if va == 17 => {
                                                                                Ok ((n,
                                                                                ChoiceWidth32::Variant17 (va)))
                                                                            }
                                                                           ,
                                                                            _ => match (U8).parse (& rest) {
                                                                                Ok ((n,
                                                                                va)) if va == 18 => {
                                                                                    Ok ((n,
                                                                                    ChoiceWidth32::Variant18 (va)))
                                                                                }
                                                                               ,
                                                                                _ => match (U8).parse (& rest) {
                                                                                    Ok ((n,
                                                                                    va)) if va == 19 => {
                                                                                        Ok ((n,
                                                                                        ChoiceWidth32::Variant19 (va)))
                                                                                    }
                                                                                   ,
                                                                                    _ => match (U8).parse (& rest) {
                                                                                        Ok ((n,
                                                                                        va)) if va == 20 => {
                                                                                            Ok ((n,
                                                                                            ChoiceWidth32::Variant20 (va)))
                                                                                        }
                                                                                       ,
                                                                                        _ => match (U8).parse (& rest) {
                                                                                            Ok ((n,
                                                                                            va)) if va == 21 => {
                                                                                                Ok ((n,
                                                                                                ChoiceWidth32::Variant21 (va)))
                                                                                            }
                                                                                           ,
                                                                                            _ => match (U8).parse (& rest) {
                                                                                                Ok ((n,
                                                                                                va)) if va == 22 => {
                                                                                                    Ok ((n,
                                                                                                    ChoiceWidth32::Variant22 (va)))
                                                                                                }
                                                                                               ,
                                                                                                _ => match (U8).parse (& rest) {
                                                                                                    Ok ((n,
                                                                                                    va)) if va == 23 => {
                                                                                                        Ok ((n,
                                                                                                        ChoiceWidth32::Variant23 (va)))
                                                                                                    }
                                                                                                   ,
                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                        Ok ((n,
                                                                                                        va)) if va == 24 => {
                                                                                                            Ok ((n,
                                                                                                            ChoiceWidth32::Variant24 (va)))
                                                                                                        }
                                                                                                       ,
                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                            Ok ((n,
                                                                                                            va)) if va == 25 => {
                                                                                                                Ok ((n,
                                                                                                                ChoiceWidth32::Variant25 (va)))
                                                                                                            }
                                                                                                           ,
                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                Ok ((n,
                                                                                                                va)) if va == 26 => {
                                                                                                                    Ok ((n,
                                                                                                                    ChoiceWidth32::Variant26 (va)))
                                                                                                                }
                                                                                                               ,
                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                    Ok ((n,
                                                                                                                    va)) if va == 27 => {
                                                                                                                        Ok ((n,
                                                                                                                        ChoiceWidth32::Variant27 (va)))
                                                                                                                    }
                                                                                                                   ,
                                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                                        Ok ((n,
                                                                                                                        va)) if va == 28 => {
                                                                                                                            Ok ((n,
                                                                                                                            ChoiceWidth32::Variant28 (va)))
                                                                                                                        }
                                                                                                                       ,
                                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                                            Ok ((n,
                                                                                                                            va)) if va == 29 => {
                                                                                                                                Ok ((n,
                                                                                                                                ChoiceWidth32::Variant29 (va)))
                                                                                                                            }
                                                                                                                           ,
                                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                                Ok ((n,
                                                                                                                                va)) if va == 30 => {
                                                                                                                                    Ok ((n,
                                                                                                                                    ChoiceWidth32::Variant30 (va)))
                                                                                                                                }
                                                                                                                               ,
                                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                                    Ok ((n,
                                                                                                                                    va)) if va >= 31 => {
                                                                                                                                        Ok ((n,
                                                                                                                                        ChoiceWidth32::Variant31 (va)))
                                                                                                                                    }
                                                                                                                                   ,
                                                                                                                                    _ => Err (ParseError::invalid_choice()),
                                                                                                                                }
                                                                                                                               ,
                                                                                                                            }
                                                                                                                           ,
                                                                                                                        }
                                                                                                                       ,
                                                                                                                    }
                                                                                                                   ,
                                                                                                                }
                                                                                                               ,
                                                                                                            }
                                                                                                           ,
                                                                                                        }
                                                                                                       ,
                                                                                                    }
                                                                                                   ,
                                                                                                }
                                                                                               ,
                                                                                            }
                                                                                           ,
                                                                                        }
                                                                                       ,
                                                                                    }
                                                                                   ,
                                                                                }
                                                                               ,
                                                                            }
                                                                           ,
                                                                        }
                                                                       ,
                                                                    }
                                                                   ,
                                                                }
                                                               ,
                                                            }
                                                           ,
                                                        }
                                                       ,
                                                    }
                                                   ,
                                                }
                                               ,
                                            }
                                           ,
                                        }
                                       ,
                                    }
                                   ,
                                }
                               ,
                            }
                           ,
                        }
                       ,
                    }
                   ,
                }
               ,
            }
           ,
        }
       ,
    }
    ?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ChoiceWidth32> for ChoiceWidth32Fmt {
        #[verifier::spinoff_prover]
        fn serialize_into(&self, v: &ChoiceWidth32, obuf: &mut Output) {
            reveal(<ChoiceWidth32Fmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceWidth32Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth32 as DeepView>::deep_view);
            reveal(ChoiceWidth32Spec::into_structural);
            let ghost old_obuf = obuf@;

            match v {
                ChoiceWidth32::Variant0 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant1 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant2 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant3 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant4 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant5 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant6 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant7 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant8 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant9 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant10 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant11 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant12 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant13 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant14 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant15 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant16 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant17 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant18 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant19 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant20 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant21 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant22 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant23 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant24 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant25 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant26 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant27 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant28 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant29 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant30 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth32::Variant31 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceWidth32> for ChoiceWidth32Fmt {
        #[verifier::spinoff_prover]
        fn prepare(&self, v: &ChoiceWidth32) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceWidth32Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth32 as DeepView>::deep_view);
            reveal(ChoiceWidth32Spec::into_structural);
            match v {
                ChoiceWidth32::Variant0 (v) => {
                    if ! (*v == 0) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant1 (v) => {
                    if ! (*v == 1) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant2 (v) => {
                    if ! (*v == 2) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant3 (v) => {
                    if ! (*v == 3) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant4 (v) => {
                    if ! (*v == 4) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant5 (v) => {
                    if ! (*v == 5) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant6 (v) => {
                    if ! (*v == 6) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant7 (v) => {
                    if ! (*v == 7) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant8 (v) => {
                    if ! (*v == 8) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant9 (v) => {
                    if ! (*v == 9) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant10 (v) => {
                    if ! (*v == 10) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant11 (v) => {
                    if ! (*v == 11) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant12 (v) => {
                    if ! (*v == 12) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant13 (v) => {
                    if ! (*v == 13) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant14 (v) => {
                    if ! (*v == 14) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant15 (v) => {
                    if ! (*v == 15) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant16 (v) => {
                    if ! (*v == 16) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant17 (v) => {
                    if ! (*v == 17) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant18 (v) => {
                    if ! (*v == 18) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant19 (v) => {
                    if ! (*v == 19) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant20 (v) => {
                    if ! (*v == 20) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant21 (v) => {
                    if ! (*v == 21) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant22 (v) => {
                    if ! (*v == 22) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant23 (v) => {
                    if ! (*v == 23) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant24 (v) => {
                    if ! (*v == 24) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant25 (v) => {
                    if ! (*v == 25) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant26 (v) => {
                    if ! (*v == 26) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant27 (v) => {
                    if ! (*v == 27) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant28 (v) => {
                    if ! (*v == 28) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant29 (v) => {
                    if ! (*v == 29) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant30 (v) => {
                    if ! (*v == 30) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth32::Variant31 (v) => {
                    if ! (*v >= 31) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
            }
        }
    }

}
}
