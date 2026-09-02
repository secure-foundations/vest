# ! [allow (warnings)] use vest_lib::combinators::mapped::spec::* ;
use vest_lib::combinators::* ;
use vest_lib::combinators::recursive::* ;
use Sum::Inl as L ;
use Sum::Inr as R ;
use vest_lib::Never ;
use vest_lib::core::exec::input::{
    InputBuf,
    InputSlice
}
;
use vest_lib::core::exec::output::OutputBuf ;
use vest_lib::core::exec::parser::* ;
use vest_lib::core::exec::serializer::* ;
use vest_lib::core::exec::ParseError ;
use vest_lib::core::exec::bytes_eq ;
use vest_lib::core::{
    proof::*,
    spec::*
}
;
use vest_lib::primitives::btcvarint::VarInt ;
use vest_lib::primitives::leb128::ULeb128 ;
use vstd::prelude::* ;
verus! {
// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `struct_width16`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct StructWidth16 {
    pub field0: u8,
    pub field1: u8,
    pub field2: u8,
    pub field3: u8,
    pub field4: u8,
    pub field5: u8,
    pub field6: u8,
    pub field7: u8,
    pub field8: u8,
    pub field9: u8,
    pub field10: u8,
    pub field11: u8,
    pub field12: u8,
    pub field13: u8,
    pub field14: u8,
    pub field15: u8,
}
# [verifier::ext_equal]
pub struct StructWidth16Spec < T0 = u8, T1 = u8, T2 = u8, T3 = u8, T4 = u8, T5 = u8, T6 = u8, T7 = u8, T8 = u8, T9 = u8, T10 = u8, T11 = u8, T12 = u8, T13 = u8, T14 = u8, T15 = u8 > {
    pub field0: T0,
    pub field1: T1,
    pub field2: T2,
    pub field3: T3,
    pub field4: T4,
    pub field5: T5,
    pub field6: T6,
    pub field7: T7,
    pub field8: T8,
    pub field9: T9,
    pub field10: T10,
    pub field11: T11,
    pub field12: T12,
    pub field13: T13,
    pub field14: T14,
    pub field15: T15,
}
pub type StructWidth16Inner = (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8))))))))))))))) ;
impl DeepView for StructWidth16 {
    type V = StructWidth16Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        StructWidth16Spec {
            field0: self.field0.deep_view(),
            field1: self.field1.deep_view(),
            field2: self.field2.deep_view(),
            field3: self.field3.deep_view(),
            field4: self.field4.deep_view(),
            field5: self.field5.deep_view(),
            field6: self.field6.deep_view(),
            field7: self.field7.deep_view(),
            field8: self.field8.deep_view(),
            field9: self.field9.deep_view(),
            field10: self.field10.deep_view(),
            field11: self.field11.deep_view(),
            field12: self.field12.deep_view(),
            field13: self.field13.deep_view(),
            field14: self.field14.deep_view(),
            field15: self.field15.deep_view(),
        }
    }
}
impl StructWidth16 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().field0 == self.field0.deep_view(),
    self.deep_view().field1 == self.field1.deep_view(),
    self.deep_view().field2 == self.field2.deep_view(),
    self.deep_view().field3 == self.field3.deep_view(),
    self.deep_view().field4 == self.field4.deep_view(),
    self.deep_view().field5 == self.field5.deep_view(),
    self.deep_view().field6 == self.field6.deep_view(),
    self.deep_view().field7 == self.field7.deep_view(),
    self.deep_view().field8 == self.field8.deep_view(),
    self.deep_view().field9 == self.field9.deep_view(),
    self.deep_view().field10 == self.field10.deep_view(),
    self.deep_view().field11 == self.field11.deep_view(),
    self.deep_view().field12 == self.field12.deep_view(),
    self.deep_view().field13 == self.field13.deep_view(),
    self.deep_view().field14 == self.field14.deep_view(),
    self.deep_view().field15 == self.field15.deep_view(),
    {
        reveal(< StructWidth16 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 > StructWidth16Spec < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    (T2,
    (T3,
    (T4,
    (T5,
    (T6,
    (T7,
    (T8,
    (T9,
    (T10,
    (T11,
    (T12,
    (T13,
    (T14,
    T15)))))))))))))))) -> Self {
        let (field0,
        (field1,
        (field2,
        (field3,
        (field4,
        (field5,
        (field6,
        (field7,
        (field8,
        (field9,
        (field10,
        (field11,
        (field12,
        (field13,
        (field14,
        field15))))))))))))))) = input ;
        Self {
            field0,
            field1,
            field2,
            field3,
            field4,
            field5,
            field6,
            field7,
            field8,
            field9,
            field10,
            field11,
            field12,
            field13,
            field14,
            field15
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    (T2,
    (T3,
    (T4,
    (T5,
    (T6,
    (T7,
    (T8,
    (T9,
    (T10,
    (T11,
    (T12,
    (T13,
    (T14,
    T15))))))))))))))) {
        let Self {
            field0,
            field1,
            field2,
            field3,
            field4,
            field5,
            field6,
            field7,
            field8,
            field9,
            field10,
            field11,
            field12,
            field13,
            field14,
            field15
        }
        = self ;
        (field0,
        (field1,
        (field2,
        (field3,
        (field4,
        (field5,
        (field6,
        (field7,
        (field8,
        (field9,
        (field10,
        (field11,
        (field12,
        (field13,
        (field14,
        field15)))))))))))))))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(StructWidth16Spec::from_structural) ;
        reveal(StructWidth16Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    (T2,
    (T3,
    (T4,
    (T5,
    (T6,
    (T7,
    (T8,
    (T9,
    (T10,
    (T11,
    (T12,
    (T13,
    (T14,
    T15)))))))))))))))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(StructWidth16Spec::from_structural) ;
        reveal(StructWidth16Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            field0,
            field1,
            field2,
            field3,
            field4,
            field5,
            field6,
            field7,
            field8,
            field9,
            field10,
            field11,
            field12,
            field13,
            field14,
            field15
        }
        => (field0,
        (field1,
        (field2,
        (field3,
        (field4,
        (field5,
        (field6,
        (field7,
        (field8,
        (field9,
        (field10,
        (field11,
        (field12,
        (field13,
        (field14,
        field15))))))))))))))),
    }
   ,
    {
        reveal(StructWidth16Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct StructWidth16Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct StructWidth16Reverse ;
impl SpecMap for StructWidth16Forward {
    type Input = StructWidth16Inner ;
    type Output = StructWidth16Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        StructWidth16Spec::from_structural (input)
    }
}
impl SpecMap for StructWidth16Reverse {
    type Input = StructWidth16Spec ;
    type Output = StructWidth16Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `choice_width64`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum ChoiceWidth64 {
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
    Variant32 (u8),
    Variant33 (u8),
    Variant34 (u8),
    Variant35 (u8),
    Variant36 (u8),
    Variant37 (u8),
    Variant38 (u8),
    Variant39 (u8),
    Variant40 (u8),
    Variant41 (u8),
    Variant42 (u8),
    Variant43 (u8),
    Variant44 (u8),
    Variant45 (u8),
    Variant46 (u8),
    Variant47 (u8),
    Variant48 (u8),
    Variant49 (u8),
    Variant50 (u8),
    Variant51 (u8),
    Variant52 (u8),
    Variant53 (u8),
    Variant54 (u8),
    Variant55 (u8),
    Variant56 (u8),
    Variant57 (u8),
    Variant58 (u8),
    Variant59 (u8),
    Variant60 (u8),
    Variant61 (u8),
    Variant62 (u8),
    Variant63 (u8),
}
# [verifier::ext_equal]
pub enum ChoiceWidth64Spec < T0 = u8, T1 = u8, T2 = u8, T3 = u8, T4 = u8, T5 = u8, T6 = u8, T7 = u8, T8 = u8, T9 = u8, T10 = u8, T11 = u8, T12 = u8, T13 = u8, T14 = u8, T15 = u8, T16 = u8, T17 = u8, T18 = u8, T19 = u8, T20 = u8, T21 = u8, T22 = u8, T23 = u8, T24 = u8, T25 = u8, T26 = u8, T27 = u8, T28 = u8, T29 = u8, T30 = u8, T31 = u8, T32 = u8, T33 = u8, T34 = u8, T35 = u8, T36 = u8, T37 = u8, T38 = u8, T39 = u8, T40 = u8, T41 = u8, T42 = u8, T43 = u8, T44 = u8, T45 = u8, T46 = u8, T47 = u8, T48 = u8, T49 = u8, T50 = u8, T51 = u8, T52 = u8, T53 = u8, T54 = u8, T55 = u8, T56 = u8, T57 = u8, T58 = u8, T59 = u8, T60 = u8, T61 = u8, T62 = u8, T63 = u8 > {
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
    Variant32 (T32),
    Variant33 (T33),
    Variant34 (T34),
    Variant35 (T35),
    Variant36 (T36),
    Variant37 (T37),
    Variant38 (T38),
    Variant39 (T39),
    Variant40 (T40),
    Variant41 (T41),
    Variant42 (T42),
    Variant43 (T43),
    Variant44 (T44),
    Variant45 (T45),
    Variant46 (T46),
    Variant47 (T47),
    Variant48 (T48),
    Variant49 (T49),
    Variant50 (T50),
    Variant51 (T51),
    Variant52 (T52),
    Variant53 (T53),
    Variant54 (T54),
    Variant55 (T55),
    Variant56 (T56),
    Variant57 (T57),
    Variant58 (T58),
    Variant59 (T59),
    Variant60 (T60),
    Variant61 (T61),
    Variant62 (T62),
    Variant63 (T63),
}
pub type ChoiceWidth64Inner = Sum < Sum < Sum < Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > >, Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > > >, Sum < Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > >, Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > > > >, Sum < Sum < Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > >, Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > > >, Sum < Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > >, Sum < Sum < Sum < u8, u8 >, Sum < u8, u8 > >, Sum < Sum < u8, u8 >, Sum < u8, u8 > > > > > > ;
impl DeepView for ChoiceWidth64 {
    type V = ChoiceWidth64Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        match self {
            ChoiceWidth64::Variant0 (v) => ChoiceWidth64Spec::Variant0 (v.deep_view()),
            ChoiceWidth64::Variant1 (v) => ChoiceWidth64Spec::Variant1 (v.deep_view()),
            ChoiceWidth64::Variant2 (v) => ChoiceWidth64Spec::Variant2 (v.deep_view()),
            ChoiceWidth64::Variant3 (v) => ChoiceWidth64Spec::Variant3 (v.deep_view()),
            ChoiceWidth64::Variant4 (v) => ChoiceWidth64Spec::Variant4 (v.deep_view()),
            ChoiceWidth64::Variant5 (v) => ChoiceWidth64Spec::Variant5 (v.deep_view()),
            ChoiceWidth64::Variant6 (v) => ChoiceWidth64Spec::Variant6 (v.deep_view()),
            ChoiceWidth64::Variant7 (v) => ChoiceWidth64Spec::Variant7 (v.deep_view()),
            ChoiceWidth64::Variant8 (v) => ChoiceWidth64Spec::Variant8 (v.deep_view()),
            ChoiceWidth64::Variant9 (v) => ChoiceWidth64Spec::Variant9 (v.deep_view()),
            ChoiceWidth64::Variant10 (v) => ChoiceWidth64Spec::Variant10 (v.deep_view()),
            ChoiceWidth64::Variant11 (v) => ChoiceWidth64Spec::Variant11 (v.deep_view()),
            ChoiceWidth64::Variant12 (v) => ChoiceWidth64Spec::Variant12 (v.deep_view()),
            ChoiceWidth64::Variant13 (v) => ChoiceWidth64Spec::Variant13 (v.deep_view()),
            ChoiceWidth64::Variant14 (v) => ChoiceWidth64Spec::Variant14 (v.deep_view()),
            ChoiceWidth64::Variant15 (v) => ChoiceWidth64Spec::Variant15 (v.deep_view()),
            ChoiceWidth64::Variant16 (v) => ChoiceWidth64Spec::Variant16 (v.deep_view()),
            ChoiceWidth64::Variant17 (v) => ChoiceWidth64Spec::Variant17 (v.deep_view()),
            ChoiceWidth64::Variant18 (v) => ChoiceWidth64Spec::Variant18 (v.deep_view()),
            ChoiceWidth64::Variant19 (v) => ChoiceWidth64Spec::Variant19 (v.deep_view()),
            ChoiceWidth64::Variant20 (v) => ChoiceWidth64Spec::Variant20 (v.deep_view()),
            ChoiceWidth64::Variant21 (v) => ChoiceWidth64Spec::Variant21 (v.deep_view()),
            ChoiceWidth64::Variant22 (v) => ChoiceWidth64Spec::Variant22 (v.deep_view()),
            ChoiceWidth64::Variant23 (v) => ChoiceWidth64Spec::Variant23 (v.deep_view()),
            ChoiceWidth64::Variant24 (v) => ChoiceWidth64Spec::Variant24 (v.deep_view()),
            ChoiceWidth64::Variant25 (v) => ChoiceWidth64Spec::Variant25 (v.deep_view()),
            ChoiceWidth64::Variant26 (v) => ChoiceWidth64Spec::Variant26 (v.deep_view()),
            ChoiceWidth64::Variant27 (v) => ChoiceWidth64Spec::Variant27 (v.deep_view()),
            ChoiceWidth64::Variant28 (v) => ChoiceWidth64Spec::Variant28 (v.deep_view()),
            ChoiceWidth64::Variant29 (v) => ChoiceWidth64Spec::Variant29 (v.deep_view()),
            ChoiceWidth64::Variant30 (v) => ChoiceWidth64Spec::Variant30 (v.deep_view()),
            ChoiceWidth64::Variant31 (v) => ChoiceWidth64Spec::Variant31 (v.deep_view()),
            ChoiceWidth64::Variant32 (v) => ChoiceWidth64Spec::Variant32 (v.deep_view()),
            ChoiceWidth64::Variant33 (v) => ChoiceWidth64Spec::Variant33 (v.deep_view()),
            ChoiceWidth64::Variant34 (v) => ChoiceWidth64Spec::Variant34 (v.deep_view()),
            ChoiceWidth64::Variant35 (v) => ChoiceWidth64Spec::Variant35 (v.deep_view()),
            ChoiceWidth64::Variant36 (v) => ChoiceWidth64Spec::Variant36 (v.deep_view()),
            ChoiceWidth64::Variant37 (v) => ChoiceWidth64Spec::Variant37 (v.deep_view()),
            ChoiceWidth64::Variant38 (v) => ChoiceWidth64Spec::Variant38 (v.deep_view()),
            ChoiceWidth64::Variant39 (v) => ChoiceWidth64Spec::Variant39 (v.deep_view()),
            ChoiceWidth64::Variant40 (v) => ChoiceWidth64Spec::Variant40 (v.deep_view()),
            ChoiceWidth64::Variant41 (v) => ChoiceWidth64Spec::Variant41 (v.deep_view()),
            ChoiceWidth64::Variant42 (v) => ChoiceWidth64Spec::Variant42 (v.deep_view()),
            ChoiceWidth64::Variant43 (v) => ChoiceWidth64Spec::Variant43 (v.deep_view()),
            ChoiceWidth64::Variant44 (v) => ChoiceWidth64Spec::Variant44 (v.deep_view()),
            ChoiceWidth64::Variant45 (v) => ChoiceWidth64Spec::Variant45 (v.deep_view()),
            ChoiceWidth64::Variant46 (v) => ChoiceWidth64Spec::Variant46 (v.deep_view()),
            ChoiceWidth64::Variant47 (v) => ChoiceWidth64Spec::Variant47 (v.deep_view()),
            ChoiceWidth64::Variant48 (v) => ChoiceWidth64Spec::Variant48 (v.deep_view()),
            ChoiceWidth64::Variant49 (v) => ChoiceWidth64Spec::Variant49 (v.deep_view()),
            ChoiceWidth64::Variant50 (v) => ChoiceWidth64Spec::Variant50 (v.deep_view()),
            ChoiceWidth64::Variant51 (v) => ChoiceWidth64Spec::Variant51 (v.deep_view()),
            ChoiceWidth64::Variant52 (v) => ChoiceWidth64Spec::Variant52 (v.deep_view()),
            ChoiceWidth64::Variant53 (v) => ChoiceWidth64Spec::Variant53 (v.deep_view()),
            ChoiceWidth64::Variant54 (v) => ChoiceWidth64Spec::Variant54 (v.deep_view()),
            ChoiceWidth64::Variant55 (v) => ChoiceWidth64Spec::Variant55 (v.deep_view()),
            ChoiceWidth64::Variant56 (v) => ChoiceWidth64Spec::Variant56 (v.deep_view()),
            ChoiceWidth64::Variant57 (v) => ChoiceWidth64Spec::Variant57 (v.deep_view()),
            ChoiceWidth64::Variant58 (v) => ChoiceWidth64Spec::Variant58 (v.deep_view()),
            ChoiceWidth64::Variant59 (v) => ChoiceWidth64Spec::Variant59 (v.deep_view()),
            ChoiceWidth64::Variant60 (v) => ChoiceWidth64Spec::Variant60 (v.deep_view()),
            ChoiceWidth64::Variant61 (v) => ChoiceWidth64Spec::Variant61 (v.deep_view()),
            ChoiceWidth64::Variant62 (v) => ChoiceWidth64Spec::Variant62 (v.deep_view()),
            ChoiceWidth64::Variant63 (v) => ChoiceWidth64Spec::Variant63 (v.deep_view()),
        }
    }
}
impl ChoiceWidth64 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view() == match self {
        ChoiceWidth64::Variant0 (v) => ChoiceWidth64Spec::Variant0 (v.deep_view()),
        ChoiceWidth64::Variant1 (v) => ChoiceWidth64Spec::Variant1 (v.deep_view()),
        ChoiceWidth64::Variant2 (v) => ChoiceWidth64Spec::Variant2 (v.deep_view()),
        ChoiceWidth64::Variant3 (v) => ChoiceWidth64Spec::Variant3 (v.deep_view()),
        ChoiceWidth64::Variant4 (v) => ChoiceWidth64Spec::Variant4 (v.deep_view()),
        ChoiceWidth64::Variant5 (v) => ChoiceWidth64Spec::Variant5 (v.deep_view()),
        ChoiceWidth64::Variant6 (v) => ChoiceWidth64Spec::Variant6 (v.deep_view()),
        ChoiceWidth64::Variant7 (v) => ChoiceWidth64Spec::Variant7 (v.deep_view()),
        ChoiceWidth64::Variant8 (v) => ChoiceWidth64Spec::Variant8 (v.deep_view()),
        ChoiceWidth64::Variant9 (v) => ChoiceWidth64Spec::Variant9 (v.deep_view()),
        ChoiceWidth64::Variant10 (v) => ChoiceWidth64Spec::Variant10 (v.deep_view()),
        ChoiceWidth64::Variant11 (v) => ChoiceWidth64Spec::Variant11 (v.deep_view()),
        ChoiceWidth64::Variant12 (v) => ChoiceWidth64Spec::Variant12 (v.deep_view()),
        ChoiceWidth64::Variant13 (v) => ChoiceWidth64Spec::Variant13 (v.deep_view()),
        ChoiceWidth64::Variant14 (v) => ChoiceWidth64Spec::Variant14 (v.deep_view()),
        ChoiceWidth64::Variant15 (v) => ChoiceWidth64Spec::Variant15 (v.deep_view()),
        ChoiceWidth64::Variant16 (v) => ChoiceWidth64Spec::Variant16 (v.deep_view()),
        ChoiceWidth64::Variant17 (v) => ChoiceWidth64Spec::Variant17 (v.deep_view()),
        ChoiceWidth64::Variant18 (v) => ChoiceWidth64Spec::Variant18 (v.deep_view()),
        ChoiceWidth64::Variant19 (v) => ChoiceWidth64Spec::Variant19 (v.deep_view()),
        ChoiceWidth64::Variant20 (v) => ChoiceWidth64Spec::Variant20 (v.deep_view()),
        ChoiceWidth64::Variant21 (v) => ChoiceWidth64Spec::Variant21 (v.deep_view()),
        ChoiceWidth64::Variant22 (v) => ChoiceWidth64Spec::Variant22 (v.deep_view()),
        ChoiceWidth64::Variant23 (v) => ChoiceWidth64Spec::Variant23 (v.deep_view()),
        ChoiceWidth64::Variant24 (v) => ChoiceWidth64Spec::Variant24 (v.deep_view()),
        ChoiceWidth64::Variant25 (v) => ChoiceWidth64Spec::Variant25 (v.deep_view()),
        ChoiceWidth64::Variant26 (v) => ChoiceWidth64Spec::Variant26 (v.deep_view()),
        ChoiceWidth64::Variant27 (v) => ChoiceWidth64Spec::Variant27 (v.deep_view()),
        ChoiceWidth64::Variant28 (v) => ChoiceWidth64Spec::Variant28 (v.deep_view()),
        ChoiceWidth64::Variant29 (v) => ChoiceWidth64Spec::Variant29 (v.deep_view()),
        ChoiceWidth64::Variant30 (v) => ChoiceWidth64Spec::Variant30 (v.deep_view()),
        ChoiceWidth64::Variant31 (v) => ChoiceWidth64Spec::Variant31 (v.deep_view()),
        ChoiceWidth64::Variant32 (v) => ChoiceWidth64Spec::Variant32 (v.deep_view()),
        ChoiceWidth64::Variant33 (v) => ChoiceWidth64Spec::Variant33 (v.deep_view()),
        ChoiceWidth64::Variant34 (v) => ChoiceWidth64Spec::Variant34 (v.deep_view()),
        ChoiceWidth64::Variant35 (v) => ChoiceWidth64Spec::Variant35 (v.deep_view()),
        ChoiceWidth64::Variant36 (v) => ChoiceWidth64Spec::Variant36 (v.deep_view()),
        ChoiceWidth64::Variant37 (v) => ChoiceWidth64Spec::Variant37 (v.deep_view()),
        ChoiceWidth64::Variant38 (v) => ChoiceWidth64Spec::Variant38 (v.deep_view()),
        ChoiceWidth64::Variant39 (v) => ChoiceWidth64Spec::Variant39 (v.deep_view()),
        ChoiceWidth64::Variant40 (v) => ChoiceWidth64Spec::Variant40 (v.deep_view()),
        ChoiceWidth64::Variant41 (v) => ChoiceWidth64Spec::Variant41 (v.deep_view()),
        ChoiceWidth64::Variant42 (v) => ChoiceWidth64Spec::Variant42 (v.deep_view()),
        ChoiceWidth64::Variant43 (v) => ChoiceWidth64Spec::Variant43 (v.deep_view()),
        ChoiceWidth64::Variant44 (v) => ChoiceWidth64Spec::Variant44 (v.deep_view()),
        ChoiceWidth64::Variant45 (v) => ChoiceWidth64Spec::Variant45 (v.deep_view()),
        ChoiceWidth64::Variant46 (v) => ChoiceWidth64Spec::Variant46 (v.deep_view()),
        ChoiceWidth64::Variant47 (v) => ChoiceWidth64Spec::Variant47 (v.deep_view()),
        ChoiceWidth64::Variant48 (v) => ChoiceWidth64Spec::Variant48 (v.deep_view()),
        ChoiceWidth64::Variant49 (v) => ChoiceWidth64Spec::Variant49 (v.deep_view()),
        ChoiceWidth64::Variant50 (v) => ChoiceWidth64Spec::Variant50 (v.deep_view()),
        ChoiceWidth64::Variant51 (v) => ChoiceWidth64Spec::Variant51 (v.deep_view()),
        ChoiceWidth64::Variant52 (v) => ChoiceWidth64Spec::Variant52 (v.deep_view()),
        ChoiceWidth64::Variant53 (v) => ChoiceWidth64Spec::Variant53 (v.deep_view()),
        ChoiceWidth64::Variant54 (v) => ChoiceWidth64Spec::Variant54 (v.deep_view()),
        ChoiceWidth64::Variant55 (v) => ChoiceWidth64Spec::Variant55 (v.deep_view()),
        ChoiceWidth64::Variant56 (v) => ChoiceWidth64Spec::Variant56 (v.deep_view()),
        ChoiceWidth64::Variant57 (v) => ChoiceWidth64Spec::Variant57 (v.deep_view()),
        ChoiceWidth64::Variant58 (v) => ChoiceWidth64Spec::Variant58 (v.deep_view()),
        ChoiceWidth64::Variant59 (v) => ChoiceWidth64Spec::Variant59 (v.deep_view()),
        ChoiceWidth64::Variant60 (v) => ChoiceWidth64Spec::Variant60 (v.deep_view()),
        ChoiceWidth64::Variant61 (v) => ChoiceWidth64Spec::Variant61 (v.deep_view()),
        ChoiceWidth64::Variant62 (v) => ChoiceWidth64Spec::Variant62 (v.deep_view()),
        ChoiceWidth64::Variant63 (v) => ChoiceWidth64Spec::Variant63 (v.deep_view()),
    }
   ,
    {
        reveal(< ChoiceWidth64 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30, T31, T32, T33, T34, T35, T36, T37, T38, T39, T40, T41, T42, T43, T44, T45, T46, T47, T48, T49, T50, T51, T52, T53, T54, T55, T56, T57, T58, T59, T60, T61, T62, T63 > ChoiceWidth64Spec < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30, T31, T32, T33, T34, T35, T36, T37, T38, T39, T40, T41, T42, T43, T44, T45, T46, T47, T48, T49, T50, T51, T52, T53, T54, T55, T56, T57, T58, T59, T60, T61, T62, T63 > {
    # [verifier::opaque] pub open spec fn from_structural (input: Sum < Sum < Sum < Sum < Sum < Sum < T0,
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
    T31 > > > > >,
    Sum < Sum < Sum < Sum < Sum < T32,
    T33 >,
    Sum < T34,
    T35 > >,
    Sum < Sum < T36,
    T37 >,
    Sum < T38,
    T39 > > >,
    Sum < Sum < Sum < T40,
    T41 >,
    Sum < T42,
    T43 > >,
    Sum < Sum < T44,
    T45 >,
    Sum < T46,
    T47 > > > >,
    Sum < Sum < Sum < Sum < T48,
    T49 >,
    Sum < T50,
    T51 > >,
    Sum < Sum < T52,
    T53 >,
    Sum < T54,
    T55 > > >,
    Sum < Sum < Sum < T56,
    T57 >,
    Sum < T58,
    T59 > >,
    Sum < Sum < T60,
    T61 >,
    Sum < T62,
    T63 > > > > > >) -> Self {
        match input {
            L (L (L (L (L (L (value)))))) => Self::Variant0 (value),
            L (L (L (L (L (R (value)))))) => Self::Variant1 (value),
            L (L (L (L (R (L (value)))))) => Self::Variant2 (value),
            L (L (L (L (R (R (value)))))) => Self::Variant3 (value),
            L (L (L (R (L (L (value)))))) => Self::Variant4 (value),
            L (L (L (R (L (R (value)))))) => Self::Variant5 (value),
            L (L (L (R (R (L (value)))))) => Self::Variant6 (value),
            L (L (L (R (R (R (value)))))) => Self::Variant7 (value),
            L (L (R (L (L (L (value)))))) => Self::Variant8 (value),
            L (L (R (L (L (R (value)))))) => Self::Variant9 (value),
            L (L (R (L (R (L (value)))))) => Self::Variant10 (value),
            L (L (R (L (R (R (value)))))) => Self::Variant11 (value),
            L (L (R (R (L (L (value)))))) => Self::Variant12 (value),
            L (L (R (R (L (R (value)))))) => Self::Variant13 (value),
            L (L (R (R (R (L (value)))))) => Self::Variant14 (value),
            L (L (R (R (R (R (value)))))) => Self::Variant15 (value),
            L (R (L (L (L (L (value)))))) => Self::Variant16 (value),
            L (R (L (L (L (R (value)))))) => Self::Variant17 (value),
            L (R (L (L (R (L (value)))))) => Self::Variant18 (value),
            L (R (L (L (R (R (value)))))) => Self::Variant19 (value),
            L (R (L (R (L (L (value)))))) => Self::Variant20 (value),
            L (R (L (R (L (R (value)))))) => Self::Variant21 (value),
            L (R (L (R (R (L (value)))))) => Self::Variant22 (value),
            L (R (L (R (R (R (value)))))) => Self::Variant23 (value),
            L (R (R (L (L (L (value)))))) => Self::Variant24 (value),
            L (R (R (L (L (R (value)))))) => Self::Variant25 (value),
            L (R (R (L (R (L (value)))))) => Self::Variant26 (value),
            L (R (R (L (R (R (value)))))) => Self::Variant27 (value),
            L (R (R (R (L (L (value)))))) => Self::Variant28 (value),
            L (R (R (R (L (R (value)))))) => Self::Variant29 (value),
            L (R (R (R (R (L (value)))))) => Self::Variant30 (value),
            L (R (R (R (R (R (value)))))) => Self::Variant31 (value),
            R (L (L (L (L (L (value)))))) => Self::Variant32 (value),
            R (L (L (L (L (R (value)))))) => Self::Variant33 (value),
            R (L (L (L (R (L (value)))))) => Self::Variant34 (value),
            R (L (L (L (R (R (value)))))) => Self::Variant35 (value),
            R (L (L (R (L (L (value)))))) => Self::Variant36 (value),
            R (L (L (R (L (R (value)))))) => Self::Variant37 (value),
            R (L (L (R (R (L (value)))))) => Self::Variant38 (value),
            R (L (L (R (R (R (value)))))) => Self::Variant39 (value),
            R (L (R (L (L (L (value)))))) => Self::Variant40 (value),
            R (L (R (L (L (R (value)))))) => Self::Variant41 (value),
            R (L (R (L (R (L (value)))))) => Self::Variant42 (value),
            R (L (R (L (R (R (value)))))) => Self::Variant43 (value),
            R (L (R (R (L (L (value)))))) => Self::Variant44 (value),
            R (L (R (R (L (R (value)))))) => Self::Variant45 (value),
            R (L (R (R (R (L (value)))))) => Self::Variant46 (value),
            R (L (R (R (R (R (value)))))) => Self::Variant47 (value),
            R (R (L (L (L (L (value)))))) => Self::Variant48 (value),
            R (R (L (L (L (R (value)))))) => Self::Variant49 (value),
            R (R (L (L (R (L (value)))))) => Self::Variant50 (value),
            R (R (L (L (R (R (value)))))) => Self::Variant51 (value),
            R (R (L (R (L (L (value)))))) => Self::Variant52 (value),
            R (R (L (R (L (R (value)))))) => Self::Variant53 (value),
            R (R (L (R (R (L (value)))))) => Self::Variant54 (value),
            R (R (L (R (R (R (value)))))) => Self::Variant55 (value),
            R (R (R (L (L (L (value)))))) => Self::Variant56 (value),
            R (R (R (L (L (R (value)))))) => Self::Variant57 (value),
            R (R (R (L (R (L (value)))))) => Self::Variant58 (value),
            R (R (R (L (R (R (value)))))) => Self::Variant59 (value),
            R (R (R (R (L (L (value)))))) => Self::Variant60 (value),
            R (R (R (R (L (R (value)))))) => Self::Variant61 (value),
            R (R (R (R (R (L (value)))))) => Self::Variant62 (value),
            R (R (R (R (R (R (value)))))) => Self::Variant63 (value),
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> Sum < Sum < Sum < Sum < Sum < Sum < T0,
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
    T31 > > > > >,
    Sum < Sum < Sum < Sum < Sum < T32,
    T33 >,
    Sum < T34,
    T35 > >,
    Sum < Sum < T36,
    T37 >,
    Sum < T38,
    T39 > > >,
    Sum < Sum < Sum < T40,
    T41 >,
    Sum < T42,
    T43 > >,
    Sum < Sum < T44,
    T45 >,
    Sum < T46,
    T47 > > > >,
    Sum < Sum < Sum < Sum < T48,
    T49 >,
    Sum < T50,
    T51 > >,
    Sum < Sum < T52,
    T53 >,
    Sum < T54,
    T55 > > >,
    Sum < Sum < Sum < T56,
    T57 >,
    Sum < T58,
    T59 > >,
    Sum < Sum < T60,
    T61 >,
    Sum < T62,
    T63 > > > > > > {
        match self {
            Self::Variant0 (value) => L (L (L (L (L (L (value)))))),
            Self::Variant1 (value) => L (L (L (L (L (R (value)))))),
            Self::Variant2 (value) => L (L (L (L (R (L (value)))))),
            Self::Variant3 (value) => L (L (L (L (R (R (value)))))),
            Self::Variant4 (value) => L (L (L (R (L (L (value)))))),
            Self::Variant5 (value) => L (L (L (R (L (R (value)))))),
            Self::Variant6 (value) => L (L (L (R (R (L (value)))))),
            Self::Variant7 (value) => L (L (L (R (R (R (value)))))),
            Self::Variant8 (value) => L (L (R (L (L (L (value)))))),
            Self::Variant9 (value) => L (L (R (L (L (R (value)))))),
            Self::Variant10 (value) => L (L (R (L (R (L (value)))))),
            Self::Variant11 (value) => L (L (R (L (R (R (value)))))),
            Self::Variant12 (value) => L (L (R (R (L (L (value)))))),
            Self::Variant13 (value) => L (L (R (R (L (R (value)))))),
            Self::Variant14 (value) => L (L (R (R (R (L (value)))))),
            Self::Variant15 (value) => L (L (R (R (R (R (value)))))),
            Self::Variant16 (value) => L (R (L (L (L (L (value)))))),
            Self::Variant17 (value) => L (R (L (L (L (R (value)))))),
            Self::Variant18 (value) => L (R (L (L (R (L (value)))))),
            Self::Variant19 (value) => L (R (L (L (R (R (value)))))),
            Self::Variant20 (value) => L (R (L (R (L (L (value)))))),
            Self::Variant21 (value) => L (R (L (R (L (R (value)))))),
            Self::Variant22 (value) => L (R (L (R (R (L (value)))))),
            Self::Variant23 (value) => L (R (L (R (R (R (value)))))),
            Self::Variant24 (value) => L (R (R (L (L (L (value)))))),
            Self::Variant25 (value) => L (R (R (L (L (R (value)))))),
            Self::Variant26 (value) => L (R (R (L (R (L (value)))))),
            Self::Variant27 (value) => L (R (R (L (R (R (value)))))),
            Self::Variant28 (value) => L (R (R (R (L (L (value)))))),
            Self::Variant29 (value) => L (R (R (R (L (R (value)))))),
            Self::Variant30 (value) => L (R (R (R (R (L (value)))))),
            Self::Variant31 (value) => L (R (R (R (R (R (value)))))),
            Self::Variant32 (value) => R (L (L (L (L (L (value)))))),
            Self::Variant33 (value) => R (L (L (L (L (R (value)))))),
            Self::Variant34 (value) => R (L (L (L (R (L (value)))))),
            Self::Variant35 (value) => R (L (L (L (R (R (value)))))),
            Self::Variant36 (value) => R (L (L (R (L (L (value)))))),
            Self::Variant37 (value) => R (L (L (R (L (R (value)))))),
            Self::Variant38 (value) => R (L (L (R (R (L (value)))))),
            Self::Variant39 (value) => R (L (L (R (R (R (value)))))),
            Self::Variant40 (value) => R (L (R (L (L (L (value)))))),
            Self::Variant41 (value) => R (L (R (L (L (R (value)))))),
            Self::Variant42 (value) => R (L (R (L (R (L (value)))))),
            Self::Variant43 (value) => R (L (R (L (R (R (value)))))),
            Self::Variant44 (value) => R (L (R (R (L (L (value)))))),
            Self::Variant45 (value) => R (L (R (R (L (R (value)))))),
            Self::Variant46 (value) => R (L (R (R (R (L (value)))))),
            Self::Variant47 (value) => R (L (R (R (R (R (value)))))),
            Self::Variant48 (value) => R (R (L (L (L (L (value)))))),
            Self::Variant49 (value) => R (R (L (L (L (R (value)))))),
            Self::Variant50 (value) => R (R (L (L (R (L (value)))))),
            Self::Variant51 (value) => R (R (L (L (R (R (value)))))),
            Self::Variant52 (value) => R (R (L (R (L (L (value)))))),
            Self::Variant53 (value) => R (R (L (R (L (R (value)))))),
            Self::Variant54 (value) => R (R (L (R (R (L (value)))))),
            Self::Variant55 (value) => R (R (L (R (R (R (value)))))),
            Self::Variant56 (value) => R (R (R (L (L (L (value)))))),
            Self::Variant57 (value) => R (R (R (L (L (R (value)))))),
            Self::Variant58 (value) => R (R (R (L (R (L (value)))))),
            Self::Variant59 (value) => R (R (R (L (R (R (value)))))),
            Self::Variant60 (value) => R (R (R (R (L (L (value)))))),
            Self::Variant61 (value) => R (R (R (R (L (R (value)))))),
            Self::Variant62 (value) => R (R (R (R (R (L (value)))))),
            Self::Variant63 (value) => R (R (R (R (R (R (value)))))),
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(ChoiceWidth64Spec::from_structural) ;
        reveal(ChoiceWidth64Spec::into_structural) ;
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
            Self::Variant32 (_) => {
            }
           ,
            Self::Variant33 (_) => {
            }
           ,
            Self::Variant34 (_) => {
            }
           ,
            Self::Variant35 (_) => {
            }
           ,
            Self::Variant36 (_) => {
            }
           ,
            Self::Variant37 (_) => {
            }
           ,
            Self::Variant38 (_) => {
            }
           ,
            Self::Variant39 (_) => {
            }
           ,
            Self::Variant40 (_) => {
            }
           ,
            Self::Variant41 (_) => {
            }
           ,
            Self::Variant42 (_) => {
            }
           ,
            Self::Variant43 (_) => {
            }
           ,
            Self::Variant44 (_) => {
            }
           ,
            Self::Variant45 (_) => {
            }
           ,
            Self::Variant46 (_) => {
            }
           ,
            Self::Variant47 (_) => {
            }
           ,
            Self::Variant48 (_) => {
            }
           ,
            Self::Variant49 (_) => {
            }
           ,
            Self::Variant50 (_) => {
            }
           ,
            Self::Variant51 (_) => {
            }
           ,
            Self::Variant52 (_) => {
            }
           ,
            Self::Variant53 (_) => {
            }
           ,
            Self::Variant54 (_) => {
            }
           ,
            Self::Variant55 (_) => {
            }
           ,
            Self::Variant56 (_) => {
            }
           ,
            Self::Variant57 (_) => {
            }
           ,
            Self::Variant58 (_) => {
            }
           ,
            Self::Variant59 (_) => {
            }
           ,
            Self::Variant60 (_) => {
            }
           ,
            Self::Variant61 (_) => {
            }
           ,
            Self::Variant62 (_) => {
            }
           ,
            Self::Variant63 (_) => {
            }
           ,
        }
    }
    pub broadcast proof fn lemma_into_from (input: Sum < Sum < Sum < Sum < Sum < Sum < T0,
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
    T31 > > > > >,
    Sum < Sum < Sum < Sum < Sum < T32,
    T33 >,
    Sum < T34,
    T35 > >,
    Sum < Sum < T36,
    T37 >,
    Sum < T38,
    T39 > > >,
    Sum < Sum < Sum < T40,
    T41 >,
    Sum < T42,
    T43 > >,
    Sum < Sum < T44,
    T45 >,
    Sum < T46,
    T47 > > > >,
    Sum < Sum < Sum < Sum < T48,
    T49 >,
    Sum < T50,
    T51 > >,
    Sum < Sum < T52,
    T53 >,
    Sum < T54,
    T55 > > >,
    Sum < Sum < Sum < T56,
    T57 >,
    Sum < T58,
    T59 > >,
    Sum < Sum < T60,
    T61 >,
    Sum < T62,
    T63 > > > > > >) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(ChoiceWidth64Spec::from_structural) ;
        reveal(ChoiceWidth64Spec::into_structural) ;
        match input {
            L (L (L (L (L (L (_)))))) => {
            }
           ,
            L (L (L (L (L (R (_)))))) => {
            }
           ,
            L (L (L (L (R (L (_)))))) => {
            }
           ,
            L (L (L (L (R (R (_)))))) => {
            }
           ,
            L (L (L (R (L (L (_)))))) => {
            }
           ,
            L (L (L (R (L (R (_)))))) => {
            }
           ,
            L (L (L (R (R (L (_)))))) => {
            }
           ,
            L (L (L (R (R (R (_)))))) => {
            }
           ,
            L (L (R (L (L (L (_)))))) => {
            }
           ,
            L (L (R (L (L (R (_)))))) => {
            }
           ,
            L (L (R (L (R (L (_)))))) => {
            }
           ,
            L (L (R (L (R (R (_)))))) => {
            }
           ,
            L (L (R (R (L (L (_)))))) => {
            }
           ,
            L (L (R (R (L (R (_)))))) => {
            }
           ,
            L (L (R (R (R (L (_)))))) => {
            }
           ,
            L (L (R (R (R (R (_)))))) => {
            }
           ,
            L (R (L (L (L (L (_)))))) => {
            }
           ,
            L (R (L (L (L (R (_)))))) => {
            }
           ,
            L (R (L (L (R (L (_)))))) => {
            }
           ,
            L (R (L (L (R (R (_)))))) => {
            }
           ,
            L (R (L (R (L (L (_)))))) => {
            }
           ,
            L (R (L (R (L (R (_)))))) => {
            }
           ,
            L (R (L (R (R (L (_)))))) => {
            }
           ,
            L (R (L (R (R (R (_)))))) => {
            }
           ,
            L (R (R (L (L (L (_)))))) => {
            }
           ,
            L (R (R (L (L (R (_)))))) => {
            }
           ,
            L (R (R (L (R (L (_)))))) => {
            }
           ,
            L (R (R (L (R (R (_)))))) => {
            }
           ,
            L (R (R (R (L (L (_)))))) => {
            }
           ,
            L (R (R (R (L (R (_)))))) => {
            }
           ,
            L (R (R (R (R (L (_)))))) => {
            }
           ,
            L (R (R (R (R (R (_)))))) => {
            }
           ,
            R (L (L (L (L (L (_)))))) => {
            }
           ,
            R (L (L (L (L (R (_)))))) => {
            }
           ,
            R (L (L (L (R (L (_)))))) => {
            }
           ,
            R (L (L (L (R (R (_)))))) => {
            }
           ,
            R (L (L (R (L (L (_)))))) => {
            }
           ,
            R (L (L (R (L (R (_)))))) => {
            }
           ,
            R (L (L (R (R (L (_)))))) => {
            }
           ,
            R (L (L (R (R (R (_)))))) => {
            }
           ,
            R (L (R (L (L (L (_)))))) => {
            }
           ,
            R (L (R (L (L (R (_)))))) => {
            }
           ,
            R (L (R (L (R (L (_)))))) => {
            }
           ,
            R (L (R (L (R (R (_)))))) => {
            }
           ,
            R (L (R (R (L (L (_)))))) => {
            }
           ,
            R (L (R (R (L (R (_)))))) => {
            }
           ,
            R (L (R (R (R (L (_)))))) => {
            }
           ,
            R (L (R (R (R (R (_)))))) => {
            }
           ,
            R (R (L (L (L (L (_)))))) => {
            }
           ,
            R (R (L (L (L (R (_)))))) => {
            }
           ,
            R (R (L (L (R (L (_)))))) => {
            }
           ,
            R (R (L (L (R (R (_)))))) => {
            }
           ,
            R (R (L (R (L (L (_)))))) => {
            }
           ,
            R (R (L (R (L (R (_)))))) => {
            }
           ,
            R (R (L (R (R (L (_)))))) => {
            }
           ,
            R (R (L (R (R (R (_)))))) => {
            }
           ,
            R (R (R (L (L (L (_)))))) => {
            }
           ,
            R (R (R (L (L (R (_)))))) => {
            }
           ,
            R (R (R (L (R (L (_)))))) => {
            }
           ,
            R (R (R (L (R (R (_)))))) => {
            }
           ,
            R (R (R (R (L (L (_)))))) => {
            }
           ,
            R (R (R (R (L (R (_)))))) => {
            }
           ,
            R (R (R (R (R (L (_)))))) => {
            }
           ,
            R (R (R (R (R (R (_)))))) => {
            }
           ,
        }
    }
    pub proof fn lemma_into_structural_variant (self) ensures Self::into_structural (self) == match self {
        Self::Variant0 (value) => L (L (L (L (L (L (value)))))),
        Self::Variant1 (value) => L (L (L (L (L (R (value)))))),
        Self::Variant2 (value) => L (L (L (L (R (L (value)))))),
        Self::Variant3 (value) => L (L (L (L (R (R (value)))))),
        Self::Variant4 (value) => L (L (L (R (L (L (value)))))),
        Self::Variant5 (value) => L (L (L (R (L (R (value)))))),
        Self::Variant6 (value) => L (L (L (R (R (L (value)))))),
        Self::Variant7 (value) => L (L (L (R (R (R (value)))))),
        Self::Variant8 (value) => L (L (R (L (L (L (value)))))),
        Self::Variant9 (value) => L (L (R (L (L (R (value)))))),
        Self::Variant10 (value) => L (L (R (L (R (L (value)))))),
        Self::Variant11 (value) => L (L (R (L (R (R (value)))))),
        Self::Variant12 (value) => L (L (R (R (L (L (value)))))),
        Self::Variant13 (value) => L (L (R (R (L (R (value)))))),
        Self::Variant14 (value) => L (L (R (R (R (L (value)))))),
        Self::Variant15 (value) => L (L (R (R (R (R (value)))))),
        Self::Variant16 (value) => L (R (L (L (L (L (value)))))),
        Self::Variant17 (value) => L (R (L (L (L (R (value)))))),
        Self::Variant18 (value) => L (R (L (L (R (L (value)))))),
        Self::Variant19 (value) => L (R (L (L (R (R (value)))))),
        Self::Variant20 (value) => L (R (L (R (L (L (value)))))),
        Self::Variant21 (value) => L (R (L (R (L (R (value)))))),
        Self::Variant22 (value) => L (R (L (R (R (L (value)))))),
        Self::Variant23 (value) => L (R (L (R (R (R (value)))))),
        Self::Variant24 (value) => L (R (R (L (L (L (value)))))),
        Self::Variant25 (value) => L (R (R (L (L (R (value)))))),
        Self::Variant26 (value) => L (R (R (L (R (L (value)))))),
        Self::Variant27 (value) => L (R (R (L (R (R (value)))))),
        Self::Variant28 (value) => L (R (R (R (L (L (value)))))),
        Self::Variant29 (value) => L (R (R (R (L (R (value)))))),
        Self::Variant30 (value) => L (R (R (R (R (L (value)))))),
        Self::Variant31 (value) => L (R (R (R (R (R (value)))))),
        Self::Variant32 (value) => R (L (L (L (L (L (value)))))),
        Self::Variant33 (value) => R (L (L (L (L (R (value)))))),
        Self::Variant34 (value) => R (L (L (L (R (L (value)))))),
        Self::Variant35 (value) => R (L (L (L (R (R (value)))))),
        Self::Variant36 (value) => R (L (L (R (L (L (value)))))),
        Self::Variant37 (value) => R (L (L (R (L (R (value)))))),
        Self::Variant38 (value) => R (L (L (R (R (L (value)))))),
        Self::Variant39 (value) => R (L (L (R (R (R (value)))))),
        Self::Variant40 (value) => R (L (R (L (L (L (value)))))),
        Self::Variant41 (value) => R (L (R (L (L (R (value)))))),
        Self::Variant42 (value) => R (L (R (L (R (L (value)))))),
        Self::Variant43 (value) => R (L (R (L (R (R (value)))))),
        Self::Variant44 (value) => R (L (R (R (L (L (value)))))),
        Self::Variant45 (value) => R (L (R (R (L (R (value)))))),
        Self::Variant46 (value) => R (L (R (R (R (L (value)))))),
        Self::Variant47 (value) => R (L (R (R (R (R (value)))))),
        Self::Variant48 (value) => R (R (L (L (L (L (value)))))),
        Self::Variant49 (value) => R (R (L (L (L (R (value)))))),
        Self::Variant50 (value) => R (R (L (L (R (L (value)))))),
        Self::Variant51 (value) => R (R (L (L (R (R (value)))))),
        Self::Variant52 (value) => R (R (L (R (L (L (value)))))),
        Self::Variant53 (value) => R (R (L (R (L (R (value)))))),
        Self::Variant54 (value) => R (R (L (R (R (L (value)))))),
        Self::Variant55 (value) => R (R (L (R (R (R (value)))))),
        Self::Variant56 (value) => R (R (R (L (L (L (value)))))),
        Self::Variant57 (value) => R (R (R (L (L (R (value)))))),
        Self::Variant58 (value) => R (R (R (L (R (L (value)))))),
        Self::Variant59 (value) => R (R (R (L (R (R (value)))))),
        Self::Variant60 (value) => R (R (R (R (L (L (value)))))),
        Self::Variant61 (value) => R (R (R (R (L (R (value)))))),
        Self::Variant62 (value) => R (R (R (R (R (L (value)))))),
        Self::Variant63 (value) => R (R (R (R (R (R (value)))))),
    }
   ,
    {
        reveal(ChoiceWidth64Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth64Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct ChoiceWidth64Reverse ;
impl SpecMap for ChoiceWidth64Forward {
    type Input = ChoiceWidth64Inner ;
    type Output = ChoiceWidth64Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        ChoiceWidth64Spec::from_structural (input)
    }
}
impl SpecMap for ChoiceWidth64Reverse {
    type Input = ChoiceWidth64Spec ;
    type Output = ChoiceWidth64Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `struct_width16`."]
# [derive (Clone, Copy)]
pub struct StructWidth16Fmt ;

pub type StructWidth16FmtSpec = Named < Mapped < Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, U8 > > > > > > > > > > > > > > >, BiMap < StructWidth16Forward, StructWidth16Reverse >> > ;

impl StructWidth16Fmt {
    # [doc = "specification constructor for `struct_width16`."] pub open spec fn spec_inner() -> StructWidth16FmtSpec {
        Named ("struct_width16",
        Mapped {
            inner: Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            Pair (U8,
            U8))))))))))))))),
            mapper: BiMap (StructWidth16Forward,
            StructWidth16Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `choice_width64`."]
# [derive (Clone, Copy)]
pub struct ChoiceWidth64Fmt ;

pub type ChoiceWidth64FmtSpec = Named < Mapped < Choice < Choice < Choice < Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > >, Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > > >, Choice < Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > >, Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > > > >, Choice < Choice < Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > >, Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > > >, Choice < Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > >, Choice < Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > >, Choice < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> > > > > > >, BiMap < ChoiceWidth64Forward, ChoiceWidth64Reverse >> > ;

impl ChoiceWidth64Fmt {
    # [doc = "specification constructor for `choice_width64`."] pub open spec fn spec_inner() -> ChoiceWidth64FmtSpec {
        Named ("choice_width64",
        Mapped {
            inner: Choice (Choice (Choice (Choice (Choice (Choice (Refined (U8,
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
            | x: u8 | x == 31)))))),
            Choice (Choice (Choice (Choice (Choice (Refined (U8,
            | x: u8 | x == 32),
            Refined (U8,
            | x: u8 | x == 33)),
            Choice (Refined (U8,
            | x: u8 | x == 34),
            Refined (U8,
            | x: u8 | x == 35))),
            Choice (Choice (Refined (U8,
            | x: u8 | x == 36),
            Refined (U8,
            | x: u8 | x == 37)),
            Choice (Refined (U8,
            | x: u8 | x == 38),
            Refined (U8,
            | x: u8 | x == 39)))),
            Choice (Choice (Choice (Refined (U8,
            | x: u8 | x == 40),
            Refined (U8,
            | x: u8 | x == 41)),
            Choice (Refined (U8,
            | x: u8 | x == 42),
            Refined (U8,
            | x: u8 | x == 43))),
            Choice (Choice (Refined (U8,
            | x: u8 | x == 44),
            Refined (U8,
            | x: u8 | x == 45)),
            Choice (Refined (U8,
            | x: u8 | x == 46),
            Refined (U8,
            | x: u8 | x == 47))))),
            Choice (Choice (Choice (Choice (Refined (U8,
            | x: u8 | x == 48),
            Refined (U8,
            | x: u8 | x == 49)),
            Choice (Refined (U8,
            | x: u8 | x == 50),
            Refined (U8,
            | x: u8 | x == 51))),
            Choice (Choice (Refined (U8,
            | x: u8 | x == 52),
            Refined (U8,
            | x: u8 | x == 53)),
            Choice (Refined (U8,
            | x: u8 | x == 54),
            Refined (U8,
            | x: u8 | x == 55)))),
            Choice (Choice (Choice (Refined (U8,
            | x: u8 | x == 56),
            Refined (U8,
            | x: u8 | x == 57)),
            Choice (Refined (U8,
            | x: u8 | x == 58),
            Refined (U8,
            | x: u8 | x == 59))),
            Choice (Choice (Refined (U8,
            | x: u8 | x == 60),
            Refined (U8,
            | x: u8 | x == 61)),
            Choice (Refined (U8,
            | x: u8 | x == 62),
            Refined (U8,
            | x: u8 | x >= 63))))))),
            mapper: BiMap (ChoiceWidth64Forward,
            ChoiceWidth64Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for StructWidth16Fmt {
        type PVal = StructWidth16Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for StructWidth16Fmt {
        type Val = StructWidth16Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for StructWidth16Fmt {
        type SValue = StructWidth16Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for StructWidth16Fmt {
        type SVal = StructWidth16Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for StructWidth16Fmt {
        type T = StructWidth16Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for ChoiceWidth64Fmt {
        type PVal = ChoiceWidth64Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for ChoiceWidth64Fmt {
        type Val = ChoiceWidth64Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for ChoiceWidth64Fmt {
        type SValue = ChoiceWidth64Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for ChoiceWidth64Fmt {
        type SVal = ChoiceWidth64Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for ChoiceWidth64Fmt {
        type T = ChoiceWidth64Spec ;
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
        vest_lib::combinators::disjoint::disjointness_lemmas,
        StructWidth16Spec::lemma_from_into,
        StructWidth16Spec::lemma_into_from,
        ChoiceWidth64Spec::lemma_from_into,
        ChoiceWidth64Spec::lemma_into_from,
    };

    impl SafeParser for StructWidth16Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for StructWidth16Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for StructWidth16Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            reveal(< StructWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: StructWidth16Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                StructWidth16Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            reveal(< StructWidth16Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: StructWidth16Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                StructWidth16Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for StructWidth16Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for StructWidth16Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< StructWidth16Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< StructWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for StructWidth16Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            reveal(< StructWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth16Fmt as Consistency>::consistent) ;
            reveal(< StructWidth16Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: StructWidth16Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                StructWidth16Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for StructWidth16Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: StructWidth16Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                StructWidth16Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for StructWidth16Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< StructWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth16Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for StructWidth16Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< StructWidth16Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< StructWidth16Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for ChoiceWidth64Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth64Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for ChoiceWidth64Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< ChoiceWidth64Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for ChoiceWidth64Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth64Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth64Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth64Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth64Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< ChoiceWidth64Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth64Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth64Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth64Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for ChoiceWidth64Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth64Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth64Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth64Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for ChoiceWidth64Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth64Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< ChoiceWidth64Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for ChoiceWidth64Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth64Fmt as SpecParser>::spec_parse) ;
            reveal(< ChoiceWidth64Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth64Fmt as Consistency>::consistent) ;
            reveal(< ChoiceWidth64Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: ChoiceWidth64Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                ChoiceWidth64Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for ChoiceWidth64Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< ChoiceWidth64Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: ChoiceWidth64Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                ChoiceWidth64Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for ChoiceWidth64Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< ChoiceWidth64Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth64Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for ChoiceWidth64Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< ChoiceWidth64Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< ChoiceWidth64Fmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for StructWidth16Fmt {
        type PT = StructWidth16;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<StructWidth16Fmt as SpecParser>::spec_parse);
            reveal(<StructWidth16 as DeepView>::deep_view);
            reveal(StructWidth16Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, field0) = (U8).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, field1) = (U8).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, field2) = (U8).parse (& rest) ?;
            let rest = rest.skip(n3);
            let (n4, field3) = (U8).parse (& rest) ?;
            let rest = rest.skip(n4);
            let (n5, field4) = (U8).parse (& rest) ?;
            let rest = rest.skip(n5);
            let (n6, field5) = (U8).parse (& rest) ?;
            let rest = rest.skip(n6);
            let (n7, field6) = (U8).parse (& rest) ?;
            let rest = rest.skip(n7);
            let (n8, field7) = (U8).parse (& rest) ?;
            let rest = rest.skip(n8);
            let (n9, field8) = (U8).parse (& rest) ?;
            let rest = rest.skip(n9);
            let (n10, field9) = (U8).parse (& rest) ?;
            let rest = rest.skip(n10);
            let (n11, field10) = (U8).parse (& rest) ?;
            let rest = rest.skip(n11);
            let (n12, field11) = (U8).parse (& rest) ?;
            let rest = rest.skip(n12);
            let (n13, field12) = (U8).parse (& rest) ?;
            let rest = rest.skip(n13);
            let (n14, field13) = (U8).parse (& rest) ?;
            let rest = rest.skip(n14);
            let (n15, field14) = (U8).parse (& rest) ?;
            let rest = rest.skip(n15);
            let (n16, field15) = (U8).parse (& rest) ?;
            let rest = rest.skip(n16);
            let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n10 + n11 + n12 + n13 + n14 + n15 + n16;
            let final_v = StructWidth16 {
                field0,
                field1,
                field2,
                field3,
                field4,
                field5,
                field6,
                field7,
                field8,
                field9,
                field10,
                field11,
                field12,
                field13,
                field14,
                field15,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, StructWidth16> for StructWidth16Fmt {
        fn serialize_into(&self, v: &StructWidth16, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<StructWidth16Fmt as SpecSerializer>::spec_serialize);
            reveal(<StructWidth16Fmt as SpecByteLen>::byte_len);
            reveal(<StructWidth16 as DeepView>::deep_view);
            reveal(StructWidth16Spec::into_structural);
            let ghost old_obuf = obuf@;

            let StructWidth16 {
                field0,
                field1,
                field2,
                field3,
                field4,
                field5,
                field6,
                field7,
                field8,
                field9,
                field10,
                field11,
                field12,
                field13,
                field14,
                field15,
            } = v;
            U8.serialize_into(field0, obuf);
            U8.serialize_into(field1, obuf);
            U8.serialize_into(field2, obuf);
            U8.serialize_into(field3, obuf);
            U8.serialize_into(field4, obuf);
            U8.serialize_into(field5, obuf);
            U8.serialize_into(field6, obuf);
            U8.serialize_into(field7, obuf);
            U8.serialize_into(field8, obuf);
            U8.serialize_into(field9, obuf);
            U8.serialize_into(field10, obuf);
            U8.serialize_into(field11, obuf);
            U8.serialize_into(field12, obuf);
            U8.serialize_into(field13, obuf);
            U8.serialize_into(field14, obuf);
            U8.serialize_into(field15, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<StructWidth16> for StructWidth16Fmt {
        fn prepare(&self, v: &StructWidth16) -> Result<usize, PreSerializeError> {
            reveal(<StructWidth16Fmt as SpecByteLen>::byte_len);
            reveal(<StructWidth16 as DeepView>::deep_view);
            reveal(StructWidth16Spec::into_structural);
            let StructWidth16 {
                field0,
                field1,
                field2,
                field3,
                field4,
                field5,
                field6,
                field7,
                field8,
                field9,
                field10,
                field11,
                field12,
                field13,
                field14,
                field15,
            } = v;
            let l1 = (U8).prepare (field0) ?;
            let l2 = (U8).prepare (field1) ?;
            let l3 = (U8).prepare (field2) ?;
            let l4 = (U8).prepare (field3) ?;
            let l5 = (U8).prepare (field4) ?;
            let l6 = (U8).prepare (field5) ?;
            let l7 = (U8).prepare (field6) ?;
            let l8 = (U8).prepare (field7) ?;
            let l9 = (U8).prepare (field8) ?;
            let l10 = (U8).prepare (field9) ?;
            let l11 = (U8).prepare (field10) ?;
            let l12 = (U8).prepare (field11) ?;
            let l13 = (U8).prepare (field12) ?;
            let l14 = (U8).prepare (field13) ?;
            let l15 = (U8).prepare (field14) ?;
            let l16 = (U8).prepare (field15) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l4).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l5).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l6).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l7).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l8).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l9).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l10).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l11).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l12).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l13).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l14).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l15).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l16).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for ChoiceWidth64Fmt {
        type PT = ChoiceWidth64;

        #[verifier::spinoff_prover]
        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<ChoiceWidth64Fmt as SpecParser>::spec_parse);
            reveal(<ChoiceWidth64 as DeepView>::deep_view);
            reveal(ChoiceWidth64Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = match (U8).parse (& rest) {
        Ok ((n,
        va)) if va == 0 => {
            Ok ((n,
            ChoiceWidth64::Variant0 (va)))
        }
       ,
        _ => match (U8).parse (& rest) {
            Ok ((n,
            va)) if va == 1 => {
                Ok ((n,
                ChoiceWidth64::Variant1 (va)))
            }
           ,
            _ => match (U8).parse (& rest) {
                Ok ((n,
                va)) if va == 2 => {
                    Ok ((n,
                    ChoiceWidth64::Variant2 (va)))
                }
               ,
                _ => match (U8).parse (& rest) {
                    Ok ((n,
                    va)) if va == 3 => {
                        Ok ((n,
                        ChoiceWidth64::Variant3 (va)))
                    }
                   ,
                    _ => match (U8).parse (& rest) {
                        Ok ((n,
                        va)) if va == 4 => {
                            Ok ((n,
                            ChoiceWidth64::Variant4 (va)))
                        }
                       ,
                        _ => match (U8).parse (& rest) {
                            Ok ((n,
                            va)) if va == 5 => {
                                Ok ((n,
                                ChoiceWidth64::Variant5 (va)))
                            }
                           ,
                            _ => match (U8).parse (& rest) {
                                Ok ((n,
                                va)) if va == 6 => {
                                    Ok ((n,
                                    ChoiceWidth64::Variant6 (va)))
                                }
                               ,
                                _ => match (U8).parse (& rest) {
                                    Ok ((n,
                                    va)) if va == 7 => {
                                        Ok ((n,
                                        ChoiceWidth64::Variant7 (va)))
                                    }
                                   ,
                                    _ => match (U8).parse (& rest) {
                                        Ok ((n,
                                        va)) if va == 8 => {
                                            Ok ((n,
                                            ChoiceWidth64::Variant8 (va)))
                                        }
                                       ,
                                        _ => match (U8).parse (& rest) {
                                            Ok ((n,
                                            va)) if va == 9 => {
                                                Ok ((n,
                                                ChoiceWidth64::Variant9 (va)))
                                            }
                                           ,
                                            _ => match (U8).parse (& rest) {
                                                Ok ((n,
                                                va)) if va == 10 => {
                                                    Ok ((n,
                                                    ChoiceWidth64::Variant10 (va)))
                                                }
                                               ,
                                                _ => match (U8).parse (& rest) {
                                                    Ok ((n,
                                                    va)) if va == 11 => {
                                                        Ok ((n,
                                                        ChoiceWidth64::Variant11 (va)))
                                                    }
                                                   ,
                                                    _ => match (U8).parse (& rest) {
                                                        Ok ((n,
                                                        va)) if va == 12 => {
                                                            Ok ((n,
                                                            ChoiceWidth64::Variant12 (va)))
                                                        }
                                                       ,
                                                        _ => match (U8).parse (& rest) {
                                                            Ok ((n,
                                                            va)) if va == 13 => {
                                                                Ok ((n,
                                                                ChoiceWidth64::Variant13 (va)))
                                                            }
                                                           ,
                                                            _ => match (U8).parse (& rest) {
                                                                Ok ((n,
                                                                va)) if va == 14 => {
                                                                    Ok ((n,
                                                                    ChoiceWidth64::Variant14 (va)))
                                                                }
                                                               ,
                                                                _ => match (U8).parse (& rest) {
                                                                    Ok ((n,
                                                                    va)) if va == 15 => {
                                                                        Ok ((n,
                                                                        ChoiceWidth64::Variant15 (va)))
                                                                    }
                                                                   ,
                                                                    _ => match (U8).parse (& rest) {
                                                                        Ok ((n,
                                                                        va)) if va == 16 => {
                                                                            Ok ((n,
                                                                            ChoiceWidth64::Variant16 (va)))
                                                                        }
                                                                       ,
                                                                        _ => match (U8).parse (& rest) {
                                                                            Ok ((n,
                                                                            va)) if va == 17 => {
                                                                                Ok ((n,
                                                                                ChoiceWidth64::Variant17 (va)))
                                                                            }
                                                                           ,
                                                                            _ => match (U8).parse (& rest) {
                                                                                Ok ((n,
                                                                                va)) if va == 18 => {
                                                                                    Ok ((n,
                                                                                    ChoiceWidth64::Variant18 (va)))
                                                                                }
                                                                               ,
                                                                                _ => match (U8).parse (& rest) {
                                                                                    Ok ((n,
                                                                                    va)) if va == 19 => {
                                                                                        Ok ((n,
                                                                                        ChoiceWidth64::Variant19 (va)))
                                                                                    }
                                                                                   ,
                                                                                    _ => match (U8).parse (& rest) {
                                                                                        Ok ((n,
                                                                                        va)) if va == 20 => {
                                                                                            Ok ((n,
                                                                                            ChoiceWidth64::Variant20 (va)))
                                                                                        }
                                                                                       ,
                                                                                        _ => match (U8).parse (& rest) {
                                                                                            Ok ((n,
                                                                                            va)) if va == 21 => {
                                                                                                Ok ((n,
                                                                                                ChoiceWidth64::Variant21 (va)))
                                                                                            }
                                                                                           ,
                                                                                            _ => match (U8).parse (& rest) {
                                                                                                Ok ((n,
                                                                                                va)) if va == 22 => {
                                                                                                    Ok ((n,
                                                                                                    ChoiceWidth64::Variant22 (va)))
                                                                                                }
                                                                                               ,
                                                                                                _ => match (U8).parse (& rest) {
                                                                                                    Ok ((n,
                                                                                                    va)) if va == 23 => {
                                                                                                        Ok ((n,
                                                                                                        ChoiceWidth64::Variant23 (va)))
                                                                                                    }
                                                                                                   ,
                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                        Ok ((n,
                                                                                                        va)) if va == 24 => {
                                                                                                            Ok ((n,
                                                                                                            ChoiceWidth64::Variant24 (va)))
                                                                                                        }
                                                                                                       ,
                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                            Ok ((n,
                                                                                                            va)) if va == 25 => {
                                                                                                                Ok ((n,
                                                                                                                ChoiceWidth64::Variant25 (va)))
                                                                                                            }
                                                                                                           ,
                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                Ok ((n,
                                                                                                                va)) if va == 26 => {
                                                                                                                    Ok ((n,
                                                                                                                    ChoiceWidth64::Variant26 (va)))
                                                                                                                }
                                                                                                               ,
                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                    Ok ((n,
                                                                                                                    va)) if va == 27 => {
                                                                                                                        Ok ((n,
                                                                                                                        ChoiceWidth64::Variant27 (va)))
                                                                                                                    }
                                                                                                                   ,
                                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                                        Ok ((n,
                                                                                                                        va)) if va == 28 => {
                                                                                                                            Ok ((n,
                                                                                                                            ChoiceWidth64::Variant28 (va)))
                                                                                                                        }
                                                                                                                       ,
                                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                                            Ok ((n,
                                                                                                                            va)) if va == 29 => {
                                                                                                                                Ok ((n,
                                                                                                                                ChoiceWidth64::Variant29 (va)))
                                                                                                                            }
                                                                                                                           ,
                                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                                Ok ((n,
                                                                                                                                va)) if va == 30 => {
                                                                                                                                    Ok ((n,
                                                                                                                                    ChoiceWidth64::Variant30 (va)))
                                                                                                                                }
                                                                                                                               ,
                                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                                    Ok ((n,
                                                                                                                                    va)) if va == 31 => {
                                                                                                                                        Ok ((n,
                                                                                                                                        ChoiceWidth64::Variant31 (va)))
                                                                                                                                    }
                                                                                                                                   ,
                                                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                                                        Ok ((n,
                                                                                                                                        va)) if va == 32 => {
                                                                                                                                            Ok ((n,
                                                                                                                                            ChoiceWidth64::Variant32 (va)))
                                                                                                                                        }
                                                                                                                                       ,
                                                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                                                            Ok ((n,
                                                                                                                                            va)) if va == 33 => {
                                                                                                                                                Ok ((n,
                                                                                                                                                ChoiceWidth64::Variant33 (va)))
                                                                                                                                            }
                                                                                                                                           ,
                                                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                                                Ok ((n,
                                                                                                                                                va)) if va == 34 => {
                                                                                                                                                    Ok ((n,
                                                                                                                                                    ChoiceWidth64::Variant34 (va)))
                                                                                                                                                }
                                                                                                                                               ,
                                                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                                                    Ok ((n,
                                                                                                                                                    va)) if va == 35 => {
                                                                                                                                                        Ok ((n,
                                                                                                                                                        ChoiceWidth64::Variant35 (va)))
                                                                                                                                                    }
                                                                                                                                                   ,
                                                                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                                                                        Ok ((n,
                                                                                                                                                        va)) if va == 36 => {
                                                                                                                                                            Ok ((n,
                                                                                                                                                            ChoiceWidth64::Variant36 (va)))
                                                                                                                                                        }
                                                                                                                                                       ,
                                                                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                                                                            Ok ((n,
                                                                                                                                                            va)) if va == 37 => {
                                                                                                                                                                Ok ((n,
                                                                                                                                                                ChoiceWidth64::Variant37 (va)))
                                                                                                                                                            }
                                                                                                                                                           ,
                                                                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                                                                Ok ((n,
                                                                                                                                                                va)) if va == 38 => {
                                                                                                                                                                    Ok ((n,
                                                                                                                                                                    ChoiceWidth64::Variant38 (va)))
                                                                                                                                                                }
                                                                                                                                                               ,
                                                                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                                                                    Ok ((n,
                                                                                                                                                                    va)) if va == 39 => {
                                                                                                                                                                        Ok ((n,
                                                                                                                                                                        ChoiceWidth64::Variant39 (va)))
                                                                                                                                                                    }
                                                                                                                                                                   ,
                                                                                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                                                                                        Ok ((n,
                                                                                                                                                                        va)) if va == 40 => {
                                                                                                                                                                            Ok ((n,
                                                                                                                                                                            ChoiceWidth64::Variant40 (va)))
                                                                                                                                                                        }
                                                                                                                                                                       ,
                                                                                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                                                                                            Ok ((n,
                                                                                                                                                                            va)) if va == 41 => {
                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                ChoiceWidth64::Variant41 (va)))
                                                                                                                                                                            }
                                                                                                                                                                           ,
                                                                                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                va)) if va == 42 => {
                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                    ChoiceWidth64::Variant42 (va)))
                                                                                                                                                                                }
                                                                                                                                                                               ,
                                                                                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                    va)) if va == 43 => {
                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                        ChoiceWidth64::Variant43 (va)))
                                                                                                                                                                                    }
                                                                                                                                                                                   ,
                                                                                                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                        va)) if va == 44 => {
                                                                                                                                                                                            Ok ((n,
                                                                                                                                                                                            ChoiceWidth64::Variant44 (va)))
                                                                                                                                                                                        }
                                                                                                                                                                                       ,
                                                                                                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                                                                                                            Ok ((n,
                                                                                                                                                                                            va)) if va == 45 => {
                                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                                ChoiceWidth64::Variant45 (va)))
                                                                                                                                                                                            }
                                                                                                                                                                                           ,
                                                                                                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                                va)) if va == 46 => {
                                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                                    ChoiceWidth64::Variant46 (va)))
                                                                                                                                                                                                }
                                                                                                                                                                                               ,
                                                                                                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                                    va)) if va == 47 => {
                                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                                        ChoiceWidth64::Variant47 (va)))
                                                                                                                                                                                                    }
                                                                                                                                                                                                   ,
                                                                                                                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                                        va)) if va == 48 => {
                                                                                                                                                                                                            Ok ((n,
                                                                                                                                                                                                            ChoiceWidth64::Variant48 (va)))
                                                                                                                                                                                                        }
                                                                                                                                                                                                       ,
                                                                                                                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                                                                                                                            Ok ((n,
                                                                                                                                                                                                            va)) if va == 49 => {
                                                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                                                ChoiceWidth64::Variant49 (va)))
                                                                                                                                                                                                            }
                                                                                                                                                                                                           ,
                                                                                                                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                                                va)) if va == 50 => {
                                                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                                                    ChoiceWidth64::Variant50 (va)))
                                                                                                                                                                                                                }
                                                                                                                                                                                                               ,
                                                                                                                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                                                    va)) if va == 51 => {
                                                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                                                        ChoiceWidth64::Variant51 (va)))
                                                                                                                                                                                                                    }
                                                                                                                                                                                                                   ,
                                                                                                                                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                                                        va)) if va == 52 => {
                                                                                                                                                                                                                            Ok ((n,
                                                                                                                                                                                                                            ChoiceWidth64::Variant52 (va)))
                                                                                                                                                                                                                        }
                                                                                                                                                                                                                       ,
                                                                                                                                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                            Ok ((n,
                                                                                                                                                                                                                            va)) if va == 53 => {
                                                                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                                                                ChoiceWidth64::Variant53 (va)))
                                                                                                                                                                                                                            }
                                                                                                                                                                                                                           ,
                                                                                                                                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                                                                va)) if va == 54 => {
                                                                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                                                                    ChoiceWidth64::Variant54 (va)))
                                                                                                                                                                                                                                }
                                                                                                                                                                                                                               ,
                                                                                                                                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                                                                    va)) if va == 55 => {
                                                                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                                                                        ChoiceWidth64::Variant55 (va)))
                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                   ,
                                                                                                                                                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                                                                        va)) if va == 56 => {
                                                                                                                                                                                                                                            Ok ((n,
                                                                                                                                                                                                                                            ChoiceWidth64::Variant56 (va)))
                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                       ,
                                                                                                                                                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                                            Ok ((n,
                                                                                                                                                                                                                                            va)) if va == 57 => {
                                                                                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                                                                                ChoiceWidth64::Variant57 (va)))
                                                                                                                                                                                                                                            }
                                                                                                                                                                                                                                           ,
                                                                                                                                                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                                                                                va)) if va == 58 => {
                                                                                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                                                                                    ChoiceWidth64::Variant58 (va)))
                                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                               ,
                                                                                                                                                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                                                                                    va)) if va == 59 => {
                                                                                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                                                                                        ChoiceWidth64::Variant59 (va)))
                                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                                   ,
                                                                                                                                                                                                                                                    _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                                                                                        va)) if va == 60 => {
                                                                                                                                                                                                                                                            Ok ((n,
                                                                                                                                                                                                                                                            ChoiceWidth64::Variant60 (va)))
                                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                                       ,
                                                                                                                                                                                                                                                        _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                                                            Ok ((n,
                                                                                                                                                                                                                                                            va)) if va == 61 => {
                                                                                                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                                                                                                ChoiceWidth64::Variant61 (va)))
                                                                                                                                                                                                                                                            }
                                                                                                                                                                                                                                                           ,
                                                                                                                                                                                                                                                            _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                                                                Ok ((n,
                                                                                                                                                                                                                                                                va)) if va == 62 => {
                                                                                                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                                                                                                    ChoiceWidth64::Variant62 (va)))
                                                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                                               ,
                                                                                                                                                                                                                                                                _ => match (U8).parse (& rest) {
                                                                                                                                                                                                                                                                    Ok ((n,
                                                                                                                                                                                                                                                                    va)) if va >= 63 => {
                                                                                                                                                                                                                                                                        Ok ((n,
                                                                                                                                                                                                                                                                        ChoiceWidth64::Variant63 (va)))
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
       ,
    }
    ?;
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, ChoiceWidth64> for ChoiceWidth64Fmt {
        #[verifier::spinoff_prover]
        fn serialize_into(&self, v: &ChoiceWidth64, obuf: &mut Output) {
            reveal(<ChoiceWidth64Fmt as SpecSerializer>::spec_serialize);
            reveal(<ChoiceWidth64Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth64 as DeepView>::deep_view);
            reveal(ChoiceWidth64Spec::into_structural);
            let ghost old_obuf = obuf@;

            match v {
                ChoiceWidth64::Variant0 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant1 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant2 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant3 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant4 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant5 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant6 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant7 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant8 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant9 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant10 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant11 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant12 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant13 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant14 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant15 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant16 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant17 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant18 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant19 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant20 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant21 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant22 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant23 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant24 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant25 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant26 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant27 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant28 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant29 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant30 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant31 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant32 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant33 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant34 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant35 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant36 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant37 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant38 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant39 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant40 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant41 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant42 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant43 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant44 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant45 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant46 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant47 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant48 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant49 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant50 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant51 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant52 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant53 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant54 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant55 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant56 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant57 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant58 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant59 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant60 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant61 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant62 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
                ChoiceWidth64::Variant63 (v) => {
                    (U8).serialize_into (v,
                    obuf) ;
                }
                ,
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<ChoiceWidth64> for ChoiceWidth64Fmt {
        #[verifier::spinoff_prover]
        fn prepare(&self, v: &ChoiceWidth64) -> Result<usize, PreSerializeError> {
            reveal(<ChoiceWidth64Fmt as SpecByteLen>::byte_len);
            reveal(<ChoiceWidth64 as DeepView>::deep_view);
            reveal(ChoiceWidth64Spec::into_structural);
            match v {
                ChoiceWidth64::Variant0 (v) => {
                    if ! (*v == 0) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant1 (v) => {
                    if ! (*v == 1) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant2 (v) => {
                    if ! (*v == 2) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant3 (v) => {
                    if ! (*v == 3) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant4 (v) => {
                    if ! (*v == 4) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant5 (v) => {
                    if ! (*v == 5) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant6 (v) => {
                    if ! (*v == 6) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant7 (v) => {
                    if ! (*v == 7) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant8 (v) => {
                    if ! (*v == 8) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant9 (v) => {
                    if ! (*v == 9) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant10 (v) => {
                    if ! (*v == 10) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant11 (v) => {
                    if ! (*v == 11) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant12 (v) => {
                    if ! (*v == 12) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant13 (v) => {
                    if ! (*v == 13) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant14 (v) => {
                    if ! (*v == 14) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant15 (v) => {
                    if ! (*v == 15) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant16 (v) => {
                    if ! (*v == 16) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant17 (v) => {
                    if ! (*v == 17) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant18 (v) => {
                    if ! (*v == 18) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant19 (v) => {
                    if ! (*v == 19) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant20 (v) => {
                    if ! (*v == 20) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant21 (v) => {
                    if ! (*v == 21) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant22 (v) => {
                    if ! (*v == 22) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant23 (v) => {
                    if ! (*v == 23) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant24 (v) => {
                    if ! (*v == 24) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant25 (v) => {
                    if ! (*v == 25) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant26 (v) => {
                    if ! (*v == 26) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant27 (v) => {
                    if ! (*v == 27) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant28 (v) => {
                    if ! (*v == 28) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant29 (v) => {
                    if ! (*v == 29) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant30 (v) => {
                    if ! (*v == 30) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant31 (v) => {
                    if ! (*v == 31) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant32 (v) => {
                    if ! (*v == 32) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant33 (v) => {
                    if ! (*v == 33) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant34 (v) => {
                    if ! (*v == 34) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant35 (v) => {
                    if ! (*v == 35) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant36 (v) => {
                    if ! (*v == 36) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant37 (v) => {
                    if ! (*v == 37) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant38 (v) => {
                    if ! (*v == 38) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant39 (v) => {
                    if ! (*v == 39) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant40 (v) => {
                    if ! (*v == 40) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant41 (v) => {
                    if ! (*v == 41) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant42 (v) => {
                    if ! (*v == 42) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant43 (v) => {
                    if ! (*v == 43) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant44 (v) => {
                    if ! (*v == 44) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant45 (v) => {
                    if ! (*v == 45) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant46 (v) => {
                    if ! (*v == 46) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant47 (v) => {
                    if ! (*v == 47) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant48 (v) => {
                    if ! (*v == 48) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant49 (v) => {
                    if ! (*v == 49) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant50 (v) => {
                    if ! (*v == 50) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant51 (v) => {
                    if ! (*v == 51) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant52 (v) => {
                    if ! (*v == 52) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant53 (v) => {
                    if ! (*v == 53) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant54 (v) => {
                    if ! (*v == 54) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant55 (v) => {
                    if ! (*v == 55) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant56 (v) => {
                    if ! (*v == 56) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant57 (v) => {
                    if ! (*v == 57) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant58 (v) => {
                    if ! (*v == 58) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant59 (v) => {
                    if ! (*v == 59) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant60 (v) => {
                    if ! (*v == 60) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant61 (v) => {
                    if ! (*v == 61) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant62 (v) => {
                    if ! (*v == 62) {
                        Err (PreSerializeError::not_compliant (ComplianceErrorKind::PredicateFailed))
                    }
                    else {
                        (U8).prepare (v)
                    }
                }
                ,
                ChoiceWidth64::Variant63 (v) => {
                    if ! (*v >= 63) {
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
