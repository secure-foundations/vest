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
# [doc = "data type for `tst_tag`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum TstTag {
    C0 = 0,
    C1 = 1,
    C2 = 2,
    C3 = 3,
    C4 = 4,
    C5 = 5,
    C6 = 6,
    C7 = 7,
    C8 = 8,
    C9 = 9,
    C10 = 10,
    C11 = 11,
    C12 = 12,
    C13 = 13,
    C14 = 14,
    C15 = 15,
    C16 = 16,
    C17 = 17,
    C18 = 18,
    C19 = 19,
    C20 = 20,
    C21 = 21,
    C22 = 22,
    C23 = 23,
    C24 = 24,
    C25 = 25,
    C26 = 26,
    C27 = 27,
    C28 = 28,
    C29 = 29,
    C30 = 30,
    Unknown (u8),
}
pub type TstTagSpec = TstTag ;
pub type TstTagInner = Sum < u8, u8 > ;
impl DeepView for TstTag {
    type V = Self ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        * self
    }
}
impl TstTag {
    pub proof fn lemma_deep_view (& self) ensures self.deep_view() == * self,
    {
        reveal(< TstTag as DeepView>::deep_view) ;
    }
    pub open spec fn structural_valid (input: TstTagInner) -> bool {
        match input {
            L (x) => x == 0 || x == 1 || x == 2 || x == 3 || x == 4 || x == 5 || x == 6 || x == 7 || x == 8 || x == 9 || x == 10 || x == 11 || x == 12 || x == 13 || x == 14 || x == 15 || x == 16 || x == 17 || x == 18 || x == 19 || x == 20 || x == 21 || x == 22 || x == 23 || x == 24 || x == 25 || x == 26 || x == 27 || x == 28 || x == 29 || x == 30,
            R (x) => true,
        }
    }
    # [verifier::opaque] pub open spec fn from_structural (input: TstTagInner) -> Self {
        match input {
            L (x) => match x {
                0 => Self::C0,
                1 => Self::C1,
                2 => Self::C2,
                3 => Self::C3,
                4 => Self::C4,
                5 => Self::C5,
                6 => Self::C6,
                7 => Self::C7,
                8 => Self::C8,
                9 => Self::C9,
                10 => Self::C10,
                11 => Self::C11,
                12 => Self::C12,
                13 => Self::C13,
                14 => Self::C14,
                15 => Self::C15,
                16 => Self::C16,
                17 => Self::C17,
                18 => Self::C18,
                19 => Self::C19,
                20 => Self::C20,
                21 => Self::C21,
                22 => Self::C22,
                23 => Self::C23,
                24 => Self::C24,
                25 => Self::C25,
                26 => Self::C26,
                27 => Self::C27,
                28 => Self::C28,
                29 => Self::C29,
                30 => Self::C30,
                _ => arbitrary(),
            }
           ,
            R (x) => Self::Unknown (x),
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> TstTagInner {
        match self {
            Self::C0 => L (0),
            Self::C1 => L (1),
            Self::C2 => L (2),
            Self::C3 => L (3),
            Self::C4 => L (4),
            Self::C5 => L (5),
            Self::C6 => L (6),
            Self::C7 => L (7),
            Self::C8 => L (8),
            Self::C9 => L (9),
            Self::C10 => L (10),
            Self::C11 => L (11),
            Self::C12 => L (12),
            Self::C13 => L (13),
            Self::C14 => L (14),
            Self::C15 => L (15),
            Self::C16 => L (16),
            Self::C17 => L (17),
            Self::C18 => L (18),
            Self::C19 => L (19),
            Self::C20 => L (20),
            Self::C21 => L (21),
            Self::C22 => L (22),
            Self::C23 => L (23),
            Self::C24 => L (24),
            Self::C25 => L (25),
            Self::C26 => L (26),
            Self::C27 => L (27),
            Self::C28 => L (28),
            Self::C29 => L (29),
            Self::C30 => L (30),
            Self::Unknown (x) => R (x),
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TstTag::from_structural) ;
        reveal(TstTag::into_structural) ;
        match self {
            Self::C0 => {
            }
           ,
            Self::C1 => {
            }
           ,
            Self::C2 => {
            }
           ,
            Self::C3 => {
            }
           ,
            Self::C4 => {
            }
           ,
            Self::C5 => {
            }
           ,
            Self::C6 => {
            }
           ,
            Self::C7 => {
            }
           ,
            Self::C8 => {
            }
           ,
            Self::C9 => {
            }
           ,
            Self::C10 => {
            }
           ,
            Self::C11 => {
            }
           ,
            Self::C12 => {
            }
           ,
            Self::C13 => {
            }
           ,
            Self::C14 => {
            }
           ,
            Self::C15 => {
            }
           ,
            Self::C16 => {
            }
           ,
            Self::C17 => {
            }
           ,
            Self::C18 => {
            }
           ,
            Self::C19 => {
            }
           ,
            Self::C20 => {
            }
           ,
            Self::C21 => {
            }
           ,
            Self::C22 => {
            }
           ,
            Self::C23 => {
            }
           ,
            Self::C24 => {
            }
           ,
            Self::C25 => {
            }
           ,
            Self::C26 => {
            }
           ,
            Self::C27 => {
            }
           ,
            Self::C28 => {
            }
           ,
            Self::C29 => {
            }
           ,
            Self::C30 => {
            }
           ,
            Self::Unknown (_) => {
            }
           ,
        }
    }
    pub broadcast proof fn lemma_into_from (input: TstTagInner) requires Self::structural_valid (input),
    ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TstTag::from_structural) ;
        reveal(TstTag::into_structural) ;
        match input {
            L (x) => match x {
                0 => {
                }
               ,
                1 => {
                }
               ,
                2 => {
                }
               ,
                3 => {
                }
               ,
                4 => {
                }
               ,
                5 => {
                }
               ,
                6 => {
                }
               ,
                7 => {
                }
               ,
                8 => {
                }
               ,
                9 => {
                }
               ,
                10 => {
                }
               ,
                11 => {
                }
               ,
                12 => {
                }
               ,
                13 => {
                }
               ,
                14 => {
                }
               ,
                15 => {
                }
               ,
                16 => {
                }
               ,
                17 => {
                }
               ,
                18 => {
                }
               ,
                19 => {
                }
               ,
                20 => {
                }
               ,
                21 => {
                }
               ,
                22 => {
                }
               ,
                23 => {
                }
               ,
                24 => {
                }
               ,
                25 => {
                }
               ,
                26 => {
                }
               ,
                27 => {
                }
               ,
                28 => {
                }
               ,
                29 => {
                }
               ,
                30 => {
                }
               ,
                _ => {
                    assert (false) ;
                }
            }
           ,
            R (_) => {
            }
           ,
        }
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TstTagForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TstTagReverse ;
impl SpecMap for TstTagForward {
    type Input = TstTagInner ;
    type Output = TstTagSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TstTag::from_structural (input)
    }
}
impl SpecMap for TstTagReverse {
    type Input = TstTagSpec ;
    type Output = TstTagInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}
# [cfg (not (verus_keep_ghost))] unsafe impl Structural for TstTag {
}

# [doc = "data type for `mydata`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Mydata<'i> {
    pub foo: &'i [u8],
    pub bar: &'i [u8],
}
# [verifier::ext_equal]
pub struct MydataSpec < T0 = Seq < u8 >, T1 = Seq < u8 > > {
    pub foo: T0,
    pub bar: T1,
}
pub type MydataInner = (Seq < u8 >, Seq < u8 >) ;
impl<'i> DeepView for Mydata<'i> {
    type V = MydataSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        MydataSpec {
            foo: self.foo.deep_view(),
            bar: self.bar.deep_view(),
        }
    }
}
impl<'i> Mydata<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().foo == self.foo.deep_view(),
    self.deep_view().bar == self.bar.deep_view(),
    {
        reveal(< Mydata as DeepView>::deep_view) ;
    }
}
impl < T0, T1 > MydataSpec < T0, T1 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    T1)) -> Self {
        let (foo,
        bar) = input ;
        Self {
            foo,
            bar
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    T1) {
        let Self {
            foo,
            bar
        }
        = self ;
        (foo,
        bar)
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(MydataSpec::from_structural) ;
        reveal(MydataSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    T1)) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(MydataSpec::from_structural) ;
        reveal(MydataSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            foo,
            bar
        }
        => (foo,
        bar),
    }
   ,
    {
        reveal(MydataSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MydataForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct MydataReverse ;
impl SpecMap for MydataForward {
    type Input = MydataInner ;
    type Output = MydataSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        MydataSpec::from_structural (input)
    }
}
impl SpecMap for MydataReverse {
    type Input = MydataSpec ;
    type Output = MydataInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `tst`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Tst<'i> {
    pub tag: TstTag,
    pub mydata: TstMydata<'i>,
}
# [verifier::ext_equal]
pub struct TstSpec < T0 = TstTagSpec, T1 = TstMydataSpec > {
    pub tag: T0,
    pub mydata: T1,
}
pub type TstInner = (TstTagSpec, TstMydataSpec) ;
impl<'i> DeepView for Tst<'i> {
    type V = TstSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        TstSpec {
            tag: self.tag.deep_view(),
            mydata: self.mydata.deep_view(),
        }
    }
}
impl<'i> Tst<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().tag == self.tag.deep_view(),
    self.deep_view().mydata == self.mydata.deep_view(),
    {
        reveal(< Tst as DeepView>::deep_view) ;
    }
}
impl < T0, T1 > TstSpec < T0, T1 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    T1)) -> Self {
        let (tag,
        mydata) = input ;
        Self {
            tag,
            mydata
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    T1) {
        let Self {
            tag,
            mydata
        }
        = self ;
        (tag,
        mydata)
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TstSpec::from_structural) ;
        reveal(TstSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    T1)) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TstSpec::from_structural) ;
        reveal(TstSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            tag,
            mydata
        }
        => (tag,
        mydata),
    }
   ,
    {
        reveal(TstSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TstForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TstReverse ;
impl SpecMap for TstForward {
    type Input = TstInner ;
    type Output = TstSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TstSpec::from_structural (input)
    }
}
impl SpecMap for TstReverse {
    type Input = TstSpec ;
    type Output = TstInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `pair_stress`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct PairStress {
    pub f1: u8,
    pub f2: u16,
    pub f3: u32,
    pub f4: u8,
    pub f5: u8,
    pub f6: u8,
    pub f7: u8,
    pub f8: u8,
    pub f9: u8,
    pub f10: u8,
    pub f11: u8,
    pub f12: u8,
    pub f13: u8,
    pub f14: u8,
    pub f15: u8,
    pub f16: u8,
    pub f17: u8,
    pub f18: u8,
}
# [verifier::ext_equal]
pub struct PairStressSpec < T0 = u8, T1 = u16, T2 = u32, T3 = u8, T4 = u8, T5 = u8, T6 = u8, T7 = u8, T8 = u8, T9 = u8, T10 = u8, T11 = u8, T12 = u8, T13 = u8, T14 = u8, T15 = u8, T16 = u8, T17 = u8 > {
    pub f1: T0,
    pub f2: T1,
    pub f3: T2,
    pub f4: T3,
    pub f5: T4,
    pub f6: T5,
    pub f7: T6,
    pub f8: T7,
    pub f9: T8,
    pub f10: T9,
    pub f11: T10,
    pub f12: T11,
    pub f13: T12,
    pub f14: T13,
    pub f15: T14,
    pub f16: T15,
    pub f17: T16,
    pub f18: T17,
}
pub type PairStressInner = (u8, (u16, (u32, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8))))))))))))))))) ;
impl DeepView for PairStress {
    type V = PairStressSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        PairStressSpec {
            f1: self.f1.deep_view(),
            f2: self.f2.deep_view(),
            f3: self.f3.deep_view(),
            f4: self.f4.deep_view(),
            f5: self.f5.deep_view(),
            f6: self.f6.deep_view(),
            f7: self.f7.deep_view(),
            f8: self.f8.deep_view(),
            f9: self.f9.deep_view(),
            f10: self.f10.deep_view(),
            f11: self.f11.deep_view(),
            f12: self.f12.deep_view(),
            f13: self.f13.deep_view(),
            f14: self.f14.deep_view(),
            f15: self.f15.deep_view(),
            f16: self.f16.deep_view(),
            f17: self.f17.deep_view(),
            f18: self.f18.deep_view(),
        }
    }
}
impl PairStress {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().f1 == self.f1.deep_view(),
    self.deep_view().f2 == self.f2.deep_view(),
    self.deep_view().f3 == self.f3.deep_view(),
    self.deep_view().f4 == self.f4.deep_view(),
    self.deep_view().f5 == self.f5.deep_view(),
    self.deep_view().f6 == self.f6.deep_view(),
    self.deep_view().f7 == self.f7.deep_view(),
    self.deep_view().f8 == self.f8.deep_view(),
    self.deep_view().f9 == self.f9.deep_view(),
    self.deep_view().f10 == self.f10.deep_view(),
    self.deep_view().f11 == self.f11.deep_view(),
    self.deep_view().f12 == self.f12.deep_view(),
    self.deep_view().f13 == self.f13.deep_view(),
    self.deep_view().f14 == self.f14.deep_view(),
    self.deep_view().f15 == self.f15.deep_view(),
    self.deep_view().f16 == self.f16.deep_view(),
    self.deep_view().f17 == self.f17.deep_view(),
    self.deep_view().f18 == self.f18.deep_view(),
    {
        reveal(< PairStress as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17 > PairStressSpec < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17 > {
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
    (T15,
    (T16,
    T17)))))))))))))))))) -> Self {
        let (f1,
        (f2,
        (f3,
        (f4,
        (f5,
        (f6,
        (f7,
        (f8,
        (f9,
        (f10,
        (f11,
        (f12,
        (f13,
        (f14,
        (f15,
        (f16,
        (f17,
        f18))))))))))))))))) = input ;
        Self {
            f1,
            f2,
            f3,
            f4,
            f5,
            f6,
            f7,
            f8,
            f9,
            f10,
            f11,
            f12,
            f13,
            f14,
            f15,
            f16,
            f17,
            f18
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
    (T15,
    (T16,
    T17))))))))))))))))) {
        let Self {
            f1,
            f2,
            f3,
            f4,
            f5,
            f6,
            f7,
            f8,
            f9,
            f10,
            f11,
            f12,
            f13,
            f14,
            f15,
            f16,
            f17,
            f18
        }
        = self ;
        (f1,
        (f2,
        (f3,
        (f4,
        (f5,
        (f6,
        (f7,
        (f8,
        (f9,
        (f10,
        (f11,
        (f12,
        (f13,
        (f14,
        (f15,
        (f16,
        (f17,
        f18)))))))))))))))))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(PairStressSpec::from_structural) ;
        reveal(PairStressSpec::into_structural) ;
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
    (T15,
    (T16,
    T17)))))))))))))))))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(PairStressSpec::from_structural) ;
        reveal(PairStressSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            f1,
            f2,
            f3,
            f4,
            f5,
            f6,
            f7,
            f8,
            f9,
            f10,
            f11,
            f12,
            f13,
            f14,
            f15,
            f16,
            f17,
            f18
        }
        => (f1,
        (f2,
        (f3,
        (f4,
        (f5,
        (f6,
        (f7,
        (f8,
        (f9,
        (f10,
        (f11,
        (f12,
        (f13,
        (f14,
        (f15,
        (f16,
        (f17,
        f18))))))))))))))))),
    }
   ,
    {
        reveal(PairStressSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct PairStressForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct PairStressReverse ;
impl SpecMap for PairStressForward {
    type Input = PairStressInner ;
    type Output = PairStressSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        PairStressSpec::from_structural (input)
    }
}
impl SpecMap for PairStressReverse {
    type Input = PairStressSpec ;
    type Output = PairStressInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `tst_mydata`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum TstMydata<'i> {
    C0 (Mydata<'i>),
    C1 (Mydata<'i>),
    C2 (Mydata<'i>),
    C3 (Mydata<'i>),
    C4 (Mydata<'i>),
    C5 (Mydata<'i>),
    C6 (Mydata<'i>),
    C7 (Mydata<'i>),
    C8 (Mydata<'i>),
    C9 (Mydata<'i>),
    C10 (Mydata<'i>),
    C11 (Mydata<'i>),
    C12 (Mydata<'i>),
    C13 (Mydata<'i>),
    C14 (Mydata<'i>),
    C15 (Mydata<'i>),
    C16 (Mydata<'i>),
    C17 (Mydata<'i>),
    C18 (Mydata<'i>),
    C19 (Mydata<'i>),
    C20 (Mydata<'i>),
    C21 (Mydata<'i>),
    C22 (Mydata<'i>),
    C23 (Mydata<'i>),
    C24 (Mydata<'i>),
    C25 (Mydata<'i>),
    C26 (Mydata<'i>),
    C27 (Mydata<'i>),
    C28 (Mydata<'i>),
    C29 (Mydata<'i>),
    C30 (Mydata<'i>),
    Default (&'i [u8]),
}
# [verifier::ext_equal]
pub enum TstMydataSpec < T0 = MydataSpec, T1 = MydataSpec, T2 = MydataSpec, T3 = MydataSpec, T4 = MydataSpec, T5 = MydataSpec, T6 = MydataSpec, T7 = MydataSpec, T8 = MydataSpec, T9 = MydataSpec, T10 = MydataSpec, T11 = MydataSpec, T12 = MydataSpec, T13 = MydataSpec, T14 = MydataSpec, T15 = MydataSpec, T16 = MydataSpec, T17 = MydataSpec, T18 = MydataSpec, T19 = MydataSpec, T20 = MydataSpec, T21 = MydataSpec, T22 = MydataSpec, T23 = MydataSpec, T24 = MydataSpec, T25 = MydataSpec, T26 = MydataSpec, T27 = MydataSpec, T28 = MydataSpec, T29 = MydataSpec, T30 = MydataSpec, T31 = Seq < u8 > > {
    C0 (T0),
    C1 (T1),
    C2 (T2),
    C3 (T3),
    C4 (T4),
    C5 (T5),
    C6 (T6),
    C7 (T7),
    C8 (T8),
    C9 (T9),
    C10 (T10),
    C11 (T11),
    C12 (T12),
    C13 (T13),
    C14 (T14),
    C15 (T15),
    C16 (T16),
    C17 (T17),
    C18 (T18),
    C19 (T19),
    C20 (T20),
    C21 (T21),
    C22 (T22),
    C23 (T23),
    C24 (T24),
    C25 (T25),
    C26 (T26),
    C27 (T27),
    C28 (T28),
    C29 (T29),
    C30 (T30),
    Default (T31),
}
pub type TstMydataInner = Sum < Sum < Sum < Sum < Sum < MydataSpec, MydataSpec >, Sum < MydataSpec, MydataSpec > >, Sum < Sum < MydataSpec, MydataSpec >, Sum < MydataSpec, MydataSpec > > >, Sum < Sum < Sum < MydataSpec, MydataSpec >, Sum < MydataSpec, MydataSpec > >, Sum < Sum < MydataSpec, MydataSpec >, Sum < MydataSpec, MydataSpec > > > >, Sum < Sum < Sum < Sum < MydataSpec, MydataSpec >, Sum < MydataSpec, MydataSpec > >, Sum < Sum < MydataSpec, MydataSpec >, Sum < MydataSpec, MydataSpec > > >, Sum < Sum < Sum < MydataSpec, MydataSpec >, Sum < MydataSpec, MydataSpec > >, Sum < Sum < MydataSpec, MydataSpec >, Sum < MydataSpec, Seq < u8 > > > > > > ;
impl<'i> DeepView for TstMydata<'i> {
    type V = TstMydataSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        match self {
            TstMydata::C0 (v) => TstMydataSpec::C0 (v.deep_view()),
            TstMydata::C1 (v) => TstMydataSpec::C1 (v.deep_view()),
            TstMydata::C2 (v) => TstMydataSpec::C2 (v.deep_view()),
            TstMydata::C3 (v) => TstMydataSpec::C3 (v.deep_view()),
            TstMydata::C4 (v) => TstMydataSpec::C4 (v.deep_view()),
            TstMydata::C5 (v) => TstMydataSpec::C5 (v.deep_view()),
            TstMydata::C6 (v) => TstMydataSpec::C6 (v.deep_view()),
            TstMydata::C7 (v) => TstMydataSpec::C7 (v.deep_view()),
            TstMydata::C8 (v) => TstMydataSpec::C8 (v.deep_view()),
            TstMydata::C9 (v) => TstMydataSpec::C9 (v.deep_view()),
            TstMydata::C10 (v) => TstMydataSpec::C10 (v.deep_view()),
            TstMydata::C11 (v) => TstMydataSpec::C11 (v.deep_view()),
            TstMydata::C12 (v) => TstMydataSpec::C12 (v.deep_view()),
            TstMydata::C13 (v) => TstMydataSpec::C13 (v.deep_view()),
            TstMydata::C14 (v) => TstMydataSpec::C14 (v.deep_view()),
            TstMydata::C15 (v) => TstMydataSpec::C15 (v.deep_view()),
            TstMydata::C16 (v) => TstMydataSpec::C16 (v.deep_view()),
            TstMydata::C17 (v) => TstMydataSpec::C17 (v.deep_view()),
            TstMydata::C18 (v) => TstMydataSpec::C18 (v.deep_view()),
            TstMydata::C19 (v) => TstMydataSpec::C19 (v.deep_view()),
            TstMydata::C20 (v) => TstMydataSpec::C20 (v.deep_view()),
            TstMydata::C21 (v) => TstMydataSpec::C21 (v.deep_view()),
            TstMydata::C22 (v) => TstMydataSpec::C22 (v.deep_view()),
            TstMydata::C23 (v) => TstMydataSpec::C23 (v.deep_view()),
            TstMydata::C24 (v) => TstMydataSpec::C24 (v.deep_view()),
            TstMydata::C25 (v) => TstMydataSpec::C25 (v.deep_view()),
            TstMydata::C26 (v) => TstMydataSpec::C26 (v.deep_view()),
            TstMydata::C27 (v) => TstMydataSpec::C27 (v.deep_view()),
            TstMydata::C28 (v) => TstMydataSpec::C28 (v.deep_view()),
            TstMydata::C29 (v) => TstMydataSpec::C29 (v.deep_view()),
            TstMydata::C30 (v) => TstMydataSpec::C30 (v.deep_view()),
            TstMydata::Default (v) => TstMydataSpec::Default (v.deep_view()),
        }
    }
}
impl<'i> TstMydata<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view() == match self {
        TstMydata::C0 (v) => TstMydataSpec::C0 (v.deep_view()),
        TstMydata::C1 (v) => TstMydataSpec::C1 (v.deep_view()),
        TstMydata::C2 (v) => TstMydataSpec::C2 (v.deep_view()),
        TstMydata::C3 (v) => TstMydataSpec::C3 (v.deep_view()),
        TstMydata::C4 (v) => TstMydataSpec::C4 (v.deep_view()),
        TstMydata::C5 (v) => TstMydataSpec::C5 (v.deep_view()),
        TstMydata::C6 (v) => TstMydataSpec::C6 (v.deep_view()),
        TstMydata::C7 (v) => TstMydataSpec::C7 (v.deep_view()),
        TstMydata::C8 (v) => TstMydataSpec::C8 (v.deep_view()),
        TstMydata::C9 (v) => TstMydataSpec::C9 (v.deep_view()),
        TstMydata::C10 (v) => TstMydataSpec::C10 (v.deep_view()),
        TstMydata::C11 (v) => TstMydataSpec::C11 (v.deep_view()),
        TstMydata::C12 (v) => TstMydataSpec::C12 (v.deep_view()),
        TstMydata::C13 (v) => TstMydataSpec::C13 (v.deep_view()),
        TstMydata::C14 (v) => TstMydataSpec::C14 (v.deep_view()),
        TstMydata::C15 (v) => TstMydataSpec::C15 (v.deep_view()),
        TstMydata::C16 (v) => TstMydataSpec::C16 (v.deep_view()),
        TstMydata::C17 (v) => TstMydataSpec::C17 (v.deep_view()),
        TstMydata::C18 (v) => TstMydataSpec::C18 (v.deep_view()),
        TstMydata::C19 (v) => TstMydataSpec::C19 (v.deep_view()),
        TstMydata::C20 (v) => TstMydataSpec::C20 (v.deep_view()),
        TstMydata::C21 (v) => TstMydataSpec::C21 (v.deep_view()),
        TstMydata::C22 (v) => TstMydataSpec::C22 (v.deep_view()),
        TstMydata::C23 (v) => TstMydataSpec::C23 (v.deep_view()),
        TstMydata::C24 (v) => TstMydataSpec::C24 (v.deep_view()),
        TstMydata::C25 (v) => TstMydataSpec::C25 (v.deep_view()),
        TstMydata::C26 (v) => TstMydataSpec::C26 (v.deep_view()),
        TstMydata::C27 (v) => TstMydataSpec::C27 (v.deep_view()),
        TstMydata::C28 (v) => TstMydataSpec::C28 (v.deep_view()),
        TstMydata::C29 (v) => TstMydataSpec::C29 (v.deep_view()),
        TstMydata::C30 (v) => TstMydataSpec::C30 (v.deep_view()),
        TstMydata::Default (v) => TstMydataSpec::Default (v.deep_view()),
    }
   ,
    {
        reveal(< TstMydata as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30, T31 > TstMydataSpec < T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30, T31 > {
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
            L (L (L (L (L (value))))) => Self::C0 (value),
            L (L (L (L (R (value))))) => Self::C1 (value),
            L (L (L (R (L (value))))) => Self::C2 (value),
            L (L (L (R (R (value))))) => Self::C3 (value),
            L (L (R (L (L (value))))) => Self::C4 (value),
            L (L (R (L (R (value))))) => Self::C5 (value),
            L (L (R (R (L (value))))) => Self::C6 (value),
            L (L (R (R (R (value))))) => Self::C7 (value),
            L (R (L (L (L (value))))) => Self::C8 (value),
            L (R (L (L (R (value))))) => Self::C9 (value),
            L (R (L (R (L (value))))) => Self::C10 (value),
            L (R (L (R (R (value))))) => Self::C11 (value),
            L (R (R (L (L (value))))) => Self::C12 (value),
            L (R (R (L (R (value))))) => Self::C13 (value),
            L (R (R (R (L (value))))) => Self::C14 (value),
            L (R (R (R (R (value))))) => Self::C15 (value),
            R (L (L (L (L (value))))) => Self::C16 (value),
            R (L (L (L (R (value))))) => Self::C17 (value),
            R (L (L (R (L (value))))) => Self::C18 (value),
            R (L (L (R (R (value))))) => Self::C19 (value),
            R (L (R (L (L (value))))) => Self::C20 (value),
            R (L (R (L (R (value))))) => Self::C21 (value),
            R (L (R (R (L (value))))) => Self::C22 (value),
            R (L (R (R (R (value))))) => Self::C23 (value),
            R (R (L (L (L (value))))) => Self::C24 (value),
            R (R (L (L (R (value))))) => Self::C25 (value),
            R (R (L (R (L (value))))) => Self::C26 (value),
            R (R (L (R (R (value))))) => Self::C27 (value),
            R (R (R (L (L (value))))) => Self::C28 (value),
            R (R (R (L (R (value))))) => Self::C29 (value),
            R (R (R (R (L (value))))) => Self::C30 (value),
            R (R (R (R (R (value))))) => Self::Default (value),
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
            Self::C0 (value) => L (L (L (L (L (value))))),
            Self::C1 (value) => L (L (L (L (R (value))))),
            Self::C2 (value) => L (L (L (R (L (value))))),
            Self::C3 (value) => L (L (L (R (R (value))))),
            Self::C4 (value) => L (L (R (L (L (value))))),
            Self::C5 (value) => L (L (R (L (R (value))))),
            Self::C6 (value) => L (L (R (R (L (value))))),
            Self::C7 (value) => L (L (R (R (R (value))))),
            Self::C8 (value) => L (R (L (L (L (value))))),
            Self::C9 (value) => L (R (L (L (R (value))))),
            Self::C10 (value) => L (R (L (R (L (value))))),
            Self::C11 (value) => L (R (L (R (R (value))))),
            Self::C12 (value) => L (R (R (L (L (value))))),
            Self::C13 (value) => L (R (R (L (R (value))))),
            Self::C14 (value) => L (R (R (R (L (value))))),
            Self::C15 (value) => L (R (R (R (R (value))))),
            Self::C16 (value) => R (L (L (L (L (value))))),
            Self::C17 (value) => R (L (L (L (R (value))))),
            Self::C18 (value) => R (L (L (R (L (value))))),
            Self::C19 (value) => R (L (L (R (R (value))))),
            Self::C20 (value) => R (L (R (L (L (value))))),
            Self::C21 (value) => R (L (R (L (R (value))))),
            Self::C22 (value) => R (L (R (R (L (value))))),
            Self::C23 (value) => R (L (R (R (R (value))))),
            Self::C24 (value) => R (R (L (L (L (value))))),
            Self::C25 (value) => R (R (L (L (R (value))))),
            Self::C26 (value) => R (R (L (R (L (value))))),
            Self::C27 (value) => R (R (L (R (R (value))))),
            Self::C28 (value) => R (R (R (L (L (value))))),
            Self::C29 (value) => R (R (R (L (R (value))))),
            Self::C30 (value) => R (R (R (R (L (value))))),
            Self::Default (value) => R (R (R (R (R (value))))),
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TstMydataSpec::from_structural) ;
        reveal(TstMydataSpec::into_structural) ;
        match self {
            Self::C0 (_) => {
            }
           ,
            Self::C1 (_) => {
            }
           ,
            Self::C2 (_) => {
            }
           ,
            Self::C3 (_) => {
            }
           ,
            Self::C4 (_) => {
            }
           ,
            Self::C5 (_) => {
            }
           ,
            Self::C6 (_) => {
            }
           ,
            Self::C7 (_) => {
            }
           ,
            Self::C8 (_) => {
            }
           ,
            Self::C9 (_) => {
            }
           ,
            Self::C10 (_) => {
            }
           ,
            Self::C11 (_) => {
            }
           ,
            Self::C12 (_) => {
            }
           ,
            Self::C13 (_) => {
            }
           ,
            Self::C14 (_) => {
            }
           ,
            Self::C15 (_) => {
            }
           ,
            Self::C16 (_) => {
            }
           ,
            Self::C17 (_) => {
            }
           ,
            Self::C18 (_) => {
            }
           ,
            Self::C19 (_) => {
            }
           ,
            Self::C20 (_) => {
            }
           ,
            Self::C21 (_) => {
            }
           ,
            Self::C22 (_) => {
            }
           ,
            Self::C23 (_) => {
            }
           ,
            Self::C24 (_) => {
            }
           ,
            Self::C25 (_) => {
            }
           ,
            Self::C26 (_) => {
            }
           ,
            Self::C27 (_) => {
            }
           ,
            Self::C28 (_) => {
            }
           ,
            Self::C29 (_) => {
            }
           ,
            Self::C30 (_) => {
            }
           ,
            Self::Default (_) => {
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
        reveal(TstMydataSpec::from_structural) ;
        reveal(TstMydataSpec::into_structural) ;
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
        Self::C0 (value) => L (L (L (L (L (value))))),
        Self::C1 (value) => L (L (L (L (R (value))))),
        Self::C2 (value) => L (L (L (R (L (value))))),
        Self::C3 (value) => L (L (L (R (R (value))))),
        Self::C4 (value) => L (L (R (L (L (value))))),
        Self::C5 (value) => L (L (R (L (R (value))))),
        Self::C6 (value) => L (L (R (R (L (value))))),
        Self::C7 (value) => L (L (R (R (R (value))))),
        Self::C8 (value) => L (R (L (L (L (value))))),
        Self::C9 (value) => L (R (L (L (R (value))))),
        Self::C10 (value) => L (R (L (R (L (value))))),
        Self::C11 (value) => L (R (L (R (R (value))))),
        Self::C12 (value) => L (R (R (L (L (value))))),
        Self::C13 (value) => L (R (R (L (R (value))))),
        Self::C14 (value) => L (R (R (R (L (value))))),
        Self::C15 (value) => L (R (R (R (R (value))))),
        Self::C16 (value) => R (L (L (L (L (value))))),
        Self::C17 (value) => R (L (L (L (R (value))))),
        Self::C18 (value) => R (L (L (R (L (value))))),
        Self::C19 (value) => R (L (L (R (R (value))))),
        Self::C20 (value) => R (L (R (L (L (value))))),
        Self::C21 (value) => R (L (R (L (R (value))))),
        Self::C22 (value) => R (L (R (R (L (value))))),
        Self::C23 (value) => R (L (R (R (R (value))))),
        Self::C24 (value) => R (R (L (L (L (value))))),
        Self::C25 (value) => R (R (L (L (R (value))))),
        Self::C26 (value) => R (R (L (R (L (value))))),
        Self::C27 (value) => R (R (L (R (R (value))))),
        Self::C28 (value) => R (R (R (L (L (value))))),
        Self::C29 (value) => R (R (R (L (R (value))))),
        Self::C30 (value) => R (R (R (R (L (value))))),
        Self::Default (value) => R (R (R (R (R (value))))),
    }
   ,
    {
        reveal(TstMydataSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TstMydataForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TstMydataReverse ;
impl SpecMap for TstMydataForward {
    type Input = TstMydataInner ;
    type Output = TstMydataSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TstMydataSpec::from_structural (input)
    }
}
impl SpecMap for TstMydataReverse {
    type Input = TstMydataSpec ;
    type Output = TstMydataInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `tst_tag`."]
# [derive (Clone, Copy)]
pub struct TstTagFmt ;

pub type TstTagFmtSpec = Named < Mapped < Choice < Refined < U8, PredFnSpec < u8 >>, Refined < U8, PredFnSpec < u8 >> >, BiMap < TstTagForward, TstTagReverse >> > ;

impl TstTagFmt {
    # [doc = "specification constructor for `tst_tag`."] pub open spec fn spec_inner() -> TstTagFmtSpec {
        Named ("tst_tag",
        Mapped {
            inner: Choice (Refined (U8,
            | x: u8 | ((((((((((((((((((((((((((((((x == 0) || (x == 1)) || (x == 2)) || (x == 3)) || (x == 4)) || (x == 5)) || (x == 6)) || (x == 7)) || (x == 8)) || (x == 9)) || (x == 10)) || (x == 11)) || (x == 12)) || (x == 13)) || (x == 14)) || (x == 15)) || (x == 16)) || (x == 17)) || (x == 18)) || (x == 19)) || (x == 20)) || (x == 21)) || (x == 22)) || (x == 23)) || (x == 24)) || (x == 25)) || (x == 26)) || (x == 27)) || (x == 28)) || (x == 29)) || (x == 30)),
            Refined (U8,
            | x: u8 | ((((((((((((((((((((((((((((((x != 0) && (x != 1)) && (x != 2)) && (x != 3)) && (x != 4)) && (x != 5)) && (x != 6)) && (x != 7)) && (x != 8)) && (x != 9)) && (x != 10)) && (x != 11)) && (x != 12)) && (x != 13)) && (x != 14)) && (x != 15)) && (x != 16)) && (x != 17)) && (x != 18)) && (x != 19)) && (x != 20)) && (x != 21)) && (x != 22)) && (x != 23)) && (x != 24)) && (x != 25)) && (x != 26)) && (x != 27)) && (x != 28)) && (x != 29)) && (x != 30))),
            mapper: BiMap (TstTagForward,
            TstTagReverse),
        }
        )
    }
}


# [doc = "named format combinator for `mydata`."]
# [derive (Clone, Copy)]
pub struct MydataFmt ;

pub type MydataFmtSpec = Named < Mapped < Pair < Fixed < 2 >, Fixed < 2 > >, BiMap < MydataForward, MydataReverse >> > ;

impl MydataFmt {
    # [doc = "specification constructor for `mydata`."] pub open spec fn spec_inner() -> MydataFmtSpec {
        Named ("mydata",
        Mapped {
            inner: Pair (Fixed::< 2 >,
            Fixed::< 2 >),
            mapper: BiMap (MydataForward,
            MydataReverse),
        }
        )
    }
}


# [doc = "named format combinator for `tst`."]
# [derive (Clone, Copy)]
pub struct TstFmt ;

pub type TstFmtSpec = Named < Mapped < Bind < TstTagFmt, spec_fn (TstTagSpec) -> TstMydataFmt >, BiMap < TstForward, TstReverse >> > ;

impl TstFmt {
    # [doc = "specification constructor for `tst`."] pub open spec fn spec_inner() -> TstFmtSpec {
        Named ("tst",
        Mapped {
            inner: Bind (TstTagFmt,
            | tag: TstTagSpec | TstMydataFmt::spec (tag)),
            mapper: BiMap (TstForward,
            TstReverse),
        }
        )
    }
}


# [doc = "named format combinator for `pair_stress`."]
# [derive (Clone, Copy)]
pub struct PairStressFmt ;

pub type PairStressFmtSpec = Named < Mapped < Pair < U8, Pair < U16Le, Pair < U32Le, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, Pair < U8, U8 > > > > > > > > > > > > > > > > >, BiMap < PairStressForward, PairStressReverse >> > ;

impl PairStressFmt {
    # [doc = "specification constructor for `pair_stress`."] pub open spec fn spec_inner() -> PairStressFmtSpec {
        Named ("pair_stress",
        Mapped {
            inner: Pair (U8,
            Pair (U16Le,
            Pair (U32Le,
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
            U8))))))))))))))))),
            mapper: BiMap (PairStressForward,
            PairStressReverse),
        }
        )
    }
}


# [doc = "named format combinator for `tst_mydata`."]
# [derive (Clone, Copy)]
pub struct TstMydataFmt {
    tag: TstTag,
}
impl TstMydataFmt {
    # [verifier::type_invariant] spec fn wf (& self) -> bool {
        TstTagFmt.consistent (self.tag.deep_view())
    }
    pub closed spec fn tag_spec (& self) -> TstTagSpec {
        self.tag.deep_view()
    }
    pub closed spec fn spec (tag: TstTag) -> Self {
        TstMydataFmt {
            tag
        }
    }
}

pub type TstMydataFmtSpec = Named < Mapped < Sum < Sum < Sum < Sum < Sum < MydataFmt, MydataFmt >, Sum < MydataFmt, MydataFmt > >, Sum < Sum < MydataFmt, MydataFmt >, Sum < MydataFmt, MydataFmt > > >, Sum < Sum < Sum < MydataFmt, MydataFmt >, Sum < MydataFmt, MydataFmt > >, Sum < Sum < MydataFmt, MydataFmt >, Sum < MydataFmt, MydataFmt > > > >, Sum < Sum < Sum < Sum < MydataFmt, MydataFmt >, Sum < MydataFmt, MydataFmt > >, Sum < Sum < MydataFmt, MydataFmt >, Sum < MydataFmt, MydataFmt > > >, Sum < Sum < Sum < MydataFmt, MydataFmt >, Sum < MydataFmt, MydataFmt > >, Sum < Sum < MydataFmt, MydataFmt >, Sum < MydataFmt, Tail > > > > >, BiMap < TstMydataForward, TstMydataReverse >> > ;

impl TstMydataFmt {
    # [doc = "specification constructor for `tst_mydata`."] pub open spec fn spec_inner (tag: TstTagSpec) -> TstMydataFmtSpec {
        Named ("tst_mydata",
        Mapped {
            inner: match tag {
                TstTagSpec::C0 => L (L (L (L (L (MydataFmt))))),
                TstTagSpec::C1 => L (L (L (L (R (MydataFmt))))),
                TstTagSpec::C2 => L (L (L (R (L (MydataFmt))))),
                TstTagSpec::C3 => L (L (L (R (R (MydataFmt))))),
                TstTagSpec::C4 => L (L (R (L (L (MydataFmt))))),
                TstTagSpec::C5 => L (L (R (L (R (MydataFmt))))),
                TstTagSpec::C6 => L (L (R (R (L (MydataFmt))))),
                TstTagSpec::C7 => L (L (R (R (R (MydataFmt))))),
                TstTagSpec::C8 => L (R (L (L (L (MydataFmt))))),
                TstTagSpec::C9 => L (R (L (L (R (MydataFmt))))),
                TstTagSpec::C10 => L (R (L (R (L (MydataFmt))))),
                TstTagSpec::C11 => L (R (L (R (R (MydataFmt))))),
                TstTagSpec::C12 => L (R (R (L (L (MydataFmt))))),
                TstTagSpec::C13 => L (R (R (L (R (MydataFmt))))),
                TstTagSpec::C14 => L (R (R (R (L (MydataFmt))))),
                TstTagSpec::C15 => L (R (R (R (R (MydataFmt))))),
                TstTagSpec::C16 => R (L (L (L (L (MydataFmt))))),
                TstTagSpec::C17 => R (L (L (L (R (MydataFmt))))),
                TstTagSpec::C18 => R (L (L (R (L (MydataFmt))))),
                TstTagSpec::C19 => R (L (L (R (R (MydataFmt))))),
                TstTagSpec::C20 => R (L (R (L (L (MydataFmt))))),
                TstTagSpec::C21 => R (L (R (L (R (MydataFmt))))),
                TstTagSpec::C22 => R (L (R (R (L (MydataFmt))))),
                TstTagSpec::C23 => R (L (R (R (R (MydataFmt))))),
                TstTagSpec::C24 => R (R (L (L (L (MydataFmt))))),
                TstTagSpec::C25 => R (R (L (L (R (MydataFmt))))),
                TstTagSpec::C26 => R (R (L (R (L (MydataFmt))))),
                TstTagSpec::C27 => R (R (L (R (R (MydataFmt))))),
                TstTagSpec::C28 => R (R (R (L (L (MydataFmt))))),
                TstTagSpec::C29 => R (R (R (L (R (MydataFmt))))),
                TstTagSpec::C30 => R (R (R (R (L (MydataFmt))))),
                _ => R (R (R (R (R (Tail))))),
            }
           ,
            mapper: BiMap (TstMydataForward,
            TstMydataReverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for TstTagFmt {
        type PVal = TstTagSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TstTagFmt {
        type Val = TstTagSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TstTagFmt {
        type SValue = TstTagSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TstTagFmt {
        type SVal = TstTagSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TstTagFmt {
        type T = TstTagSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for MydataFmt {
        type PVal = MydataSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for MydataFmt {
        type Val = MydataSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for MydataFmt {
        type SValue = MydataSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for MydataFmt {
        type SVal = MydataSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for MydataFmt {
        type T = MydataSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for TstFmt {
        type PVal = TstSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TstFmt {
        type Val = TstSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TstFmt {
        type SValue = TstSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TstFmt {
        type SVal = TstSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TstFmt {
        type T = TstSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for PairStressFmt {
        type PVal = PairStressSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for PairStressFmt {
        type Val = PairStressSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for PairStressFmt {
        type SValue = PairStressSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for PairStressFmt {
        type SVal = PairStressSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for PairStressFmt {
        type T = PairStressSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for TstMydataFmt {
        type PVal = TstMydataSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner (self.tag_spec()).spec_parse (ibuf)
        }
    }
    impl Consistency for TstMydataFmt {
        type Val = TstMydataSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner (self.tag_spec()).consistent (v)
        }
    }
    impl SpecSerializerDps for TstMydataFmt {
        type SValue = TstMydataSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner (self.tag_spec()).spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TstMydataFmt {
        type SVal = TstMydataSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner (self.tag_spec()).spec_serialize (v)
        }
    }
    impl SpecByteLen for TstMydataFmt {
        type T = TstMydataSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner (self.tag_spec()).byte_len (v)
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
        TstTag::lemma_from_into,
        TstTag::lemma_into_from,
        MydataSpec::lemma_from_into,
        MydataSpec::lemma_into_from,
        TstSpec::lemma_from_into,
        TstSpec::lemma_into_from,
        PairStressSpec::lemma_from_into,
        PairStressSpec::lemma_into_from,
        TstMydataSpec::lemma_from_into,
        TstMydataSpec::lemma_into_from,
    };

    impl SafeParser for TstTagFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TstTagFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TstTagFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TstTagFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TstTagFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TstTagFmt as SpecParser>::spec_parse) ;
            reveal(< TstTagFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TstTagInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                assert (TstTag::structural_valid (input)) ;
                TstTag::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TstTagFmt as SpecParser>::spec_parse) ;
            reveal(< TstTagFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TstTagInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                assert (TstTag::structural_valid (input)) ;
                TstTag::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for TstTagFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TstTagFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TstTagFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TstTagFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for TstTagFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TstTagFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TstTagFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TstTagFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TstTagFmt as SpecParser>::spec_parse) ;
            reveal(< TstTagFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TstTagFmt as Consistency>::consistent) ;
            reveal(< TstTagFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: TstTagSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TstTag::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TstTagFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TstTagFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TstTagInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                assert (TstTag::structural_valid (input)) ;
                TstTag::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for TstTagFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< TstTagFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TstTagFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for TstTagFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TstTagFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TstTagFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for MydataFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< MydataFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for MydataFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< MydataFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for MydataFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< MydataFmt as SpecParser>::spec_parse) ;
            reveal(< MydataFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: MydataInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                MydataSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< MydataFmt as SpecParser>::spec_parse) ;
            reveal(< MydataFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: MydataInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                MydataSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for MydataFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< MydataFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< MydataFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< MydataFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for MydataFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< MydataFmt as SpecSerializer>::spec_serialize) ;
            reveal(< MydataFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for MydataFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< MydataFmt as SpecParser>::spec_parse) ;
            reveal(< MydataFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< MydataFmt as Consistency>::consistent) ;
            reveal(< MydataFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: MydataSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                MydataSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for MydataFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< MydataFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: MydataInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                MydataSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for MydataFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< MydataFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< MydataFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for MydataFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< MydataFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< MydataFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for TstFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TstFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TstFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TstFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TstFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TstFmt as SpecParser>::spec_parse) ;
            reveal(< TstFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TstInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TstSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TstFmt as SpecParser>::spec_parse) ;
            reveal(< TstFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TstInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TstSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl GoodSerializer for TstFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TstFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TstFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TstFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TstFmt as SpecParser>::spec_parse) ;
            reveal(< TstFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TstFmt as Consistency>::consistent) ;
            reveal(< TstFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: TstSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TstSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TstFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TstFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TstInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TstSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializers for TstFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TstFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TstFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for PairStressFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< PairStressFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for PairStressFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< PairStressFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for PairStressFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< PairStressFmt as SpecParser>::spec_parse) ;
            reveal(< PairStressFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: PairStressInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                PairStressSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< PairStressFmt as SpecParser>::spec_parse) ;
            reveal(< PairStressFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: PairStressInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                PairStressSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for PairStressFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< PairStressFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< PairStressFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< PairStressFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for PairStressFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< PairStressFmt as SpecSerializer>::spec_serialize) ;
            reveal(< PairStressFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for PairStressFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< PairStressFmt as SpecParser>::spec_parse) ;
            reveal(< PairStressFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< PairStressFmt as Consistency>::consistent) ;
            reveal(< PairStressFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: PairStressSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                PairStressSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for PairStressFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< PairStressFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: PairStressInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                PairStressSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for PairStressFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< PairStressFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< PairStressFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for PairStressFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< PairStressFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< PairStressFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for TstMydataFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TstMydataFmt as SpecParser>::spec_parse) ;
            Self::spec_inner (self.tag_spec()).lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TstMydataFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner (self.tag_spec()).productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TstMydataFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner (self.tag_spec()) ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TstMydataFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TstMydataFmt as SpecParser>::spec_parse) ;
            reveal(< TstMydataFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.tag_spec()) ;
            assert forall | input: TstMydataInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TstMydataSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TstMydataFmt as SpecParser>::spec_parse) ;
            reveal(< TstMydataFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner (self.tag_spec()) ;
            assert forall | input: TstMydataInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TstMydataSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl GoodSerializer for TstMydataFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TstMydataFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TstMydataFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.tag_spec()) ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TstMydataFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TstMydataFmt as SpecParser>::spec_parse) ;
            reveal(< TstMydataFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TstMydataFmt as Consistency>::consistent) ;
            reveal(< TstMydataFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.tag_spec()) ;
            assert forall | output: TstMydataSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TstMydataSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TstMydataFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TstMydataFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner (self.tag_spec()) ;
            assert forall | input: TstMydataInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TstMydataSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializers for TstMydataFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TstMydataFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TstMydataFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner (self.tag_spec()) ;
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

    impl<'i> Parser<&'i [u8]> for TstTagFmt {
        type PT = TstTag;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<TstTagFmt as SpecParser>::spec_parse);
            reveal(<TstTag as DeepView>::deep_view);
            reveal(TstTag::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                0 => TstTag::C0,
                1 => TstTag::C1,
                2 => TstTag::C2,
                3 => TstTag::C3,
                4 => TstTag::C4,
                5 => TstTag::C5,
                6 => TstTag::C6,
                7 => TstTag::C7,
                8 => TstTag::C8,
                9 => TstTag::C9,
                10 => TstTag::C10,
                11 => TstTag::C11,
                12 => TstTag::C12,
                13 => TstTag::C13,
                14 => TstTag::C14,
                15 => TstTag::C15,
                16 => TstTag::C16,
                17 => TstTag::C17,
                18 => TstTag::C18,
                19 => TstTag::C19,
                20 => TstTag::C20,
                21 => TstTag::C21,
                22 => TstTag::C22,
                23 => TstTag::C23,
                24 => TstTag::C24,
                25 => TstTag::C25,
                26 => TstTag::C26,
                27 => TstTag::C27,
                28 => TstTag::C28,
                29 => TstTag::C29,
                30 => TstTag::C30,
                x => TstTag::Unknown (x),
            };
            assert (self.spec_parse (ibuf @) == Some ((n as int, enum_val.deep_view()))) ;
            Ok((n, enum_val))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TstTag> for TstTagFmt {
        fn serialize_into(&self, v: &TstTag, obuf: &mut Output) {
            reveal(<TstTagFmt as SpecSerializer>::spec_serialize);
            reveal(<TstTagFmt as SpecByteLen>::byte_len);
            reveal(<TstTag as DeepView>::deep_view);
            reveal(TstTag::into_structural);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                TstTag::C0 => 0,
                TstTag::C1 => 1,
                TstTag::C2 => 2,
                TstTag::C3 => 3,
                TstTag::C4 => 4,
                TstTag::C5 => 5,
                TstTag::C6 => 6,
                TstTag::C7 => 7,
                TstTag::C8 => 8,
                TstTag::C9 => 9,
                TstTag::C10 => 10,
                TstTag::C11 => 11,
                TstTag::C12 => 12,
                TstTag::C13 => 13,
                TstTag::C14 => 14,
                TstTag::C15 => 15,
                TstTag::C16 => 16,
                TstTag::C17 => 17,
                TstTag::C18 => 18,
                TstTag::C19 => 19,
                TstTag::C20 => 20,
                TstTag::C21 => 21,
                TstTag::C22 => 22,
                TstTag::C23 => 23,
                TstTag::C24 => 24,
                TstTag::C25 => 25,
                TstTag::C26 => 26,
                TstTag::C27 => 27,
                TstTag::C28 => 28,
                TstTag::C29 => 29,
                TstTag::C30 => 30,
                TstTag::Unknown (x) => x,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TstTag> for TstTagFmt {
        fn prepare(&self, v: &TstTag) -> Result<usize, PreSerializeError> {
            reveal(<TstTagFmt as SpecByteLen>::byte_len);
            reveal(<TstTag as DeepView>::deep_view);
            reveal(TstTag::into_structural);
            let tag = match *v {
                TstTag::C0 => 0,
                TstTag::C1 => 1,
                TstTag::C2 => 2,
                TstTag::C3 => 3,
                TstTag::C4 => 4,
                TstTag::C5 => 5,
                TstTag::C6 => 6,
                TstTag::C7 => 7,
                TstTag::C8 => 8,
                TstTag::C9 => 9,
                TstTag::C10 => 10,
                TstTag::C11 => 11,
                TstTag::C12 => 12,
                TstTag::C13 => 13,
                TstTag::C14 => 14,
                TstTag::C15 => 15,
                TstTag::C16 => 16,
                TstTag::C17 => 17,
                TstTag::C18 => 18,
                TstTag::C19 => 19,
                TstTag::C20 => 20,
                TstTag::C21 => 21,
                TstTag::C22 => 22,
                TstTag::C23 => 23,
                TstTag::C24 => 24,
                TstTag::C25 => 25,
                TstTag::C26 => 26,
                TstTag::C27 => 27,
                TstTag::C28 => 28,
                TstTag::C29 => 29,
                TstTag::C30 => 30,
                TstTag::Unknown (x) if x != 0 && x != 1 && x != 2 && x != 3 && x != 4 && x != 5 && x != 6 && x != 7 && x != 8 && x != 9 && x != 10 && x != 11 && x != 12 && x != 13 && x != 14 && x != 15 && x != 16 && x != 17 && x != 18 && x != 19 && x != 20 && x != 21 && x != 22 && x != 23 && x != 24 && x != 25 && x != 26 && x != 27 && x != 28 && x != 29 && x != 30 => x, _ => return Err (PreSerializeError::not_compliant (ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }



    impl<'i> Parser<&'i [u8]> for MydataFmt {
        type PT = Mydata<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<MydataFmt as SpecParser>::spec_parse);
            reveal(<Mydata as DeepView>::deep_view);
            reveal(MydataSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, foo) = (Fixed::< 2 >).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, bar) = (Fixed::< 2 >).parse (& rest) ?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Mydata {
                foo,
                bar,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Mydata<'i>> for MydataFmt {
        fn serialize_into(&self, v: &Mydata<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<MydataFmt as SpecSerializer>::spec_serialize);
            reveal(<MydataFmt as SpecByteLen>::byte_len);
            reveal(<Mydata as DeepView>::deep_view);
            reveal(MydataSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Mydata {
                foo,
                bar,
            } = v;
            Fixed::< 2 >.serialize_into(* foo, obuf);
            Fixed::< 2 >.serialize_into(* bar, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Mydata<'i>> for MydataFmt {
        fn prepare(&self, v: &Mydata<'i>) -> Result<usize, PreSerializeError> {
            reveal(<MydataFmt as SpecByteLen>::byte_len);
            reveal(<Mydata as DeepView>::deep_view);
            reveal(MydataSpec::into_structural);
            let Mydata {
                foo,
                bar,
            } = v;
            let l1 = (Fixed::< 2 >).prepare (foo) ?;
            let l2 = (Fixed::< 2 >).prepare (bar) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for TstFmt {
        type PT = Tst<'i>;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TstFmt as SpecParser>::spec_parse);
            reveal(<Tst as DeepView>::deep_view);
            reveal(TstSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, tag) = (Named ("tst_tag", TstTagFmt)).parse (& rest) ?;
            proof {
                tag.lemma_deep_view();
            }
            let rest = rest.skip(n1);
            proof {
                tag.lemma_deep_view();
            }

            let (n2, mydata) = (Named ("tst_mydata", TstMydataFmt {
                tag: tag
            }
            )).parse (& rest) ?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = Tst {
                tag,
                mydata,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Tst<'i>> for TstFmt {
        fn serialize_into(&self, v: &Tst<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<TstFmt as SpecSerializer>::spec_serialize);
            reveal(<TstFmt as SpecByteLen>::byte_len);
            reveal(<Tst as DeepView>::deep_view);
            reveal(TstSpec::into_structural);
            let ghost old_obuf = obuf@;

            let Tst {
                tag,
                mydata,
            } = v;
            proof {
                tag.lemma_deep_view();
            }

            TstTagFmt.serialize_into(tag, obuf);
            TstMydataFmt {
                tag: *tag
            }
            .serialize_into(mydata, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Tst<'i>> for TstFmt {
        fn prepare(&self, v: &Tst<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TstFmt as SpecByteLen>::byte_len);
            reveal(<Tst as DeepView>::deep_view);
            reveal(TstSpec::into_structural);
            let Tst {
                tag,
                mydata,
            } = v;
            proof {
                tag.lemma_deep_view();
            }

            let l1 = (Named ("tst_tag", TstTagFmt)).prepare (tag) ?;
            let l2 = (Named ("tst_mydata", TstMydataFmt {
                tag: *tag
            }
            )).prepare (mydata) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for PairStressFmt {
        type PT = PairStress;

        #[verifier::spinoff_prover]
        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<PairStressFmt as SpecParser>::spec_parse);
            reveal(<PairStress as DeepView>::deep_view);
            reveal(PairStressSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, f1) = (U8).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, f2) = (U16Le).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, f3) = (U32Le).parse (& rest) ?;
            let rest = rest.skip(n3);
            let (n4, f4) = (U8).parse (& rest) ?;
            let rest = rest.skip(n4);
            let (n5, f5) = (U8).parse (& rest) ?;
            let rest = rest.skip(n5);
            let (n6, f6) = (U8).parse (& rest) ?;
            let rest = rest.skip(n6);
            let (n7, f7) = (U8).parse (& rest) ?;
            let rest = rest.skip(n7);
            let (n8, f8) = (U8).parse (& rest) ?;
            let rest = rest.skip(n8);
            let (n9, f9) = (U8).parse (& rest) ?;
            let rest = rest.skip(n9);
            let (n10, f10) = (U8).parse (& rest) ?;
            let rest = rest.skip(n10);
            let (n11, f11) = (U8).parse (& rest) ?;
            let rest = rest.skip(n11);
            let (n12, f12) = (U8).parse (& rest) ?;
            let rest = rest.skip(n12);
            let (n13, f13) = (U8).parse (& rest) ?;
            let rest = rest.skip(n13);
            let (n14, f14) = (U8).parse (& rest) ?;
            let rest = rest.skip(n14);
            let (n15, f15) = (U8).parse (& rest) ?;
            let rest = rest.skip(n15);
            let (n16, f16) = (U8).parse (& rest) ?;
            let rest = rest.skip(n16);
            let (n17, f17) = (U8).parse (& rest) ?;
            let rest = rest.skip(n17);
            let (n18, f18) = (U8).parse (& rest) ?;
            let rest = rest.skip(n18);
            let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n10 + n11 + n12 + n13 + n14 + n15 + n16 + n17 + n18;
            let final_v = PairStress {
                f1,
                f2,
                f3,
                f4,
                f5,
                f6,
                f7,
                f8,
                f9,
                f10,
                f11,
                f12,
                f13,
                f14,
                f15,
                f16,
                f17,
                f18,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, PairStress> for PairStressFmt {
        #[verifier::spinoff_prover]
        fn serialize_into(&self, v: &PairStress, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<PairStressFmt as SpecSerializer>::spec_serialize);
            reveal(<PairStressFmt as SpecByteLen>::byte_len);
            reveal(<PairStress as DeepView>::deep_view);
            reveal(PairStressSpec::into_structural);
            let ghost old_obuf = obuf@;

            let PairStress {
                f1,
                f2,
                f3,
                f4,
                f5,
                f6,
                f7,
                f8,
                f9,
                f10,
                f11,
                f12,
                f13,
                f14,
                f15,
                f16,
                f17,
                f18,
            } = v;
            U8.serialize_into(f1, obuf);
            U16Le.serialize_into(f2, obuf);
            U32Le.serialize_into(f3, obuf);
            U8.serialize_into(f4, obuf);
            U8.serialize_into(f5, obuf);
            U8.serialize_into(f6, obuf);
            U8.serialize_into(f7, obuf);
            U8.serialize_into(f8, obuf);
            U8.serialize_into(f9, obuf);
            U8.serialize_into(f10, obuf);
            U8.serialize_into(f11, obuf);
            U8.serialize_into(f12, obuf);
            U8.serialize_into(f13, obuf);
            U8.serialize_into(f14, obuf);
            U8.serialize_into(f15, obuf);
            U8.serialize_into(f16, obuf);
            U8.serialize_into(f17, obuf);
            U8.serialize_into(f18, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<PairStress> for PairStressFmt {
        #[verifier::spinoff_prover]
        fn prepare(&self, v: &PairStress) -> Result<usize, PreSerializeError> {
            reveal(<PairStressFmt as SpecByteLen>::byte_len);
            reveal(<PairStress as DeepView>::deep_view);
            reveal(PairStressSpec::into_structural);
            let PairStress {
                f1,
                f2,
                f3,
                f4,
                f5,
                f6,
                f7,
                f8,
                f9,
                f10,
                f11,
                f12,
                f13,
                f14,
                f15,
                f16,
                f17,
                f18,
            } = v;
            let l1 = (U8).prepare (f1) ?;
            let l2 = (U16Le).prepare (f2) ?;
            let l3 = (U32Le).prepare (f3) ?;
            let l4 = (U8).prepare (f4) ?;
            let l5 = (U8).prepare (f5) ?;
            let l6 = (U8).prepare (f6) ?;
            let l7 = (U8).prepare (f7) ?;
            let l8 = (U8).prepare (f8) ?;
            let l9 = (U8).prepare (f9) ?;
            let l10 = (U8).prepare (f10) ?;
            let l11 = (U8).prepare (f11) ?;
            let l12 = (U8).prepare (f12) ?;
            let l13 = (U8).prepare (f13) ?;
            let l14 = (U8).prepare (f14) ?;
            let l15 = (U8).prepare (f15) ?;
            let l16 = (U8).prepare (f16) ?;
            let l17 = (U8).prepare (f17) ?;
            let l18 = (U8).prepare (f18) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l4).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l5).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l6).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l7).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l8).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l9).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l10).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l11).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l12).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l13).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l14).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l15).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l16).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l17).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l18).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for TstMydataFmt {
        type PT = TstMydata<'i>;

        #[verifier::spinoff_prover]
        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<TstMydataFmt as SpecParser>::spec_parse);
            reveal(<TstMydata as DeepView>::deep_view);
            reveal(TstMydataSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.tag.lemma_deep_view();
            }

            proof {
                self.tag.lemma_deep_view();
            }

            let (n, v) = match self.tag {
                TstTag::C0 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C0 (v))
                }
                ,
                TstTag::C1 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C1 (v))
                }
                ,
                TstTag::C2 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C2 (v))
                }
                ,
                TstTag::C3 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C3 (v))
                }
                ,
                TstTag::C4 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C4 (v))
                }
                ,
                TstTag::C5 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C5 (v))
                }
                ,
                TstTag::C6 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C6 (v))
                }
                ,
                TstTag::C7 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C7 (v))
                }
                ,
                TstTag::C8 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C8 (v))
                }
                ,
                TstTag::C9 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C9 (v))
                }
                ,
                TstTag::C10 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C10 (v))
                }
                ,
                TstTag::C11 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C11 (v))
                }
                ,
                TstTag::C12 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C12 (v))
                }
                ,
                TstTag::C13 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C13 (v))
                }
                ,
                TstTag::C14 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C14 (v))
                }
                ,
                TstTag::C15 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C15 (v))
                }
                ,
                TstTag::C16 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C16 (v))
                }
                ,
                TstTag::C17 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C17 (v))
                }
                ,
                TstTag::C18 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C18 (v))
                }
                ,
                TstTag::C19 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C19 (v))
                }
                ,
                TstTag::C20 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C20 (v))
                }
                ,
                TstTag::C21 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C21 (v))
                }
                ,
                TstTag::C22 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C22 (v))
                }
                ,
                TstTag::C23 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C23 (v))
                }
                ,
                TstTag::C24 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C24 (v))
                }
                ,
                TstTag::C25 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C25 (v))
                }
                ,
                TstTag::C26 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C26 (v))
                }
                ,
                TstTag::C27 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C27 (v))
                }
                ,
                TstTag::C28 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C28 (v))
                }
                ,
                TstTag::C29 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C29 (v))
                }
                ,
                TstTag::C30 => {
                    let (n,
                    v) = (Named ("mydata",
                    MydataFmt)).parse (& rest) ?;
                    (n,
                    TstMydata::C30 (v))
                }
                ,
                _ => {
                    let (n,
                    v) = (Tail).parse (& rest) ?;
                    (n,
                    TstMydata::Default (v))
                }
                ,
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TstMydata<'i>> for TstMydataFmt {
        #[verifier::spinoff_prover]
        fn serialize_into(&self, v: &TstMydata<'i>, obuf: &mut Output) {
            reveal(<TstMydataFmt as SpecSerializer>::spec_serialize);
            reveal(<TstMydataFmt as SpecByteLen>::byte_len);
            reveal(<TstMydata as DeepView>::deep_view);
            reveal(TstMydataSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.tag.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            proof {
                self.tag.lemma_deep_view();
            }

            match (self.tag, v) {
                (TstTag::C0, TstMydata::C0 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C1, TstMydata::C1 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C2, TstMydata::C2 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C3, TstMydata::C3 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C4, TstMydata::C4 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C5, TstMydata::C5 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C6, TstMydata::C6 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C7, TstMydata::C7 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C8, TstMydata::C8 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C9, TstMydata::C9 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C10, TstMydata::C10 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C11, TstMydata::C11 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C12, TstMydata::C12 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C13, TstMydata::C13 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C14, TstMydata::C14 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C15, TstMydata::C15 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C16, TstMydata::C16 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C17, TstMydata::C17 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C18, TstMydata::C18 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C19, TstMydata::C19 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C20, TstMydata::C20 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C21, TstMydata::C21 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C22, TstMydata::C22 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C23, TstMydata::C23 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C24, TstMydata::C24 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C25, TstMydata::C25 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C26, TstMydata::C26 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C27, TstMydata::C27 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C28, TstMydata::C28 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C29, TstMydata::C29 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TstTag::C30, TstMydata::C30 (v)) => {
                    (MydataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (_, TstMydata::Default (v)) => {
                    (Tail).serialize_into (v,
                    obuf) ;
                }
                ,
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TstMydata<'i>> for TstMydataFmt {
        #[verifier::spinoff_prover]
        fn prepare(&self, v: &TstMydata<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TstMydataFmt as SpecByteLen>::byte_len);
            reveal(<TstMydata as DeepView>::deep_view);
            reveal(TstMydataSpec::into_structural);
            proof {
                use_type_invariant(self);
                self.tag.lemma_deep_view();
            }

            proof {
                self.tag.lemma_deep_view();
            }

            match (self.tag, v) {
                (TstTag::C0, TstMydata::C0 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C1, TstMydata::C1 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C2, TstMydata::C2 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C3, TstMydata::C3 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C4, TstMydata::C4 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C5, TstMydata::C5 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C6, TstMydata::C6 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C7, TstMydata::C7 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C8, TstMydata::C8 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C9, TstMydata::C9 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C10, TstMydata::C10 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C11, TstMydata::C11 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C12, TstMydata::C12 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C13, TstMydata::C13 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C14, TstMydata::C14 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C15, TstMydata::C15 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C16, TstMydata::C16 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C17, TstMydata::C17 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C18, TstMydata::C18 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C19, TstMydata::C19 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C20, TstMydata::C20 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C21, TstMydata::C21 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C22, TstMydata::C22 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C23, TstMydata::C23 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C24, TstMydata::C24 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C25, TstMydata::C25 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C26, TstMydata::C26 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C27, TstMydata::C27 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C28, TstMydata::C28 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C29, TstMydata::C29 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::C30, TstMydata::C30 (v)) => (Named ("mydata", MydataFmt)).prepare (v),
                (TstTag::Unknown (x), TstMydata::Default (v)) if x != 0 && x != 1 && x != 2 && x != 3 && x != 4 && x != 5 && x != 6 && x != 7 && x != 8 && x != 9 && x != 10 && x != 11 && x != 12 && x != 13 && x != 14 && x != 15 && x != 16 && x != 17 && x != 18 && x != 19 && x != 20 && x != 21 && x != 22 && x != 23 && x != 24 && x != 25 && x != 26 && x != 27 && x != 28 && x != 29 && x != 30 => (Tail).prepare (v),
                 _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}
}
