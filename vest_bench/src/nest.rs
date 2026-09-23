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
# [doc = "data type for `nest0`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Nest0<'i> {
    pub id: u64,
    pub len: u32,
    pub payload: &'i [u8],
}
# [verifier::ext_equal]
pub struct Nest0Spec < T0 = u64, T1 = u32, T2 = Seq < u8 > > {
    pub id: T0,
    pub len: T1,
    pub payload: T2,
}
pub type Nest0Inner = (u64, (u32, Seq < u8 >)) ;
impl<'i> DeepView for Nest0<'i> {
    type V = Nest0Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Nest0Spec {
            id: self.id.deep_view(),
            len: self.len.deep_view(),
            payload: self.payload.deep_view(),
        }
    }
}
impl<'i> Nest0<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().id == self.id.deep_view(),
    self.deep_view().len == self.len.deep_view(),
    self.deep_view().payload == self.payload.deep_view(),
    {
        reveal(< Nest0 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > Nest0Spec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (id,
        (len,
        payload)) = input ;
        Self {
            id,
            len,
            payload
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            id,
            len,
            payload
        }
        = self ;
        (id,
        (len,
        payload))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Nest0Spec::from_structural) ;
        reveal(Nest0Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Nest0Spec::from_structural) ;
        reveal(Nest0Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            id,
            len,
            payload
        }
        => (id,
        (len,
        payload)),
    }
   ,
    {
        reveal(Nest0Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest0Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest0Reverse ;
impl SpecMap for Nest0Forward {
    type Input = Nest0Inner ;
    type Output = Nest0Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Nest0Spec::from_structural (input)
    }
}
impl SpecMap for Nest0Reverse {
    type Input = Nest0Spec ;
    type Output = Nest0Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nest1`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Nest1<'i> {
    pub hdr: u32,
    pub inner: Nest0<'i>,
    pub ftr: u16,
}
# [verifier::ext_equal]
pub struct Nest1Spec < T0 = u32, T1 = Nest0Spec, T2 = u16 > {
    pub hdr: T0,
    pub inner: T1,
    pub ftr: T2,
}
pub type Nest1Inner = (u32, (Nest0Spec, u16)) ;
impl<'i> DeepView for Nest1<'i> {
    type V = Nest1Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Nest1Spec {
            hdr: self.hdr.deep_view(),
            inner: self.inner.deep_view(),
            ftr: self.ftr.deep_view(),
        }
    }
}
impl<'i> Nest1<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().hdr == self.hdr.deep_view(),
    self.deep_view().inner == self.inner.deep_view(),
    self.deep_view().ftr == self.ftr.deep_view(),
    {
        reveal(< Nest1 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > Nest1Spec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (hdr,
        (inner,
        ftr)) = input ;
        Self {
            hdr,
            inner,
            ftr
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            hdr,
            inner,
            ftr
        }
        = self ;
        (hdr,
        (inner,
        ftr))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Nest1Spec::from_structural) ;
        reveal(Nest1Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Nest1Spec::from_structural) ;
        reveal(Nest1Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            hdr,
            inner,
            ftr
        }
        => (hdr,
        (inner,
        ftr)),
    }
   ,
    {
        reveal(Nest1Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest1Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest1Reverse ;
impl SpecMap for Nest1Forward {
    type Input = Nest1Inner ;
    type Output = Nest1Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Nest1Spec::from_structural (input)
    }
}
impl SpecMap for Nest1Reverse {
    type Input = Nest1Spec ;
    type Output = Nest1Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nest2`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Nest2<'i> {
    pub hdr: u32,
    pub inner: Nest1<'i>,
    pub ftr: u16,
}
# [verifier::ext_equal]
pub struct Nest2Spec < T0 = u32, T1 = Nest1Spec, T2 = u16 > {
    pub hdr: T0,
    pub inner: T1,
    pub ftr: T2,
}
pub type Nest2Inner = (u32, (Nest1Spec, u16)) ;
impl<'i> DeepView for Nest2<'i> {
    type V = Nest2Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Nest2Spec {
            hdr: self.hdr.deep_view(),
            inner: self.inner.deep_view(),
            ftr: self.ftr.deep_view(),
        }
    }
}
impl<'i> Nest2<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().hdr == self.hdr.deep_view(),
    self.deep_view().inner == self.inner.deep_view(),
    self.deep_view().ftr == self.ftr.deep_view(),
    {
        reveal(< Nest2 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > Nest2Spec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (hdr,
        (inner,
        ftr)) = input ;
        Self {
            hdr,
            inner,
            ftr
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            hdr,
            inner,
            ftr
        }
        = self ;
        (hdr,
        (inner,
        ftr))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Nest2Spec::from_structural) ;
        reveal(Nest2Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Nest2Spec::from_structural) ;
        reveal(Nest2Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            hdr,
            inner,
            ftr
        }
        => (hdr,
        (inner,
        ftr)),
    }
   ,
    {
        reveal(Nest2Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest2Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest2Reverse ;
impl SpecMap for Nest2Forward {
    type Input = Nest2Inner ;
    type Output = Nest2Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Nest2Spec::from_structural (input)
    }
}
impl SpecMap for Nest2Reverse {
    type Input = Nest2Spec ;
    type Output = Nest2Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nest3`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Nest3<'i> {
    pub hdr: u32,
    pub inner: Nest2<'i>,
    pub ftr: u16,
}
# [verifier::ext_equal]
pub struct Nest3Spec < T0 = u32, T1 = Nest2Spec, T2 = u16 > {
    pub hdr: T0,
    pub inner: T1,
    pub ftr: T2,
}
pub type Nest3Inner = (u32, (Nest2Spec, u16)) ;
impl<'i> DeepView for Nest3<'i> {
    type V = Nest3Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Nest3Spec {
            hdr: self.hdr.deep_view(),
            inner: self.inner.deep_view(),
            ftr: self.ftr.deep_view(),
        }
    }
}
impl<'i> Nest3<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().hdr == self.hdr.deep_view(),
    self.deep_view().inner == self.inner.deep_view(),
    self.deep_view().ftr == self.ftr.deep_view(),
    {
        reveal(< Nest3 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > Nest3Spec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (hdr,
        (inner,
        ftr)) = input ;
        Self {
            hdr,
            inner,
            ftr
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            hdr,
            inner,
            ftr
        }
        = self ;
        (hdr,
        (inner,
        ftr))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Nest3Spec::from_structural) ;
        reveal(Nest3Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Nest3Spec::from_structural) ;
        reveal(Nest3Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            hdr,
            inner,
            ftr
        }
        => (hdr,
        (inner,
        ftr)),
    }
   ,
    {
        reveal(Nest3Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest3Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest3Reverse ;
impl SpecMap for Nest3Forward {
    type Input = Nest3Inner ;
    type Output = Nest3Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Nest3Spec::from_structural (input)
    }
}
impl SpecMap for Nest3Reverse {
    type Input = Nest3Spec ;
    type Output = Nest3Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nest4`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Nest4<'i> {
    pub hdr: u32,
    pub inner: Nest3<'i>,
    pub ftr: u16,
}
# [verifier::ext_equal]
pub struct Nest4Spec < T0 = u32, T1 = Nest3Spec, T2 = u16 > {
    pub hdr: T0,
    pub inner: T1,
    pub ftr: T2,
}
pub type Nest4Inner = (u32, (Nest3Spec, u16)) ;
impl<'i> DeepView for Nest4<'i> {
    type V = Nest4Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Nest4Spec {
            hdr: self.hdr.deep_view(),
            inner: self.inner.deep_view(),
            ftr: self.ftr.deep_view(),
        }
    }
}
impl<'i> Nest4<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().hdr == self.hdr.deep_view(),
    self.deep_view().inner == self.inner.deep_view(),
    self.deep_view().ftr == self.ftr.deep_view(),
    {
        reveal(< Nest4 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > Nest4Spec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (hdr,
        (inner,
        ftr)) = input ;
        Self {
            hdr,
            inner,
            ftr
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            hdr,
            inner,
            ftr
        }
        = self ;
        (hdr,
        (inner,
        ftr))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Nest4Spec::from_structural) ;
        reveal(Nest4Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Nest4Spec::from_structural) ;
        reveal(Nest4Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            hdr,
            inner,
            ftr
        }
        => (hdr,
        (inner,
        ftr)),
    }
   ,
    {
        reveal(Nest4Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest4Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest4Reverse ;
impl SpecMap for Nest4Forward {
    type Input = Nest4Inner ;
    type Output = Nest4Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Nest4Spec::from_structural (input)
    }
}
impl SpecMap for Nest4Reverse {
    type Input = Nest4Spec ;
    type Output = Nest4Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nest5`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Nest5<'i> {
    pub hdr: u32,
    pub inner: Nest4<'i>,
    pub ftr: u16,
}
# [verifier::ext_equal]
pub struct Nest5Spec < T0 = u32, T1 = Nest4Spec, T2 = u16 > {
    pub hdr: T0,
    pub inner: T1,
    pub ftr: T2,
}
pub type Nest5Inner = (u32, (Nest4Spec, u16)) ;
impl<'i> DeepView for Nest5<'i> {
    type V = Nest5Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Nest5Spec {
            hdr: self.hdr.deep_view(),
            inner: self.inner.deep_view(),
            ftr: self.ftr.deep_view(),
        }
    }
}
impl<'i> Nest5<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().hdr == self.hdr.deep_view(),
    self.deep_view().inner == self.inner.deep_view(),
    self.deep_view().ftr == self.ftr.deep_view(),
    {
        reveal(< Nest5 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > Nest5Spec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (hdr,
        (inner,
        ftr)) = input ;
        Self {
            hdr,
            inner,
            ftr
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            hdr,
            inner,
            ftr
        }
        = self ;
        (hdr,
        (inner,
        ftr))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Nest5Spec::from_structural) ;
        reveal(Nest5Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Nest5Spec::from_structural) ;
        reveal(Nest5Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            hdr,
            inner,
            ftr
        }
        => (hdr,
        (inner,
        ftr)),
    }
   ,
    {
        reveal(Nest5Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest5Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest5Reverse ;
impl SpecMap for Nest5Forward {
    type Input = Nest5Inner ;
    type Output = Nest5Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Nest5Spec::from_structural (input)
    }
}
impl SpecMap for Nest5Reverse {
    type Input = Nest5Spec ;
    type Output = Nest5Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nest6`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Nest6<'i> {
    pub hdr: u32,
    pub inner: Nest5<'i>,
    pub ftr: u16,
}
# [verifier::ext_equal]
pub struct Nest6Spec < T0 = u32, T1 = Nest5Spec, T2 = u16 > {
    pub hdr: T0,
    pub inner: T1,
    pub ftr: T2,
}
pub type Nest6Inner = (u32, (Nest5Spec, u16)) ;
impl<'i> DeepView for Nest6<'i> {
    type V = Nest6Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Nest6Spec {
            hdr: self.hdr.deep_view(),
            inner: self.inner.deep_view(),
            ftr: self.ftr.deep_view(),
        }
    }
}
impl<'i> Nest6<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().hdr == self.hdr.deep_view(),
    self.deep_view().inner == self.inner.deep_view(),
    self.deep_view().ftr == self.ftr.deep_view(),
    {
        reveal(< Nest6 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > Nest6Spec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (hdr,
        (inner,
        ftr)) = input ;
        Self {
            hdr,
            inner,
            ftr
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            hdr,
            inner,
            ftr
        }
        = self ;
        (hdr,
        (inner,
        ftr))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Nest6Spec::from_structural) ;
        reveal(Nest6Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Nest6Spec::from_structural) ;
        reveal(Nest6Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            hdr,
            inner,
            ftr
        }
        => (hdr,
        (inner,
        ftr)),
    }
   ,
    {
        reveal(Nest6Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest6Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest6Reverse ;
impl SpecMap for Nest6Forward {
    type Input = Nest6Inner ;
    type Output = Nest6Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Nest6Spec::from_structural (input)
    }
}
impl SpecMap for Nest6Reverse {
    type Input = Nest6Spec ;
    type Output = Nest6Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nest7`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Nest7<'i> {
    pub hdr: u32,
    pub inner: Nest6<'i>,
    pub ftr: u16,
}
# [verifier::ext_equal]
pub struct Nest7Spec < T0 = u32, T1 = Nest6Spec, T2 = u16 > {
    pub hdr: T0,
    pub inner: T1,
    pub ftr: T2,
}
pub type Nest7Inner = (u32, (Nest6Spec, u16)) ;
impl<'i> DeepView for Nest7<'i> {
    type V = Nest7Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Nest7Spec {
            hdr: self.hdr.deep_view(),
            inner: self.inner.deep_view(),
            ftr: self.ftr.deep_view(),
        }
    }
}
impl<'i> Nest7<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().hdr == self.hdr.deep_view(),
    self.deep_view().inner == self.inner.deep_view(),
    self.deep_view().ftr == self.ftr.deep_view(),
    {
        reveal(< Nest7 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > Nest7Spec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (hdr,
        (inner,
        ftr)) = input ;
        Self {
            hdr,
            inner,
            ftr
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            hdr,
            inner,
            ftr
        }
        = self ;
        (hdr,
        (inner,
        ftr))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Nest7Spec::from_structural) ;
        reveal(Nest7Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Nest7Spec::from_structural) ;
        reveal(Nest7Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            hdr,
            inner,
            ftr
        }
        => (hdr,
        (inner,
        ftr)),
    }
   ,
    {
        reveal(Nest7Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest7Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest7Reverse ;
impl SpecMap for Nest7Forward {
    type Input = Nest7Inner ;
    type Output = Nest7Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Nest7Spec::from_structural (input)
    }
}
impl SpecMap for Nest7Reverse {
    type Input = Nest7Spec ;
    type Output = Nest7Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `nest8`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Nest8<'i> {
    pub hdr: u32,
    pub inner: Nest7<'i>,
    pub ftr: u16,
}
# [verifier::ext_equal]
pub struct Nest8Spec < T0 = u32, T1 = Nest7Spec, T2 = u16 > {
    pub hdr: T0,
    pub inner: T1,
    pub ftr: T2,
}
pub type Nest8Inner = (u32, (Nest7Spec, u16)) ;
impl<'i> DeepView for Nest8<'i> {
    type V = Nest8Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Nest8Spec {
            hdr: self.hdr.deep_view(),
            inner: self.inner.deep_view(),
            ftr: self.ftr.deep_view(),
        }
    }
}
impl<'i> Nest8<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().hdr == self.hdr.deep_view(),
    self.deep_view().inner == self.inner.deep_view(),
    self.deep_view().ftr == self.ftr.deep_view(),
    {
        reveal(< Nest8 as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > Nest8Spec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (hdr,
        (inner,
        ftr)) = input ;
        Self {
            hdr,
            inner,
            ftr
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            hdr,
            inner,
            ftr
        }
        = self ;
        (hdr,
        (inner,
        ftr))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Nest8Spec::from_structural) ;
        reveal(Nest8Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Nest8Spec::from_structural) ;
        reveal(Nest8Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            hdr,
            inner,
            ftr
        }
        => (hdr,
        (inner,
        ftr)),
    }
   ,
    {
        reveal(Nest8Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest8Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Nest8Reverse ;
impl SpecMap for Nest8Forward {
    type Input = Nest8Inner ;
    type Output = Nest8Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Nest8Spec::from_structural (input)
    }
}
impl SpecMap for Nest8Reverse {
    type Input = Nest8Spec ;
    type Output = Nest8Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `nest0`."]
# [derive (Clone, Copy)]
pub struct Nest0Fmt ;

pub type Nest0FmtSpec = Named < Mapped < Pair < U64Be, Bind < U32Be, spec_fn (u32) -> Varied < u32 > > >, BiMap < Nest0Forward, Nest0Reverse >> > ;

impl Nest0Fmt {
    # [doc = "specification constructor for `nest0`."] pub open spec fn spec_inner() -> Nest0FmtSpec {
        Named ("nest0",
        Mapped {
            inner: Pair (U64Be,
            Bind (U32Be,
            | len: u32 | Varied (len))),
            mapper: BiMap (Nest0Forward,
            Nest0Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `nest1`."]
# [derive (Clone, Copy)]
pub struct Nest1Fmt ;

pub type Nest1FmtSpec = Named < Mapped < Pair < U32Be, Pair < Nest0Fmt, U16Be > >, BiMap < Nest1Forward, Nest1Reverse >> > ;

impl Nest1Fmt {
    # [doc = "specification constructor for `nest1`."] pub open spec fn spec_inner() -> Nest1FmtSpec {
        Named ("nest1",
        Mapped {
            inner: Pair (U32Be,
            Pair (Nest0Fmt,
            U16Be)),
            mapper: BiMap (Nest1Forward,
            Nest1Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `nest2`."]
# [derive (Clone, Copy)]
pub struct Nest2Fmt ;

pub type Nest2FmtSpec = Named < Mapped < Pair < U32Be, Pair < Nest1Fmt, U16Be > >, BiMap < Nest2Forward, Nest2Reverse >> > ;

impl Nest2Fmt {
    # [doc = "specification constructor for `nest2`."] pub open spec fn spec_inner() -> Nest2FmtSpec {
        Named ("nest2",
        Mapped {
            inner: Pair (U32Be,
            Pair (Nest1Fmt,
            U16Be)),
            mapper: BiMap (Nest2Forward,
            Nest2Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `nest3`."]
# [derive (Clone, Copy)]
pub struct Nest3Fmt ;

pub type Nest3FmtSpec = Named < Mapped < Pair < U32Be, Pair < Nest2Fmt, U16Be > >, BiMap < Nest3Forward, Nest3Reverse >> > ;

impl Nest3Fmt {
    # [doc = "specification constructor for `nest3`."] pub open spec fn spec_inner() -> Nest3FmtSpec {
        Named ("nest3",
        Mapped {
            inner: Pair (U32Be,
            Pair (Nest2Fmt,
            U16Be)),
            mapper: BiMap (Nest3Forward,
            Nest3Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `nest4`."]
# [derive (Clone, Copy)]
pub struct Nest4Fmt ;

pub type Nest4FmtSpec = Named < Mapped < Pair < U32Be, Pair < Nest3Fmt, U16Be > >, BiMap < Nest4Forward, Nest4Reverse >> > ;

impl Nest4Fmt {
    # [doc = "specification constructor for `nest4`."] pub open spec fn spec_inner() -> Nest4FmtSpec {
        Named ("nest4",
        Mapped {
            inner: Pair (U32Be,
            Pair (Nest3Fmt,
            U16Be)),
            mapper: BiMap (Nest4Forward,
            Nest4Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `nest5`."]
# [derive (Clone, Copy)]
pub struct Nest5Fmt ;

pub type Nest5FmtSpec = Named < Mapped < Pair < U32Be, Pair < Nest4Fmt, U16Be > >, BiMap < Nest5Forward, Nest5Reverse >> > ;

impl Nest5Fmt {
    # [doc = "specification constructor for `nest5`."] pub open spec fn spec_inner() -> Nest5FmtSpec {
        Named ("nest5",
        Mapped {
            inner: Pair (U32Be,
            Pair (Nest4Fmt,
            U16Be)),
            mapper: BiMap (Nest5Forward,
            Nest5Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `nest6`."]
# [derive (Clone, Copy)]
pub struct Nest6Fmt ;

pub type Nest6FmtSpec = Named < Mapped < Pair < U32Be, Pair < Nest5Fmt, U16Be > >, BiMap < Nest6Forward, Nest6Reverse >> > ;

impl Nest6Fmt {
    # [doc = "specification constructor for `nest6`."] pub open spec fn spec_inner() -> Nest6FmtSpec {
        Named ("nest6",
        Mapped {
            inner: Pair (U32Be,
            Pair (Nest5Fmt,
            U16Be)),
            mapper: BiMap (Nest6Forward,
            Nest6Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `nest7`."]
# [derive (Clone, Copy)]
pub struct Nest7Fmt ;

pub type Nest7FmtSpec = Named < Mapped < Pair < U32Be, Pair < Nest6Fmt, U16Be > >, BiMap < Nest7Forward, Nest7Reverse >> > ;

impl Nest7Fmt {
    # [doc = "specification constructor for `nest7`."] pub open spec fn spec_inner() -> Nest7FmtSpec {
        Named ("nest7",
        Mapped {
            inner: Pair (U32Be,
            Pair (Nest6Fmt,
            U16Be)),
            mapper: BiMap (Nest7Forward,
            Nest7Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `nest8`."]
# [derive (Clone, Copy)]
pub struct Nest8Fmt ;

pub type Nest8FmtSpec = Named < Mapped < Pair < U32Be, Pair < Nest7Fmt, U16Be > >, BiMap < Nest8Forward, Nest8Reverse >> > ;

impl Nest8Fmt {
    # [doc = "specification constructor for `nest8`."] pub open spec fn spec_inner() -> Nest8FmtSpec {
        Named ("nest8",
        Mapped {
            inner: Pair (U32Be,
            Pair (Nest7Fmt,
            U16Be)),
            mapper: BiMap (Nest8Forward,
            Nest8Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for Nest0Fmt {
        type PVal = Nest0Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Nest0Fmt {
        type Val = Nest0Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Nest0Fmt {
        type SValue = Nest0Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Nest0Fmt {
        type SVal = Nest0Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Nest0Fmt {
        type T = Nest0Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Nest1Fmt {
        type PVal = Nest1Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Nest1Fmt {
        type Val = Nest1Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Nest1Fmt {
        type SValue = Nest1Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Nest1Fmt {
        type SVal = Nest1Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Nest1Fmt {
        type T = Nest1Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Nest2Fmt {
        type PVal = Nest2Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Nest2Fmt {
        type Val = Nest2Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Nest2Fmt {
        type SValue = Nest2Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Nest2Fmt {
        type SVal = Nest2Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Nest2Fmt {
        type T = Nest2Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Nest3Fmt {
        type PVal = Nest3Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Nest3Fmt {
        type Val = Nest3Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Nest3Fmt {
        type SValue = Nest3Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Nest3Fmt {
        type SVal = Nest3Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Nest3Fmt {
        type T = Nest3Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Nest4Fmt {
        type PVal = Nest4Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Nest4Fmt {
        type Val = Nest4Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Nest4Fmt {
        type SValue = Nest4Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Nest4Fmt {
        type SVal = Nest4Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Nest4Fmt {
        type T = Nest4Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Nest5Fmt {
        type PVal = Nest5Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Nest5Fmt {
        type Val = Nest5Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Nest5Fmt {
        type SValue = Nest5Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Nest5Fmt {
        type SVal = Nest5Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Nest5Fmt {
        type T = Nest5Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Nest6Fmt {
        type PVal = Nest6Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Nest6Fmt {
        type Val = Nest6Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Nest6Fmt {
        type SValue = Nest6Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Nest6Fmt {
        type SVal = Nest6Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Nest6Fmt {
        type T = Nest6Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Nest7Fmt {
        type PVal = Nest7Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Nest7Fmt {
        type Val = Nest7Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Nest7Fmt {
        type SValue = Nest7Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Nest7Fmt {
        type SVal = Nest7Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Nest7Fmt {
        type T = Nest7Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Nest8Fmt {
        type PVal = Nest8Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Nest8Fmt {
        type Val = Nest8Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Nest8Fmt {
        type SValue = Nest8Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Nest8Fmt {
        type SVal = Nest8Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Nest8Fmt {
        type T = Nest8Spec ;
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
        Nest0Spec::lemma_from_into,
        Nest0Spec::lemma_into_from,
        Nest1Spec::lemma_from_into,
        Nest1Spec::lemma_into_from,
        Nest2Spec::lemma_from_into,
        Nest2Spec::lemma_into_from,
        Nest3Spec::lemma_from_into,
        Nest3Spec::lemma_into_from,
        Nest4Spec::lemma_from_into,
        Nest4Spec::lemma_into_from,
        Nest5Spec::lemma_from_into,
        Nest5Spec::lemma_into_from,
        Nest6Spec::lemma_from_into,
        Nest6Spec::lemma_into_from,
        Nest7Spec::lemma_from_into,
        Nest7Spec::lemma_into_from,
        Nest8Spec::lemma_from_into,
        Nest8Spec::lemma_into_from,
    };

    impl SafeParser for Nest0Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest0Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Nest0Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Nest0Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Nest0Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest0Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest0Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest0Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest0Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest0Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest0Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest0Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Nest0Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Nest0Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Nest0Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Nest0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Nest0Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Nest0Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest0Fmt as Consistency>::consistent) ;
            reveal(< Nest0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Nest0Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Nest0Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Nest0Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Nest0Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest0Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest0Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Nest0Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Nest0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest0Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Nest0Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Nest0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest0Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Nest1Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest1Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Nest1Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Nest1Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Nest1Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest1Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest1Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest1Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest1Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest1Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Nest1Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Nest1Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Nest1Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Nest1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Nest1Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Nest1Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest1Fmt as Consistency>::consistent) ;
            reveal(< Nest1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Nest1Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Nest1Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Nest1Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Nest1Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest1Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Nest1Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Nest1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest1Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Nest1Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Nest1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest1Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Nest2Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest2Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Nest2Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Nest2Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Nest2Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest2Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest2Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest2Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest2Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest2Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest2Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest2Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Nest2Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Nest2Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Nest2Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Nest2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Nest2Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Nest2Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest2Fmt as Consistency>::consistent) ;
            reveal(< Nest2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Nest2Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Nest2Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Nest2Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Nest2Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest2Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest2Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Nest2Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Nest2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest2Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Nest2Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Nest2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest2Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Nest3Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest3Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Nest3Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Nest3Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Nest3Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest3Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest3Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest3Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest3Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest3Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest3Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest3Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest3Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Nest3Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest3Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest3Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest3Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Nest3Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Nest3Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Nest3Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Nest3Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Nest3Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest3Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest3Fmt as Consistency>::consistent) ;
            reveal(< Nest3Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Nest3Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Nest3Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Nest3Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Nest3Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest3Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest3Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Nest3Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Nest3Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest3Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Nest3Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Nest3Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest3Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Nest4Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest4Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Nest4Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Nest4Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Nest4Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest4Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest4Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest4Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest4Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest4Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest4Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest4Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Nest4Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Nest4Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Nest4Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Nest4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Nest4Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Nest4Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest4Fmt as Consistency>::consistent) ;
            reveal(< Nest4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Nest4Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Nest4Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Nest4Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Nest4Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest4Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest4Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Nest4Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Nest4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest4Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Nest4Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Nest4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest4Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Nest5Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest5Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Nest5Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Nest5Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Nest5Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest5Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest5Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest5Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest5Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest5Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest5Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest5Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest5Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Nest5Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest5Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest5Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest5Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Nest5Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Nest5Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Nest5Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Nest5Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Nest5Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest5Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest5Fmt as Consistency>::consistent) ;
            reveal(< Nest5Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Nest5Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Nest5Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Nest5Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Nest5Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest5Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest5Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Nest5Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Nest5Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest5Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Nest5Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Nest5Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest5Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Nest6Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest6Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Nest6Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Nest6Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Nest6Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest6Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest6Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest6Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest6Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest6Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest6Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest6Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest6Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Nest6Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest6Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest6Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest6Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Nest6Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Nest6Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Nest6Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Nest6Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Nest6Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest6Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest6Fmt as Consistency>::consistent) ;
            reveal(< Nest6Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Nest6Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Nest6Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Nest6Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Nest6Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest6Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest6Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Nest6Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Nest6Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest6Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Nest6Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Nest6Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest6Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Nest7Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest7Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Nest7Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Nest7Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Nest7Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest7Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest7Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest7Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest7Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest7Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest7Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest7Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest7Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Nest7Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest7Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest7Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest7Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Nest7Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Nest7Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Nest7Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Nest7Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Nest7Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest7Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest7Fmt as Consistency>::consistent) ;
            reveal(< Nest7Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Nest7Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Nest7Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Nest7Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Nest7Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest7Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest7Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Nest7Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Nest7Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest7Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Nest7Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Nest7Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest7Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Nest8Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest8Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Nest8Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Nest8Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Nest8Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest8Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest8Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest8Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Nest8Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest8Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest8Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest8Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Nest8Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Nest8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Nest8Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Nest8Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Nest8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Nest8Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Nest8Fmt as SpecParser>::spec_parse) ;
            reveal(< Nest8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest8Fmt as Consistency>::consistent) ;
            reveal(< Nest8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Nest8Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Nest8Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Nest8Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Nest8Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Nest8Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Nest8Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Nest8Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Nest8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest8Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Nest8Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Nest8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Nest8Fmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for Nest0Fmt {
        type PT = Nest0<'i>;

        fn min_byte_len(&self) -> usize {
            12
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Nest0Fmt as SpecParser>::spec_parse);
            reveal(<Nest0 as DeepView>::deep_view);
            reveal(Nest0Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, id) = (U64Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, len) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, payload) = (Varied (len)).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Nest0 {
                id,
                len,
                payload,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Nest0<'i>> for Nest0Fmt {
        fn serialize_into(&self, v: &Nest0<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<Nest0Fmt as SpecSerializer>::spec_serialize);
            reveal(<Nest0Fmt as SpecByteLen>::byte_len);
            reveal(<Nest0 as DeepView>::deep_view);
            reveal(Nest0Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Nest0 {
                id,
                len,
                payload,
            } = v;
            U64Be.serialize_into(id, obuf);
            U32Be.serialize_into(len, obuf);
            Varied (*len).serialize_into(* payload, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Nest0<'i>> for Nest0Fmt {
        fn prepare(&self, v: &Nest0<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Nest0Fmt as SpecByteLen>::byte_len);
            reveal(<Nest0 as DeepView>::deep_view);
            reveal(Nest0Spec::into_structural);
            let Nest0 {
                id,
                len,
                payload,
            } = v;
            let l1 = (U64Be).prepare (id) ?;
            let l2 = (U32Be).prepare (len) ?;
            let l3 = (Varied (*len)).prepare (payload) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Nest1Fmt {
        type PT = Nest1<'i>;

        fn min_byte_len(&self) -> usize {
            18
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Nest1Fmt as SpecParser>::spec_parse);
            reveal(<Nest1 as DeepView>::deep_view);
            reveal(Nest1Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, inner) = (Named ("nest0", Nest0Fmt)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, ftr) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Nest1 {
                hdr,
                inner,
                ftr,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Nest1<'i>> for Nest1Fmt {
        fn serialize_into(&self, v: &Nest1<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<Nest1Fmt as SpecSerializer>::spec_serialize);
            reveal(<Nest1Fmt as SpecByteLen>::byte_len);
            reveal(<Nest1 as DeepView>::deep_view);
            reveal(Nest1Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Nest1 {
                hdr,
                inner,
                ftr,
            } = v;
            U32Be.serialize_into(hdr, obuf);
            Nest0Fmt.serialize_into(inner, obuf);
            U16Be.serialize_into(ftr, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Nest1<'i>> for Nest1Fmt {
        fn prepare(&self, v: &Nest1<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Nest1Fmt as SpecByteLen>::byte_len);
            reveal(<Nest1 as DeepView>::deep_view);
            reveal(Nest1Spec::into_structural);
            let Nest1 {
                hdr,
                inner,
                ftr,
            } = v;
            let l1 = (U32Be).prepare (hdr) ?;
            let l2 = (Named ("nest0", Nest0Fmt)).prepare (inner) ?;
            let l3 = (U16Be).prepare (ftr) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Nest2Fmt {
        type PT = Nest2<'i>;

        fn min_byte_len(&self) -> usize {
            24
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Nest2Fmt as SpecParser>::spec_parse);
            reveal(<Nest2 as DeepView>::deep_view);
            reveal(Nest2Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, inner) = (Named ("nest1", Nest1Fmt)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, ftr) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Nest2 {
                hdr,
                inner,
                ftr,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Nest2<'i>> for Nest2Fmt {
        fn serialize_into(&self, v: &Nest2<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<Nest2Fmt as SpecSerializer>::spec_serialize);
            reveal(<Nest2Fmt as SpecByteLen>::byte_len);
            reveal(<Nest2 as DeepView>::deep_view);
            reveal(Nest2Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Nest2 {
                hdr,
                inner,
                ftr,
            } = v;
            U32Be.serialize_into(hdr, obuf);
            Nest1Fmt.serialize_into(inner, obuf);
            U16Be.serialize_into(ftr, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Nest2<'i>> for Nest2Fmt {
        fn prepare(&self, v: &Nest2<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Nest2Fmt as SpecByteLen>::byte_len);
            reveal(<Nest2 as DeepView>::deep_view);
            reveal(Nest2Spec::into_structural);
            let Nest2 {
                hdr,
                inner,
                ftr,
            } = v;
            let l1 = (U32Be).prepare (hdr) ?;
            let l2 = (Named ("nest1", Nest1Fmt)).prepare (inner) ?;
            let l3 = (U16Be).prepare (ftr) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Nest3Fmt {
        type PT = Nest3<'i>;

        fn min_byte_len(&self) -> usize {
            30
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Nest3Fmt as SpecParser>::spec_parse);
            reveal(<Nest3 as DeepView>::deep_view);
            reveal(Nest3Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, inner) = (Named ("nest2", Nest2Fmt)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, ftr) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Nest3 {
                hdr,
                inner,
                ftr,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Nest3<'i>> for Nest3Fmt {
        fn serialize_into(&self, v: &Nest3<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<Nest3Fmt as SpecSerializer>::spec_serialize);
            reveal(<Nest3Fmt as SpecByteLen>::byte_len);
            reveal(<Nest3 as DeepView>::deep_view);
            reveal(Nest3Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Nest3 {
                hdr,
                inner,
                ftr,
            } = v;
            U32Be.serialize_into(hdr, obuf);
            Nest2Fmt.serialize_into(inner, obuf);
            U16Be.serialize_into(ftr, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Nest3<'i>> for Nest3Fmt {
        fn prepare(&self, v: &Nest3<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Nest3Fmt as SpecByteLen>::byte_len);
            reveal(<Nest3 as DeepView>::deep_view);
            reveal(Nest3Spec::into_structural);
            let Nest3 {
                hdr,
                inner,
                ftr,
            } = v;
            let l1 = (U32Be).prepare (hdr) ?;
            let l2 = (Named ("nest2", Nest2Fmt)).prepare (inner) ?;
            let l3 = (U16Be).prepare (ftr) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Nest4Fmt {
        type PT = Nest4<'i>;

        fn min_byte_len(&self) -> usize {
            36
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Nest4Fmt as SpecParser>::spec_parse);
            reveal(<Nest4 as DeepView>::deep_view);
            reveal(Nest4Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, inner) = (Named ("nest3", Nest3Fmt)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, ftr) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Nest4 {
                hdr,
                inner,
                ftr,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Nest4<'i>> for Nest4Fmt {
        fn serialize_into(&self, v: &Nest4<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<Nest4Fmt as SpecSerializer>::spec_serialize);
            reveal(<Nest4Fmt as SpecByteLen>::byte_len);
            reveal(<Nest4 as DeepView>::deep_view);
            reveal(Nest4Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Nest4 {
                hdr,
                inner,
                ftr,
            } = v;
            U32Be.serialize_into(hdr, obuf);
            Nest3Fmt.serialize_into(inner, obuf);
            U16Be.serialize_into(ftr, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Nest4<'i>> for Nest4Fmt {
        fn prepare(&self, v: &Nest4<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Nest4Fmt as SpecByteLen>::byte_len);
            reveal(<Nest4 as DeepView>::deep_view);
            reveal(Nest4Spec::into_structural);
            let Nest4 {
                hdr,
                inner,
                ftr,
            } = v;
            let l1 = (U32Be).prepare (hdr) ?;
            let l2 = (Named ("nest3", Nest3Fmt)).prepare (inner) ?;
            let l3 = (U16Be).prepare (ftr) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Nest5Fmt {
        type PT = Nest5<'i>;

        fn min_byte_len(&self) -> usize {
            42
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Nest5Fmt as SpecParser>::spec_parse);
            reveal(<Nest5 as DeepView>::deep_view);
            reveal(Nest5Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, inner) = (Named ("nest4", Nest4Fmt)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, ftr) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Nest5 {
                hdr,
                inner,
                ftr,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Nest5<'i>> for Nest5Fmt {
        fn serialize_into(&self, v: &Nest5<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<Nest5Fmt as SpecSerializer>::spec_serialize);
            reveal(<Nest5Fmt as SpecByteLen>::byte_len);
            reveal(<Nest5 as DeepView>::deep_view);
            reveal(Nest5Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Nest5 {
                hdr,
                inner,
                ftr,
            } = v;
            U32Be.serialize_into(hdr, obuf);
            Nest4Fmt.serialize_into(inner, obuf);
            U16Be.serialize_into(ftr, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Nest5<'i>> for Nest5Fmt {
        fn prepare(&self, v: &Nest5<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Nest5Fmt as SpecByteLen>::byte_len);
            reveal(<Nest5 as DeepView>::deep_view);
            reveal(Nest5Spec::into_structural);
            let Nest5 {
                hdr,
                inner,
                ftr,
            } = v;
            let l1 = (U32Be).prepare (hdr) ?;
            let l2 = (Named ("nest4", Nest4Fmt)).prepare (inner) ?;
            let l3 = (U16Be).prepare (ftr) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Nest6Fmt {
        type PT = Nest6<'i>;

        fn min_byte_len(&self) -> usize {
            48
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Nest6Fmt as SpecParser>::spec_parse);
            reveal(<Nest6 as DeepView>::deep_view);
            reveal(Nest6Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, inner) = (Named ("nest5", Nest5Fmt)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, ftr) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Nest6 {
                hdr,
                inner,
                ftr,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Nest6<'i>> for Nest6Fmt {
        fn serialize_into(&self, v: &Nest6<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<Nest6Fmt as SpecSerializer>::spec_serialize);
            reveal(<Nest6Fmt as SpecByteLen>::byte_len);
            reveal(<Nest6 as DeepView>::deep_view);
            reveal(Nest6Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Nest6 {
                hdr,
                inner,
                ftr,
            } = v;
            U32Be.serialize_into(hdr, obuf);
            Nest5Fmt.serialize_into(inner, obuf);
            U16Be.serialize_into(ftr, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Nest6<'i>> for Nest6Fmt {
        fn prepare(&self, v: &Nest6<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Nest6Fmt as SpecByteLen>::byte_len);
            reveal(<Nest6 as DeepView>::deep_view);
            reveal(Nest6Spec::into_structural);
            let Nest6 {
                hdr,
                inner,
                ftr,
            } = v;
            let l1 = (U32Be).prepare (hdr) ?;
            let l2 = (Named ("nest5", Nest5Fmt)).prepare (inner) ?;
            let l3 = (U16Be).prepare (ftr) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Nest7Fmt {
        type PT = Nest7<'i>;

        fn min_byte_len(&self) -> usize {
            54
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Nest7Fmt as SpecParser>::spec_parse);
            reveal(<Nest7 as DeepView>::deep_view);
            reveal(Nest7Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, inner) = (Named ("nest6", Nest6Fmt)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, ftr) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Nest7 {
                hdr,
                inner,
                ftr,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Nest7<'i>> for Nest7Fmt {
        fn serialize_into(&self, v: &Nest7<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<Nest7Fmt as SpecSerializer>::spec_serialize);
            reveal(<Nest7Fmt as SpecByteLen>::byte_len);
            reveal(<Nest7 as DeepView>::deep_view);
            reveal(Nest7Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Nest7 {
                hdr,
                inner,
                ftr,
            } = v;
            U32Be.serialize_into(hdr, obuf);
            Nest6Fmt.serialize_into(inner, obuf);
            U16Be.serialize_into(ftr, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Nest7<'i>> for Nest7Fmt {
        fn prepare(&self, v: &Nest7<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Nest7Fmt as SpecByteLen>::byte_len);
            reveal(<Nest7 as DeepView>::deep_view);
            reveal(Nest7Spec::into_structural);
            let Nest7 {
                hdr,
                inner,
                ftr,
            } = v;
            let l1 = (U32Be).prepare (hdr) ?;
            let l2 = (Named ("nest6", Nest6Fmt)).prepare (inner) ?;
            let l3 = (U16Be).prepare (ftr) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Nest8Fmt {
        type PT = Nest8<'i>;

        fn min_byte_len(&self) -> usize {
            60
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Nest8Fmt as SpecParser>::spec_parse);
            reveal(<Nest8 as DeepView>::deep_view);
            reveal(Nest8Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, hdr) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, inner) = (Named ("nest7", Nest7Fmt)).parse (& rest) ?;
            let rest = rest.skip(n2);
            let (n3, ftr) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = Nest8 {
                hdr,
                inner,
                ftr,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Nest8<'i>> for Nest8Fmt {
        fn serialize_into(&self, v: &Nest8<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<Nest8Fmt as SpecSerializer>::spec_serialize);
            reveal(<Nest8Fmt as SpecByteLen>::byte_len);
            reveal(<Nest8 as DeepView>::deep_view);
            reveal(Nest8Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Nest8 {
                hdr,
                inner,
                ftr,
            } = v;
            U32Be.serialize_into(hdr, obuf);
            Nest7Fmt.serialize_into(inner, obuf);
            U16Be.serialize_into(ftr, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Nest8<'i>> for Nest8Fmt {
        fn prepare(&self, v: &Nest8<'i>) -> Result<usize, PreSerializeError> {
            reveal(<Nest8Fmt as SpecByteLen>::byte_len);
            reveal(<Nest8 as DeepView>::deep_view);
            reveal(Nest8Spec::into_structural);
            let Nest8 {
                hdr,
                inner,
                ftr,
            } = v;
            let l1 = (U32Be).prepare (hdr) ?;
            let l2 = (Named ("nest7", Nest7Fmt)).prepare (inner) ?;
            let l3 = (U16Be).prepare (ftr) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }

}
}
