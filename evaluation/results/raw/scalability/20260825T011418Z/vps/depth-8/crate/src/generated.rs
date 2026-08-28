# ! [allow (warnings)] use vps_lib::combinators::mapped::spec::* ;
use vps_lib::combinators::* ;
use vps_lib::combinators::recursive::* ;
use Sum::Inl as L ;
use Sum::Inr as R ;
use vps_lib::Never ;
use vps_lib::core::exec::input::{
    InputBuf,
    InputSlice
}
;
use vps_lib::core::exec::output::OutputBuf ;
use vps_lib::core::exec::parser::* ;
use vps_lib::core::exec::serializer::* ;
use vps_lib::core::exec::ParseError ;
use vps_lib::core::exec::bytes_eq ;
use vps_lib::core::{
    proof::*,
    spec::*
}
;
use vps_lib::primitives::btcvarint::VarInt ;
use vps_lib::primitives::leb128::ULeb128 ;
use vstd::prelude::* ;
verus! {
// ============================================================
// Data Types
// ============================================================
# [doc = "data type for `depth0`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth0 {
    pub value: u8,
}
# [verifier::ext_equal]
pub struct Depth0Spec < T0 = u8 > {
    pub value: T0,
}
pub type Depth0Inner = u8 ;
impl DeepView for Depth0 {
    type V = Depth0Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth0Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth0 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth0 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth0Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth0Spec::from_structural) ;
        reveal(Depth0Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth0Spec::from_structural) ;
        reveal(Depth0Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth0Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth0Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth0Reverse ;
impl SpecMap for Depth0Forward {
    type Input = Depth0Inner ;
    type Output = Depth0Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth0Spec::from_structural (input)
    }
}
impl SpecMap for Depth0Reverse {
    type Input = Depth0Spec ;
    type Output = Depth0Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `depth1`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth1 {
    pub value: Depth0,
}
# [verifier::ext_equal]
pub struct Depth1Spec < T0 = Depth0Spec > {
    pub value: T0,
}
pub type Depth1Inner = Depth0Spec ;
impl DeepView for Depth1 {
    type V = Depth1Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth1Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth1 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth1 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth1Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth1Spec::from_structural) ;
        reveal(Depth1Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth1Spec::from_structural) ;
        reveal(Depth1Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth1Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth1Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth1Reverse ;
impl SpecMap for Depth1Forward {
    type Input = Depth1Inner ;
    type Output = Depth1Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth1Spec::from_structural (input)
    }
}
impl SpecMap for Depth1Reverse {
    type Input = Depth1Spec ;
    type Output = Depth1Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `depth2`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth2 {
    pub value: Depth1,
}
# [verifier::ext_equal]
pub struct Depth2Spec < T0 = Depth1Spec > {
    pub value: T0,
}
pub type Depth2Inner = Depth1Spec ;
impl DeepView for Depth2 {
    type V = Depth2Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth2Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth2 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth2 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth2Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth2Spec::from_structural) ;
        reveal(Depth2Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth2Spec::from_structural) ;
        reveal(Depth2Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth2Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth2Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth2Reverse ;
impl SpecMap for Depth2Forward {
    type Input = Depth2Inner ;
    type Output = Depth2Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth2Spec::from_structural (input)
    }
}
impl SpecMap for Depth2Reverse {
    type Input = Depth2Spec ;
    type Output = Depth2Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `depth3`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth3 {
    pub value: Depth2,
}
# [verifier::ext_equal]
pub struct Depth3Spec < T0 = Depth2Spec > {
    pub value: T0,
}
pub type Depth3Inner = Depth2Spec ;
impl DeepView for Depth3 {
    type V = Depth3Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth3Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth3 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth3 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth3Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth3Spec::from_structural) ;
        reveal(Depth3Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth3Spec::from_structural) ;
        reveal(Depth3Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth3Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth3Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth3Reverse ;
impl SpecMap for Depth3Forward {
    type Input = Depth3Inner ;
    type Output = Depth3Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth3Spec::from_structural (input)
    }
}
impl SpecMap for Depth3Reverse {
    type Input = Depth3Spec ;
    type Output = Depth3Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `depth4`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth4 {
    pub value: Depth3,
}
# [verifier::ext_equal]
pub struct Depth4Spec < T0 = Depth3Spec > {
    pub value: T0,
}
pub type Depth4Inner = Depth3Spec ;
impl DeepView for Depth4 {
    type V = Depth4Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth4Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth4 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth4 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth4Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth4Spec::from_structural) ;
        reveal(Depth4Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth4Spec::from_structural) ;
        reveal(Depth4Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth4Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth4Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth4Reverse ;
impl SpecMap for Depth4Forward {
    type Input = Depth4Inner ;
    type Output = Depth4Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth4Spec::from_structural (input)
    }
}
impl SpecMap for Depth4Reverse {
    type Input = Depth4Spec ;
    type Output = Depth4Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `depth5`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth5 {
    pub value: Depth4,
}
# [verifier::ext_equal]
pub struct Depth5Spec < T0 = Depth4Spec > {
    pub value: T0,
}
pub type Depth5Inner = Depth4Spec ;
impl DeepView for Depth5 {
    type V = Depth5Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth5Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth5 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth5 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth5Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth5Spec::from_structural) ;
        reveal(Depth5Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth5Spec::from_structural) ;
        reveal(Depth5Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth5Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth5Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth5Reverse ;
impl SpecMap for Depth5Forward {
    type Input = Depth5Inner ;
    type Output = Depth5Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth5Spec::from_structural (input)
    }
}
impl SpecMap for Depth5Reverse {
    type Input = Depth5Spec ;
    type Output = Depth5Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `depth6`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth6 {
    pub value: Depth5,
}
# [verifier::ext_equal]
pub struct Depth6Spec < T0 = Depth5Spec > {
    pub value: T0,
}
pub type Depth6Inner = Depth5Spec ;
impl DeepView for Depth6 {
    type V = Depth6Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth6Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth6 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth6 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth6Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth6Spec::from_structural) ;
        reveal(Depth6Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth6Spec::from_structural) ;
        reveal(Depth6Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth6Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth6Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth6Reverse ;
impl SpecMap for Depth6Forward {
    type Input = Depth6Inner ;
    type Output = Depth6Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth6Spec::from_structural (input)
    }
}
impl SpecMap for Depth6Reverse {
    type Input = Depth6Spec ;
    type Output = Depth6Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `depth7`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth7 {
    pub value: Depth6,
}
# [verifier::ext_equal]
pub struct Depth7Spec < T0 = Depth6Spec > {
    pub value: T0,
}
pub type Depth7Inner = Depth6Spec ;
impl DeepView for Depth7 {
    type V = Depth7Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth7Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth7 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth7 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth7Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth7Spec::from_structural) ;
        reveal(Depth7Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth7Spec::from_structural) ;
        reveal(Depth7Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth7Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth7Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth7Reverse ;
impl SpecMap for Depth7Forward {
    type Input = Depth7Inner ;
    type Output = Depth7Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth7Spec::from_structural (input)
    }
}
impl SpecMap for Depth7Reverse {
    type Input = Depth7Spec ;
    type Output = Depth7Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `depth8`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct Depth8 {
    pub value: Depth7,
}
# [verifier::ext_equal]
pub struct Depth8Spec < T0 = Depth7Spec > {
    pub value: T0,
}
pub type Depth8Inner = Depth7Spec ;
impl DeepView for Depth8 {
    type V = Depth8Spec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        Depth8Spec {
            value: self.value.deep_view(),
        }
    }
}
impl Depth8 {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().value == self.value.deep_view(),
    {
        reveal(< Depth8 as DeepView>::deep_view) ;
    }
}
impl < T0 > Depth8Spec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let value = input ;
        Self {
            value
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            value
        }
        = self ;
        value
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(Depth8Spec::from_structural) ;
        reveal(Depth8Spec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(Depth8Spec::from_structural) ;
        reveal(Depth8Spec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            value
        }
        => value,
    }
   ,
    {
        reveal(Depth8Spec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth8Forward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct Depth8Reverse ;
impl SpecMap for Depth8Forward {
    type Input = Depth8Inner ;
    type Output = Depth8Spec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        Depth8Spec::from_structural (input)
    }
}
impl SpecMap for Depth8Reverse {
    type Input = Depth8Spec ;
    type Output = Depth8Inner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `depth0`."]
# [derive (Clone, Copy)]
pub struct Depth0Fmt ;

pub type Depth0FmtSpec = Named < Mapped < U8, BiMap < Depth0Forward, Depth0Reverse >> > ;

impl Depth0Fmt {
    # [doc = "specification constructor for `depth0`."] pub open spec fn spec_inner() -> Depth0FmtSpec {
        Named ("depth0",
        Mapped {
            inner: U8,
            mapper: BiMap (Depth0Forward,
            Depth0Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `depth1`."]
# [derive (Clone, Copy)]
pub struct Depth1Fmt ;

pub type Depth1FmtSpec = Named < Mapped < Depth0Fmt, BiMap < Depth1Forward, Depth1Reverse >> > ;

impl Depth1Fmt {
    # [doc = "specification constructor for `depth1`."] pub open spec fn spec_inner() -> Depth1FmtSpec {
        Named ("depth1",
        Mapped {
            inner: Depth0Fmt,
            mapper: BiMap (Depth1Forward,
            Depth1Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `depth2`."]
# [derive (Clone, Copy)]
pub struct Depth2Fmt ;

pub type Depth2FmtSpec = Named < Mapped < Depth1Fmt, BiMap < Depth2Forward, Depth2Reverse >> > ;

impl Depth2Fmt {
    # [doc = "specification constructor for `depth2`."] pub open spec fn spec_inner() -> Depth2FmtSpec {
        Named ("depth2",
        Mapped {
            inner: Depth1Fmt,
            mapper: BiMap (Depth2Forward,
            Depth2Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `depth3`."]
# [derive (Clone, Copy)]
pub struct Depth3Fmt ;

pub type Depth3FmtSpec = Named < Mapped < Depth2Fmt, BiMap < Depth3Forward, Depth3Reverse >> > ;

impl Depth3Fmt {
    # [doc = "specification constructor for `depth3`."] pub open spec fn spec_inner() -> Depth3FmtSpec {
        Named ("depth3",
        Mapped {
            inner: Depth2Fmt,
            mapper: BiMap (Depth3Forward,
            Depth3Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `depth4`."]
# [derive (Clone, Copy)]
pub struct Depth4Fmt ;

pub type Depth4FmtSpec = Named < Mapped < Depth3Fmt, BiMap < Depth4Forward, Depth4Reverse >> > ;

impl Depth4Fmt {
    # [doc = "specification constructor for `depth4`."] pub open spec fn spec_inner() -> Depth4FmtSpec {
        Named ("depth4",
        Mapped {
            inner: Depth3Fmt,
            mapper: BiMap (Depth4Forward,
            Depth4Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `depth5`."]
# [derive (Clone, Copy)]
pub struct Depth5Fmt ;

pub type Depth5FmtSpec = Named < Mapped < Depth4Fmt, BiMap < Depth5Forward, Depth5Reverse >> > ;

impl Depth5Fmt {
    # [doc = "specification constructor for `depth5`."] pub open spec fn spec_inner() -> Depth5FmtSpec {
        Named ("depth5",
        Mapped {
            inner: Depth4Fmt,
            mapper: BiMap (Depth5Forward,
            Depth5Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `depth6`."]
# [derive (Clone, Copy)]
pub struct Depth6Fmt ;

pub type Depth6FmtSpec = Named < Mapped < Depth5Fmt, BiMap < Depth6Forward, Depth6Reverse >> > ;

impl Depth6Fmt {
    # [doc = "specification constructor for `depth6`."] pub open spec fn spec_inner() -> Depth6FmtSpec {
        Named ("depth6",
        Mapped {
            inner: Depth5Fmt,
            mapper: BiMap (Depth6Forward,
            Depth6Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `depth7`."]
# [derive (Clone, Copy)]
pub struct Depth7Fmt ;

pub type Depth7FmtSpec = Named < Mapped < Depth6Fmt, BiMap < Depth7Forward, Depth7Reverse >> > ;

impl Depth7Fmt {
    # [doc = "specification constructor for `depth7`."] pub open spec fn spec_inner() -> Depth7FmtSpec {
        Named ("depth7",
        Mapped {
            inner: Depth6Fmt,
            mapper: BiMap (Depth7Forward,
            Depth7Reverse),
        }
        )
    }
}


# [doc = "named format combinator for `depth8`."]
# [derive (Clone, Copy)]
pub struct Depth8Fmt ;

pub type Depth8FmtSpec = Named < Mapped < Depth7Fmt, BiMap < Depth8Forward, Depth8Reverse >> > ;

impl Depth8Fmt {
    # [doc = "specification constructor for `depth8`."] pub open spec fn spec_inner() -> Depth8FmtSpec {
        Named ("depth8",
        Mapped {
            inner: Depth7Fmt,
            mapper: BiMap (Depth8Forward,
            Depth8Reverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for Depth0Fmt {
        type PVal = Depth0Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth0Fmt {
        type Val = Depth0Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth0Fmt {
        type SValue = Depth0Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth0Fmt {
        type SVal = Depth0Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth0Fmt {
        type T = Depth0Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Depth1Fmt {
        type PVal = Depth1Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth1Fmt {
        type Val = Depth1Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth1Fmt {
        type SValue = Depth1Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth1Fmt {
        type SVal = Depth1Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth1Fmt {
        type T = Depth1Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Depth2Fmt {
        type PVal = Depth2Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth2Fmt {
        type Val = Depth2Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth2Fmt {
        type SValue = Depth2Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth2Fmt {
        type SVal = Depth2Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth2Fmt {
        type T = Depth2Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Depth3Fmt {
        type PVal = Depth3Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth3Fmt {
        type Val = Depth3Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth3Fmt {
        type SValue = Depth3Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth3Fmt {
        type SVal = Depth3Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth3Fmt {
        type T = Depth3Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Depth4Fmt {
        type PVal = Depth4Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth4Fmt {
        type Val = Depth4Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth4Fmt {
        type SValue = Depth4Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth4Fmt {
        type SVal = Depth4Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth4Fmt {
        type T = Depth4Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Depth5Fmt {
        type PVal = Depth5Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth5Fmt {
        type Val = Depth5Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth5Fmt {
        type SValue = Depth5Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth5Fmt {
        type SVal = Depth5Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth5Fmt {
        type T = Depth5Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Depth6Fmt {
        type PVal = Depth6Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth6Fmt {
        type Val = Depth6Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth6Fmt {
        type SValue = Depth6Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth6Fmt {
        type SVal = Depth6Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth6Fmt {
        type T = Depth6Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Depth7Fmt {
        type PVal = Depth7Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth7Fmt {
        type Val = Depth7Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth7Fmt {
        type SValue = Depth7Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth7Fmt {
        type SVal = Depth7Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth7Fmt {
        type T = Depth7Spec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for Depth8Fmt {
        type PVal = Depth8Spec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for Depth8Fmt {
        type Val = Depth8Spec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for Depth8Fmt {
        type SValue = Depth8Spec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for Depth8Fmt {
        type SVal = Depth8Spec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for Depth8Fmt {
        type T = Depth8Spec ;
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
        vps_lib::combinators::disjoint::disjointness_lemmas,
        Depth0Spec::lemma_from_into,
        Depth0Spec::lemma_into_from,
        Depth1Spec::lemma_from_into,
        Depth1Spec::lemma_into_from,
        Depth2Spec::lemma_from_into,
        Depth2Spec::lemma_into_from,
        Depth3Spec::lemma_from_into,
        Depth3Spec::lemma_into_from,
        Depth4Spec::lemma_from_into,
        Depth4Spec::lemma_into_from,
        Depth5Spec::lemma_from_into,
        Depth5Spec::lemma_into_from,
        Depth6Spec::lemma_from_into,
        Depth6Spec::lemma_into_from,
        Depth7Spec::lemma_from_into,
        Depth7Spec::lemma_into_from,
        Depth8Spec::lemma_from_into,
        Depth8Spec::lemma_into_from,
    };

    impl SafeParser for Depth0Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth0Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth0Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth0Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth0Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth0Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth0Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth0Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth0Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth0Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth0Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth0Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth0Fmt as Consistency>::consistent) ;
            reveal(< Depth0Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth0Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth0Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth0Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth0Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth0Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth0Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth0Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth0Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth0Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth0Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Depth1Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth1Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth1Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth1Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth1Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth1Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth1Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth1Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth1Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth1Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth1Fmt as Consistency>::consistent) ;
            reveal(< Depth1Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth1Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth1Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth1Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth1Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth1Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth1Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth1Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth1Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth1Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth1Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Depth2Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth2Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth2Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth2Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth2Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth2Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth2Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth2Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth2Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth2Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth2Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth2Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth2Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth2Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth2Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth2Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth2Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth2Fmt as Consistency>::consistent) ;
            reveal(< Depth2Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth2Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth2Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth2Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth2Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth2Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth2Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth2Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth2Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth2Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth2Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth2Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Depth3Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth3Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth3Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth3Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth3Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth3Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth3Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth3Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth3Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth3Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth3Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth3Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth3Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth3Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth3Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth3Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth3Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth3Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth3Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth3Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth3Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth3Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth3Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth3Fmt as Consistency>::consistent) ;
            reveal(< Depth3Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth3Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth3Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth3Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth3Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth3Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth3Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth3Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth3Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth3Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth3Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth3Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth3Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Depth4Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth4Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth4Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth4Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth4Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth4Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth4Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth4Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth4Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth4Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth4Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth4Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth4Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth4Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth4Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth4Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth4Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth4Fmt as Consistency>::consistent) ;
            reveal(< Depth4Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth4Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth4Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth4Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth4Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth4Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth4Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth4Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth4Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth4Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth4Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth4Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Depth5Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth5Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth5Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth5Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth5Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth5Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth5Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth5Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth5Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth5Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth5Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth5Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth5Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth5Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth5Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth5Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth5Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth5Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth5Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth5Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth5Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth5Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth5Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth5Fmt as Consistency>::consistent) ;
            reveal(< Depth5Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth5Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth5Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth5Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth5Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth5Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth5Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth5Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth5Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth5Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth5Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth5Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth5Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Depth6Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth6Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth6Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth6Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth6Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth6Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth6Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth6Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth6Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth6Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth6Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth6Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth6Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth6Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth6Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth6Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth6Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth6Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth6Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth6Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth6Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth6Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth6Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth6Fmt as Consistency>::consistent) ;
            reveal(< Depth6Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth6Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth6Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth6Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth6Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth6Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth6Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth6Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth6Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth6Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth6Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth6Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth6Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Depth7Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth7Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth7Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth7Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth7Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth7Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth7Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth7Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth7Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth7Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth7Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth7Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth7Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth7Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth7Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth7Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth7Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth7Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth7Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth7Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth7Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth7Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth7Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth7Fmt as Consistency>::consistent) ;
            reveal(< Depth7Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth7Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth7Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth7Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth7Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth7Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth7Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth7Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth7Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth7Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth7Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth7Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth7Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for Depth8Fmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth8Fmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for Depth8Fmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< Depth8Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for Depth8Fmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth8Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth8Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth8Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< Depth8Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth8Fmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth8Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth8Spec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for Depth8Fmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< Depth8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for Depth8Fmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< Depth8Fmt as SpecSerializer>::spec_serialize) ;
            reveal(< Depth8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for Depth8Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< Depth8Fmt as SpecParser>::spec_parse) ;
            reveal(< Depth8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth8Fmt as Consistency>::consistent) ;
            reveal(< Depth8Fmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: Depth8Spec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                Depth8Spec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for Depth8Fmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< Depth8Fmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: Depth8Inner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                Depth8Spec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for Depth8Fmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< Depth8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth8Fmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for Depth8Fmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< Depth8Fmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< Depth8Fmt as SpecSerializer>::spec_serialize) ;
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

    impl<'i> Parser<&'i [u8]> for Depth0Fmt {
        type PT = Depth0;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth0Fmt as SpecParser>::spec_parse);
            reveal(<Depth0 as DeepView>::deep_view);
            reveal(Depth0Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (U8).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth0 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth0> for Depth0Fmt {
        fn serialize_into(&self, v: &Depth0, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;
            reveal(<Depth0Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth0Fmt as SpecByteLen>::byte_len);
            reveal(<Depth0 as DeepView>::deep_view);
            reveal(Depth0Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth0 {
                value,
            } = v;
            U8.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth0> for Depth0Fmt {
        fn prepare(&self, v: &Depth0) -> Result<usize, PreSerializeError> {
            reveal(<Depth0Fmt as SpecByteLen>::byte_len);
            reveal(<Depth0 as DeepView>::deep_view);
            reveal(Depth0Spec::into_structural);
            let Depth0 {
                value,
            } = v;
            let l1 = (U8).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Depth1Fmt {
        type PT = Depth1;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth1Fmt as SpecParser>::spec_parse);
            reveal(<Depth1 as DeepView>::deep_view);
            reveal(Depth1Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named ("depth0", Depth0Fmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth1 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth1> for Depth1Fmt {
        fn serialize_into(&self, v: &Depth1, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;
            reveal(<Depth1Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth1Fmt as SpecByteLen>::byte_len);
            reveal(<Depth1 as DeepView>::deep_view);
            reveal(Depth1Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth1 {
                value,
            } = v;
            Depth0Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth1> for Depth1Fmt {
        fn prepare(&self, v: &Depth1) -> Result<usize, PreSerializeError> {
            reveal(<Depth1Fmt as SpecByteLen>::byte_len);
            reveal(<Depth1 as DeepView>::deep_view);
            reveal(Depth1Spec::into_structural);
            let Depth1 {
                value,
            } = v;
            let l1 = (Named ("depth0", Depth0Fmt)).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Depth2Fmt {
        type PT = Depth2;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth2Fmt as SpecParser>::spec_parse);
            reveal(<Depth2 as DeepView>::deep_view);
            reveal(Depth2Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named ("depth1", Depth1Fmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth2 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth2> for Depth2Fmt {
        fn serialize_into(&self, v: &Depth2, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;
            reveal(<Depth2Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth2Fmt as SpecByteLen>::byte_len);
            reveal(<Depth2 as DeepView>::deep_view);
            reveal(Depth2Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth2 {
                value,
            } = v;
            Depth1Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth2> for Depth2Fmt {
        fn prepare(&self, v: &Depth2) -> Result<usize, PreSerializeError> {
            reveal(<Depth2Fmt as SpecByteLen>::byte_len);
            reveal(<Depth2 as DeepView>::deep_view);
            reveal(Depth2Spec::into_structural);
            let Depth2 {
                value,
            } = v;
            let l1 = (Named ("depth1", Depth1Fmt)).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Depth3Fmt {
        type PT = Depth3;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth3Fmt as SpecParser>::spec_parse);
            reveal(<Depth3 as DeepView>::deep_view);
            reveal(Depth3Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named ("depth2", Depth2Fmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth3 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth3> for Depth3Fmt {
        fn serialize_into(&self, v: &Depth3, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;
            reveal(<Depth3Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth3Fmt as SpecByteLen>::byte_len);
            reveal(<Depth3 as DeepView>::deep_view);
            reveal(Depth3Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth3 {
                value,
            } = v;
            Depth2Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth3> for Depth3Fmt {
        fn prepare(&self, v: &Depth3) -> Result<usize, PreSerializeError> {
            reveal(<Depth3Fmt as SpecByteLen>::byte_len);
            reveal(<Depth3 as DeepView>::deep_view);
            reveal(Depth3Spec::into_structural);
            let Depth3 {
                value,
            } = v;
            let l1 = (Named ("depth2", Depth2Fmt)).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Depth4Fmt {
        type PT = Depth4;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth4Fmt as SpecParser>::spec_parse);
            reveal(<Depth4 as DeepView>::deep_view);
            reveal(Depth4Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named ("depth3", Depth3Fmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth4 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth4> for Depth4Fmt {
        fn serialize_into(&self, v: &Depth4, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;
            reveal(<Depth4Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth4Fmt as SpecByteLen>::byte_len);
            reveal(<Depth4 as DeepView>::deep_view);
            reveal(Depth4Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth4 {
                value,
            } = v;
            Depth3Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth4> for Depth4Fmt {
        fn prepare(&self, v: &Depth4) -> Result<usize, PreSerializeError> {
            reveal(<Depth4Fmt as SpecByteLen>::byte_len);
            reveal(<Depth4 as DeepView>::deep_view);
            reveal(Depth4Spec::into_structural);
            let Depth4 {
                value,
            } = v;
            let l1 = (Named ("depth3", Depth3Fmt)).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Depth5Fmt {
        type PT = Depth5;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth5Fmt as SpecParser>::spec_parse);
            reveal(<Depth5 as DeepView>::deep_view);
            reveal(Depth5Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named ("depth4", Depth4Fmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth5 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth5> for Depth5Fmt {
        fn serialize_into(&self, v: &Depth5, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;
            reveal(<Depth5Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth5Fmt as SpecByteLen>::byte_len);
            reveal(<Depth5 as DeepView>::deep_view);
            reveal(Depth5Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth5 {
                value,
            } = v;
            Depth4Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth5> for Depth5Fmt {
        fn prepare(&self, v: &Depth5) -> Result<usize, PreSerializeError> {
            reveal(<Depth5Fmt as SpecByteLen>::byte_len);
            reveal(<Depth5 as DeepView>::deep_view);
            reveal(Depth5Spec::into_structural);
            let Depth5 {
                value,
            } = v;
            let l1 = (Named ("depth4", Depth4Fmt)).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Depth6Fmt {
        type PT = Depth6;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth6Fmt as SpecParser>::spec_parse);
            reveal(<Depth6 as DeepView>::deep_view);
            reveal(Depth6Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named ("depth5", Depth5Fmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth6 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth6> for Depth6Fmt {
        fn serialize_into(&self, v: &Depth6, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;
            reveal(<Depth6Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth6Fmt as SpecByteLen>::byte_len);
            reveal(<Depth6 as DeepView>::deep_view);
            reveal(Depth6Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth6 {
                value,
            } = v;
            Depth5Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth6> for Depth6Fmt {
        fn prepare(&self, v: &Depth6) -> Result<usize, PreSerializeError> {
            reveal(<Depth6Fmt as SpecByteLen>::byte_len);
            reveal(<Depth6 as DeepView>::deep_view);
            reveal(Depth6Spec::into_structural);
            let Depth6 {
                value,
            } = v;
            let l1 = (Named ("depth5", Depth5Fmt)).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Depth7Fmt {
        type PT = Depth7;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth7Fmt as SpecParser>::spec_parse);
            reveal(<Depth7 as DeepView>::deep_view);
            reveal(Depth7Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named ("depth6", Depth6Fmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth7 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth7> for Depth7Fmt {
        fn serialize_into(&self, v: &Depth7, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;
            reveal(<Depth7Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth7Fmt as SpecByteLen>::byte_len);
            reveal(<Depth7 as DeepView>::deep_view);
            reveal(Depth7Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth7 {
                value,
            } = v;
            Depth6Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth7> for Depth7Fmt {
        fn prepare(&self, v: &Depth7) -> Result<usize, PreSerializeError> {
            reveal(<Depth7Fmt as SpecByteLen>::byte_len);
            reveal(<Depth7 as DeepView>::deep_view);
            reveal(Depth7Spec::into_structural);
            let Depth7 {
                value,
            } = v;
            let l1 = (Named ("depth6", Depth6Fmt)).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for Depth8Fmt {
        type PT = Depth8;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vps_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vps_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<Depth8Fmt as SpecParser>::spec_parse);
            reveal(<Depth8 as DeepView>::deep_view);
            reveal(Depth8Spec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, value) = (Named ("depth7", Depth7Fmt)).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = Depth8 {
                value,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, Depth8> for Depth8Fmt {
        fn serialize_into(&self, v: &Depth8, obuf: &mut Output) {
            broadcast use vps_lib::core::exec::output::outbuf_lemmas;
            reveal(<Depth8Fmt as SpecSerializer>::spec_serialize);
            reveal(<Depth8Fmt as SpecByteLen>::byte_len);
            reveal(<Depth8 as DeepView>::deep_view);
            reveal(Depth8Spec::into_structural);
            let ghost old_obuf = obuf@;

            let Depth8 {
                value,
            } = v;
            Depth7Fmt.serialize_into(value, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<Depth8> for Depth8Fmt {
        fn prepare(&self, v: &Depth8) -> Result<usize, PreSerializeError> {
            reveal(<Depth8Fmt as SpecByteLen>::byte_len);
            reveal(<Depth8 as DeepView>::deep_view);
            reveal(Depth8Spec::into_structural);
            let Depth8 {
                value,
            } = v;
            let l1 = (Named ("depth7", Depth7Fmt)).prepare (value) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }

}
}
