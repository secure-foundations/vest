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
# [doc = "data type for `tlv_kind`."]
# [repr (u8)]
# [derive (Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
pub enum TlvKind {
    Ping = 1,
    Data = 2,
    Addr = 3,
}
pub type TlvKindSpec = TlvKind ;
pub type TlvKindInner = u8 ;
impl DeepView for TlvKind {
    type V = Self ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        * self
    }
}
impl TlvKind {
    pub proof fn lemma_deep_view (& self) ensures self.deep_view() == * self,
    {
        reveal(< TlvKind as DeepView>::deep_view) ;
    }
    pub open spec fn structural_valid (input: TlvKindInner) -> bool {
        {
            let x = input ;
            x == 1 || x == 2 || x == 3
        }
    }
    # [verifier::opaque] pub open spec fn from_structural (input: TlvKindInner) -> Self {
        match input {
            1 => Self::Ping,
            2 => Self::Data,
            3 => Self::Addr,
            _ => arbitrary(),
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> TlvKindInner {
        match self {
            Self::Ping => 1,
            Self::Data => 2,
            Self::Addr => 3,
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TlvKind::from_structural) ;
        reveal(TlvKind::into_structural) ;
        match self {
            Self::Ping => {
            }
           ,
            Self::Data => {
            }
           ,
            Self::Addr => {
            }
           ,
        }
    }
    pub broadcast proof fn lemma_into_from (input: TlvKindInner) requires Self::structural_valid (input),
    ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TlvKind::from_structural) ;
        reveal(TlvKind::into_structural) ;
        match input {
            1 => {
            }
           ,
            2 => {
            }
           ,
            3 => {
            }
           ,
            _ => {
                assert (false) ;
            }
        }
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvKindForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvKindReverse ;
impl SpecMap for TlvKindForward {
    type Input = TlvKindInner ;
    type Output = TlvKindSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TlvKind::from_structural (input)
    }
}
impl SpecMap for TlvKindReverse {
    type Input = TlvKindSpec ;
    type Output = TlvKindInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}
# [cfg (not (verus_keep_ghost))] unsafe impl Structural for TlvKind {
}

# [doc = "data type for `tlv_ping`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct TlvPing {
    pub nonce: u64,
}
# [verifier::ext_equal]
pub struct TlvPingSpec < T0 = u64 > {
    pub nonce: T0,
}
pub type TlvPingInner = u64 ;
impl DeepView for TlvPing {
    type V = TlvPingSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        TlvPingSpec {
            nonce: self.nonce.deep_view(),
        }
    }
}
impl TlvPing {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().nonce == self.nonce.deep_view(),
    {
        reveal(< TlvPing as DeepView>::deep_view) ;
    }
}
impl < T0 > TlvPingSpec < T0 > {
    # [verifier::opaque] pub open spec fn from_structural (input: T0) -> Self {
        let nonce = input ;
        Self {
            nonce
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> T0 {
        let Self {
            nonce
        }
        = self ;
        nonce
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TlvPingSpec::from_structural) ;
        reveal(TlvPingSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: T0) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TlvPingSpec::from_structural) ;
        reveal(TlvPingSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            nonce
        }
        => nonce,
    }
   ,
    {
        reveal(TlvPingSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvPingForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvPingReverse ;
impl SpecMap for TlvPingForward {
    type Input = TlvPingInner ;
    type Output = TlvPingSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TlvPingSpec::from_structural (input)
    }
}
impl SpecMap for TlvPingReverse {
    type Input = TlvPingSpec ;
    type Output = TlvPingInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `tlv_data`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct TlvData<'i> {
    pub seq: u32,
    pub body: &'i [u8],
}
# [verifier::ext_equal]
pub struct TlvDataSpec < T0 = u32, T1 = Seq < u8 > > {
    pub seq: T0,
    pub body: T1,
}
pub type TlvDataInner = (u32, Seq < u8 >) ;
impl<'i> DeepView for TlvData<'i> {
    type V = TlvDataSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        TlvDataSpec {
            seq: self.seq.deep_view(),
            body: self.body.deep_view(),
        }
    }
}
impl<'i> TlvData<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().seq == self.seq.deep_view(),
    self.deep_view().body == self.body.deep_view(),
    {
        reveal(< TlvData as DeepView>::deep_view) ;
    }
}
impl < T0, T1 > TlvDataSpec < T0, T1 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    T1)) -> Self {
        let (seq,
        body) = input ;
        Self {
            seq,
            body
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    T1) {
        let Self {
            seq,
            body
        }
        = self ;
        (seq,
        body)
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TlvDataSpec::from_structural) ;
        reveal(TlvDataSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    T1)) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TlvDataSpec::from_structural) ;
        reveal(TlvDataSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            seq,
            body
        }
        => (seq,
        body),
    }
   ,
    {
        reveal(TlvDataSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvDataForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvDataReverse ;
impl SpecMap for TlvDataForward {
    type Input = TlvDataInner ;
    type Output = TlvDataSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TlvDataSpec::from_structural (input)
    }
}
impl SpecMap for TlvDataReverse {
    type Input = TlvDataSpec ;
    type Output = TlvDataInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `tlv_addr`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct TlvAddr<'i> {
    pub host: &'i [u8],
    pub port: u16,
}
# [verifier::ext_equal]
pub struct TlvAddrSpec < T0 = Seq < u8 >, T1 = u16 > {
    pub host: T0,
    pub port: T1,
}
pub type TlvAddrInner = (Seq < u8 >, u16) ;
impl<'i> DeepView for TlvAddr<'i> {
    type V = TlvAddrSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        TlvAddrSpec {
            host: self.host.deep_view(),
            port: self.port.deep_view(),
        }
    }
}
impl<'i> TlvAddr<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().host == self.host.deep_view(),
    self.deep_view().port == self.port.deep_view(),
    {
        reveal(< TlvAddr as DeepView>::deep_view) ;
    }
}
impl < T0, T1 > TlvAddrSpec < T0, T1 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    T1)) -> Self {
        let (host,
        port) = input ;
        Self {
            host,
            port
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    T1) {
        let Self {
            host,
            port
        }
        = self ;
        (host,
        port)
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TlvAddrSpec::from_structural) ;
        reveal(TlvAddrSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    T1)) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TlvAddrSpec::from_structural) ;
        reveal(TlvAddrSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            host,
            port
        }
        => (host,
        port),
    }
   ,
    {
        reveal(TlvAddrSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvAddrForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvAddrReverse ;
impl SpecMap for TlvAddrForward {
    type Input = TlvAddrInner ;
    type Output = TlvAddrSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TlvAddrSpec::from_structural (input)
    }
}
impl SpecMap for TlvAddrReverse {
    type Input = TlvAddrSpec ;
    type Output = TlvAddrInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `tlv_msg`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub struct TlvMsg<'i> {
    pub kind: TlvKind,
    pub len: u16,
    pub body: TlvMsgBody<'i>,
}
# [verifier::ext_equal]
pub struct TlvMsgSpec < T0 = TlvKindSpec, T1 = u16, T2 = TlvMsgBodySpec > {
    pub kind: T0,
    pub len: T1,
    pub body: T2,
}
pub type TlvMsgInner = (TlvKindSpec, (u16, TlvMsgBodySpec)) ;
impl<'i> DeepView for TlvMsg<'i> {
    type V = TlvMsgSpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        TlvMsgSpec {
            kind: self.kind.deep_view(),
            len: self.len.deep_view(),
            body: self.body.deep_view(),
        }
    }
}
impl<'i> TlvMsg<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view().kind == self.kind.deep_view(),
    self.deep_view().len == self.len.deep_view(),
    self.deep_view().body == self.body.deep_view(),
    {
        reveal(< TlvMsg as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > TlvMsgSpec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: (T0,
    (T1,
    T2))) -> Self {
        let (kind,
        (len,
        body)) = input ;
        Self {
            kind,
            len,
            body
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> (T0,
    (T1,
    T2)) {
        let Self {
            kind,
            len,
            body
        }
        = self ;
        (kind,
        (len,
        body))
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TlvMsgSpec::from_structural) ;
        reveal(TlvMsgSpec::into_structural) ;
    }
    pub broadcast proof fn lemma_into_from (input: (T0,
    (T1,
    T2))) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TlvMsgSpec::from_structural) ;
        reveal(TlvMsgSpec::into_structural) ;
    }
    pub proof fn lemma_into_structural_fields (self) ensures Self::into_structural (self) == match self {
        Self {
            kind,
            len,
            body
        }
        => (kind,
        (len,
        body)),
    }
   ,
    {
        reveal(TlvMsgSpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvMsgForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvMsgReverse ;
impl SpecMap for TlvMsgForward {
    type Input = TlvMsgInner ;
    type Output = TlvMsgSpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TlvMsgSpec::from_structural (input)
    }
}
impl SpecMap for TlvMsgReverse {
    type Input = TlvMsgSpec ;
    type Output = TlvMsgInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

# [doc = "data type for `tlv_msg_body`."]
# [derive (Debug, PartialEq, Eq, Clone, Copy)]
pub enum TlvMsgBody<'i> {
    Ping (TlvPing),
    Data (TlvData<'i>),
    Addr (TlvAddr<'i>),
}
# [verifier::ext_equal]
pub enum TlvMsgBodySpec < T0 = TlvPingSpec, T1 = TlvDataSpec, T2 = TlvAddrSpec > {
    Ping (T0),
    Data (T1),
    Addr (T2),
}
pub type TlvMsgBodyInner = Sum < TlvPingSpec, Sum < TlvDataSpec, TlvAddrSpec > > ;
impl<'i> DeepView for TlvMsgBody<'i> {
    type V = TlvMsgBodySpec ;
    # [verifier::opaque] open spec fn deep_view (& self) -> Self::V {
        match self {
            TlvMsgBody::Ping (v) => TlvMsgBodySpec::Ping (v.deep_view()),
            TlvMsgBody::Data (v) => TlvMsgBodySpec::Data (v.deep_view()),
            TlvMsgBody::Addr (v) => TlvMsgBodySpec::Addr (v.deep_view()),
        }
    }
}
impl<'i> TlvMsgBody<'i> {
    pub proof fn lemma_deep_view_fields (& self) ensures self.deep_view() == match self {
        TlvMsgBody::Ping (v) => TlvMsgBodySpec::Ping (v.deep_view()),
        TlvMsgBody::Data (v) => TlvMsgBodySpec::Data (v.deep_view()),
        TlvMsgBody::Addr (v) => TlvMsgBodySpec::Addr (v.deep_view()),
    }
   ,
    {
        reveal(< TlvMsgBody as DeepView>::deep_view) ;
    }
}
impl < T0, T1, T2 > TlvMsgBodySpec < T0, T1, T2 > {
    # [verifier::opaque] pub open spec fn from_structural (input: Sum < T0,
    Sum < T1,
    T2 > >) -> Self {
        match input {
            L (value) => Self::Ping (value),
            R (L (value)) => Self::Data (value),
            R (R (value)) => Self::Addr (value),
        }
    }
    # [verifier::opaque] pub open spec fn into_structural (self) -> Sum < T0,
    Sum < T1,
    T2 > > {
        match self {
            Self::Ping (value) => L (value),
            Self::Data (value) => R (L (value)),
            Self::Addr (value) => R (R (value)),
        }
    }
    pub broadcast proof fn lemma_from_into (self) ensures # [trigger] Self::from_structural (Self::into_structural (self)) == self,
    {
        reveal(TlvMsgBodySpec::from_structural) ;
        reveal(TlvMsgBodySpec::into_structural) ;
        match self {
            Self::Ping (_) => {
            }
           ,
            Self::Data (_) => {
            }
           ,
            Self::Addr (_) => {
            }
           ,
        }
    }
    pub broadcast proof fn lemma_into_from (input: Sum < T0,
    Sum < T1,
    T2 > >) ensures # [trigger] Self::into_structural (Self::from_structural (input)) == input,
    {
        reveal(TlvMsgBodySpec::from_structural) ;
        reveal(TlvMsgBodySpec::into_structural) ;
        match input {
            L (_) => {
            }
           ,
            R (L (_)) => {
            }
           ,
            R (R (_)) => {
            }
           ,
        }
    }
    pub proof fn lemma_into_structural_variant (self) ensures Self::into_structural (self) == match self {
        Self::Ping (value) => L (value),
        Self::Data (value) => R (L (value)),
        Self::Addr (value) => R (R (value)),
    }
   ,
    {
        reveal(TlvMsgBodySpec::into_structural) ;
    }
}
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvMsgBodyForward ;
# [derive (Clone, Copy)]
# [doc (hidden)]
pub struct TlvMsgBodyReverse ;
impl SpecMap for TlvMsgBodyForward {
    type Input = TlvMsgBodyInner ;
    type Output = TlvMsgBodySpec ;
    open spec fn spec_map (& self,
    input: Self::Input) -> Self::Output {
        TlvMsgBodySpec::from_structural (input)
    }
}
impl SpecMap for TlvMsgBodyReverse {
    type Input = TlvMsgBodySpec ;
    type Output = TlvMsgBodyInner ;
    open spec fn spec_map (& self,
    value: Self::Input) -> Self::Output {
        value.into_structural()
    }
}

// ============================================================
// Format Specifications
// ============================================================
# [doc = "named format combinator for `tlv_kind`."]
# [derive (Clone, Copy)]
pub struct TlvKindFmt ;

pub type TlvKindFmtSpec = Named < Mapped < Refined < U8, PredFnSpec < u8 >>, BiMap < TlvKindForward, TlvKindReverse >> > ;

impl TlvKindFmt {
    # [doc = "specification constructor for `tlv_kind`."] pub open spec fn spec_inner() -> TlvKindFmtSpec {
        Named ("tlv_kind",
        Mapped {
            inner: Refined (U8,
            | x: u8 | ((x == 1) || (x == 2)) || (x == 3)),
            mapper: BiMap (TlvKindForward,
            TlvKindReverse),
        }
        )
    }
}


# [doc = "named format combinator for `tlv_ping`."]
# [derive (Clone, Copy)]
pub struct TlvPingFmt ;

pub type TlvPingFmtSpec = Named < Mapped < U64Be, BiMap < TlvPingForward, TlvPingReverse >> > ;

impl TlvPingFmt {
    # [doc = "specification constructor for `tlv_ping`."] pub open spec fn spec_inner() -> TlvPingFmtSpec {
        Named ("tlv_ping",
        Mapped {
            inner: U64Be,
            mapper: BiMap (TlvPingForward,
            TlvPingReverse),
        }
        )
    }
}


# [doc = "named format combinator for `tlv_data`."]
# [derive (Clone, Copy)]
pub struct TlvDataFmt ;

pub type TlvDataFmtSpec = Named < Mapped < Pair < U32Be, Tail >, BiMap < TlvDataForward, TlvDataReverse >> > ;

impl TlvDataFmt {
    # [doc = "specification constructor for `tlv_data`."] pub open spec fn spec_inner() -> TlvDataFmtSpec {
        Named ("tlv_data",
        Mapped {
            inner: Pair (U32Be,
            Tail),
            mapper: BiMap (TlvDataForward,
            TlvDataReverse),
        }
        )
    }
}


# [doc = "named format combinator for `tlv_addr`."]
# [derive (Clone, Copy)]
pub struct TlvAddrFmt ;

pub type TlvAddrFmtSpec = Named < Mapped < Pair < Fixed < 4 >, U16Be >, BiMap < TlvAddrForward, TlvAddrReverse >> > ;

impl TlvAddrFmt {
    # [doc = "specification constructor for `tlv_addr`."] pub open spec fn spec_inner() -> TlvAddrFmtSpec {
        Named ("tlv_addr",
        Mapped {
            inner: Pair (Fixed::< 4 >,
            U16Be),
            mapper: BiMap (TlvAddrForward,
            TlvAddrReverse),
        }
        )
    }
}


# [doc = "named format combinator for `tlv_msg`."]
# [derive (Clone, Copy)]
pub struct TlvMsgFmt ;

pub type TlvMsgFmtSpec = Named < Mapped < Bind < TlvKindFmt, spec_fn (TlvKindSpec) -> Bind < U16Be, spec_fn (u16) -> ExactLen < TlvMsgBodyFmt, u16 > > >, BiMap < TlvMsgForward, TlvMsgReverse >> > ;

impl TlvMsgFmt {
    # [doc = "specification constructor for `tlv_msg`."] pub open spec fn spec_inner() -> TlvMsgFmtSpec {
        Named ("tlv_msg",
        Mapped {
            inner: Bind (TlvKindFmt,
            | kind: TlvKindSpec | Bind (U16Be,
            | len: u16 | ExactLen (len,
            TlvMsgBodyFmt::spec (kind)))),
            mapper: BiMap (TlvMsgForward,
            TlvMsgReverse),
        }
        )
    }
}


# [doc = "named format combinator for `tlv_msg_body`."]
# [derive (Clone, Copy)]
pub struct TlvMsgBodyFmt {
    kind: TlvKind,
}
impl TlvMsgBodyFmt {
    # [verifier::type_invariant] spec fn wf (& self) -> bool {
        TlvKindFmt.consistent (self.kind.deep_view())
    }
    pub closed spec fn kind_spec (& self) -> TlvKindSpec {
        self.kind.deep_view()
    }
    pub closed spec fn spec (kind: TlvKind) -> Self {
        TlvMsgBodyFmt {
            kind
        }
    }
}

pub type TlvMsgBodyFmtSpec = Named < Mapped < Sum < TlvPingFmt, Sum < TlvDataFmt, TlvAddrFmt > >, BiMap < TlvMsgBodyForward, TlvMsgBodyReverse >> > ;

impl TlvMsgBodyFmt {
    # [doc = "specification constructor for `tlv_msg_body`."] pub open spec fn spec_inner (kind: TlvKindSpec) -> TlvMsgBodyFmtSpec {
        Named ("tlv_msg_body",
        Mapped {
            inner: match kind {
                TlvKindSpec::Ping => L (TlvPingFmt),
                TlvKindSpec::Data => R (L (TlvDataFmt)),
                TlvKindSpec::Addr => R (R (TlvAddrFmt)),
            }
           ,
            mapper: BiMap (TlvMsgBodyForward,
            TlvMsgBodyReverse),
        }
        )
    }
}

// ============================================================
// Derived Parser, Serializer, Length, and Consistency Specifications
// ============================================================
mod derived_specs {
    use super::*;

    impl SpecParser for TlvKindFmt {
        type PVal = TlvKindSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TlvKindFmt {
        type Val = TlvKindSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TlvKindFmt {
        type SValue = TlvKindSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TlvKindFmt {
        type SVal = TlvKindSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TlvKindFmt {
        type T = TlvKindSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for TlvPingFmt {
        type PVal = TlvPingSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TlvPingFmt {
        type Val = TlvPingSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TlvPingFmt {
        type SValue = TlvPingSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TlvPingFmt {
        type SVal = TlvPingSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TlvPingFmt {
        type T = TlvPingSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for TlvDataFmt {
        type PVal = TlvDataSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TlvDataFmt {
        type Val = TlvDataSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TlvDataFmt {
        type SValue = TlvDataSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TlvDataFmt {
        type SVal = TlvDataSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TlvDataFmt {
        type T = TlvDataSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for TlvAddrFmt {
        type PVal = TlvAddrSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TlvAddrFmt {
        type Val = TlvAddrSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TlvAddrFmt {
        type SValue = TlvAddrSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TlvAddrFmt {
        type SVal = TlvAddrSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TlvAddrFmt {
        type T = TlvAddrSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for TlvMsgFmt {
        type PVal = TlvMsgSpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner().spec_parse (ibuf)
        }
    }
    impl Consistency for TlvMsgFmt {
        type Val = TlvMsgSpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner().consistent (v)
        }
    }
    impl SpecSerializerDps for TlvMsgFmt {
        type SValue = TlvMsgSpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner().spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TlvMsgFmt {
        type SVal = TlvMsgSpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner().spec_serialize (v)
        }
    }
    impl SpecByteLen for TlvMsgFmt {
        type T = TlvMsgSpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner().byte_len (v)
        }
    }

    impl SpecParser for TlvMsgBodyFmt {
        type PVal = TlvMsgBodySpec ;
        # [verifier::opaque] open spec fn spec_parse (& self,
        ibuf: Seq < u8 >) -> Option < (int,
        Self::PVal) > {
            Self::spec_inner (self.kind_spec()).spec_parse (ibuf)
        }
    }
    impl Consistency for TlvMsgBodyFmt {
        type Val = TlvMsgBodySpec ;
        open spec fn consistent (& self,
        v: Self::Val) -> bool {
            Self::spec_inner (self.kind_spec()).consistent (v)
        }
    }
    impl SpecSerializerDps for TlvMsgBodyFmt {
        type SValue = TlvMsgBodySpec ;
        # [verifier::opaque] open spec fn spec_serialize_dps (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) -> Seq < u8 > {
            Self::spec_inner (self.kind_spec()).spec_serialize_dps (v,
            obuf)
        }
    }
    impl SpecSerializer for TlvMsgBodyFmt {
        type SVal = TlvMsgBodySpec ;
        # [verifier::opaque] open spec fn spec_serialize (& self,
        v: Self::SVal) -> Seq < u8 > {
            Self::spec_inner (self.kind_spec()).spec_serialize (v)
        }
    }
    impl SpecByteLen for TlvMsgBodyFmt {
        type T = TlvMsgBodySpec ;
        # [verifier::opaque] open spec fn byte_len (& self,
        v: Self::T) -> nat {
            Self::spec_inner (self.kind_spec()).byte_len (v)
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
        TlvKind::lemma_from_into,
        TlvKind::lemma_into_from,
        TlvPingSpec::lemma_from_into,
        TlvPingSpec::lemma_into_from,
        TlvDataSpec::lemma_from_into,
        TlvDataSpec::lemma_into_from,
        TlvAddrSpec::lemma_from_into,
        TlvAddrSpec::lemma_into_from,
        TlvMsgSpec::lemma_from_into,
        TlvMsgSpec::lemma_into_from,
        TlvMsgBodySpec::lemma_from_into,
        TlvMsgBodySpec::lemma_into_from,
    };

    impl SafeParser for TlvKindFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvKindFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TlvKindFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TlvKindFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TlvKindFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvKindFmt as SpecParser>::spec_parse) ;
            reveal(< TlvKindFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvKindInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                assert (TlvKind::structural_valid (input)) ;
                TlvKind::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvKindFmt as SpecParser>::spec_parse) ;
            reveal(< TlvKindFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvKindInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                assert (TlvKind::structural_valid (input)) ;
                TlvKind::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for TlvKindFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TlvKindFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TlvKindFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvKindFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for TlvKindFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TlvKindFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TlvKindFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TlvKindFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TlvKindFmt as SpecParser>::spec_parse) ;
            reveal(< TlvKindFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvKindFmt as Consistency>::consistent) ;
            reveal(< TlvKindFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: TlvKindSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TlvKind::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TlvKindFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TlvKindFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvKindInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                assert (TlvKind::structural_valid (input)) ;
                TlvKind::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for TlvKindFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< TlvKindFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvKindFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for TlvKindFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TlvKindFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvKindFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for TlvPingFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvPingFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TlvPingFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TlvPingFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TlvPingFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvPingFmt as SpecParser>::spec_parse) ;
            reveal(< TlvPingFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvPingInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvPingSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvPingFmt as SpecParser>::spec_parse) ;
            reveal(< TlvPingFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvPingInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvPingSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for TlvPingFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TlvPingFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TlvPingFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvPingFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for TlvPingFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TlvPingFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TlvPingFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TlvPingFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TlvPingFmt as SpecParser>::spec_parse) ;
            reveal(< TlvPingFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvPingFmt as Consistency>::consistent) ;
            reveal(< TlvPingFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: TlvPingSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TlvPingSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TlvPingFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TlvPingFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvPingInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvPingSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for TlvPingFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< TlvPingFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvPingFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for TlvPingFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TlvPingFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvPingFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for TlvDataFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvDataFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TlvDataFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TlvDataFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TlvDataFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvDataFmt as SpecParser>::spec_parse) ;
            reveal(< TlvDataFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvDataInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvDataSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvDataFmt as SpecParser>::spec_parse) ;
            reveal(< TlvDataFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvDataInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvDataSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl GoodSerializer for TlvDataFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TlvDataFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TlvDataFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TlvDataFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TlvDataFmt as SpecParser>::spec_parse) ;
            reveal(< TlvDataFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvDataFmt as Consistency>::consistent) ;
            reveal(< TlvDataFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: TlvDataSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TlvDataSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TlvDataFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TlvDataFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvDataInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvDataSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializers for TlvDataFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TlvDataFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvDataFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for TlvAddrFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvAddrFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TlvAddrFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TlvAddrFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TlvAddrFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvAddrFmt as SpecParser>::spec_parse) ;
            reveal(< TlvAddrFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvAddrInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvAddrSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvAddrFmt as SpecParser>::spec_parse) ;
            reveal(< TlvAddrFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvAddrInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvAddrSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for TlvAddrFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TlvAddrFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TlvAddrFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvAddrFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for TlvAddrFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TlvAddrFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TlvAddrFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TlvAddrFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TlvAddrFmt as SpecParser>::spec_parse) ;
            reveal(< TlvAddrFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvAddrFmt as Consistency>::consistent) ;
            reveal(< TlvAddrFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: TlvAddrSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TlvAddrSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TlvAddrFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TlvAddrFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvAddrInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvAddrSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for TlvAddrFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< TlvAddrFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvAddrFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for TlvAddrFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TlvAddrFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvAddrFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for TlvMsgFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvMsgFmt as SpecParser>::spec_parse) ;
            Self::spec_inner().lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TlvMsgFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner().productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TlvMsgFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TlvMsgFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvMsgFmt as SpecParser>::spec_parse) ;
            reveal(< TlvMsgFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvMsgInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvMsgSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvMsgFmt as SpecParser>::spec_parse) ;
            reveal(< TlvMsgFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvMsgInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvMsgSpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl NonTailFmt for TlvMsgFmt {
        proof fn lemma_serialize_dps_prepend (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TlvMsgFmt as SpecSerializerDps>::spec_serialize_dps) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_prepend (v,
            obuf) ;
        }
        proof fn lemma_serialize_dps_len (& self,
        v: Self::SValue,
        obuf: Seq < u8 >) {
            reveal(< TlvMsgFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvMsgFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_dps_inv()) ;
            fmt.lemma_serialize_dps_len (v,
            obuf) ;
        }
    }
    impl GoodSerializer for TlvMsgFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TlvMsgFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TlvMsgFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TlvMsgFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TlvMsgFmt as SpecParser>::spec_parse) ;
            reveal(< TlvMsgFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvMsgFmt as Consistency>::consistent) ;
            reveal(< TlvMsgFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner() ;
            assert forall | output: TlvMsgSpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TlvMsgSpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TlvMsgFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TlvMsgFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner() ;
            assert forall | input: TlvMsgInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvMsgSpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializersGeneral for TlvMsgFmt {
        proof fn lemma_serialize_equiv (& self,
        v: Self::SVal,
        obuf: Seq < u8 >) {
            reveal(< TlvMsgFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvMsgFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_general_inv()) ;
            fmt.lemma_serialize_equiv (v,
            obuf) ;
        }
    }
    impl EquivSerializers for TlvMsgFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TlvMsgFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvMsgFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner() ;
            assert (fmt.equiv_inv()) ;
            fmt.lemma_serialize_equiv_on_empty (v) ;
        }
    }

    impl SafeParser for TlvMsgBodyFmt {
        proof fn lemma_parse_safe (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvMsgBodyFmt as SpecParser>::spec_parse) ;
            Self::spec_inner (self.kind_spec()).lemma_parse_safe (ibuf) ;
        }
    }
    impl Productive for TlvMsgBodyFmt {
        open spec fn productive_inv (& self) -> bool {
            Self::spec_inner (self.kind_spec()).productive_inv()
        }
        proof fn lemma_productive (& self,
        s: Seq < u8 >) {
            reveal(< TlvMsgBodyFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner (self.kind_spec()) ;
            assert (fmt.productive_inv()) ;
            fmt.lemma_productive (s) ;
        }
    }
    impl SoundParser for TlvMsgBodyFmt {
        proof fn lemma_parse_sound_consumption (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvMsgBodyFmt as SpecParser>::spec_parse) ;
            reveal(< TlvMsgBodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.kind_spec()) ;
            assert forall | input: TlvMsgBodyInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvMsgBodySpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_consumption (ibuf) ;
        }
        proof fn lemma_parse_sound_value (& self,
        ibuf: Seq < u8 >) {
            reveal(< TlvMsgBodyFmt as SpecParser>::spec_parse) ;
            reveal(< TlvMsgBodyFmt as Consistency>::consistent) ;
            let fmt = Self::spec_inner (self.kind_spec()) ;
            assert forall | input: TlvMsgBodyInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvMsgBodySpec::lemma_into_from (input) ;
            }
            assert (fmt.sound_inv()) ;
            fmt.lemma_parse_sound_value (ibuf) ;
        }
    }
    impl GoodSerializer for TlvMsgBodyFmt {
        proof fn lemma_serialize_len (& self,
        v: Self::SVal) {
            reveal(< TlvMsgBodyFmt as SpecSerializer>::spec_serialize) ;
            reveal(< TlvMsgBodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.kind_spec()) ;
            assert (fmt.serialize_inv()) ;
            fmt.lemma_serialize_len (v) ;
        }
    }
    impl SPRoundTripDps for TlvMsgBodyFmt {
        proof fn theorem_serialize_dps_parse_roundtrip (& self,
        v: Self::T,
        obuf: Seq < u8 >) {
            reveal(< TlvMsgBodyFmt as SpecParser>::spec_parse) ;
            reveal(< TlvMsgBodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvMsgBodyFmt as Consistency>::consistent) ;
            reveal(< TlvMsgBodyFmt as SpecByteLen>::byte_len) ;
            let fmt = Self::spec_inner (self.kind_spec()) ;
            assert forall | output: TlvMsgBodySpec | # [trigger] fmt.1.consistent (output) implies fmt.1.mapper.sound (output) by {
                TlvMsgBodySpec::lemma_from_into (output) ;
            }
            assert (fmt.unambiguous()) ;
            fmt.theorem_serialize_dps_parse_roundtrip (v,
            obuf) ;
        }
    }
    impl NonMalleable for TlvMsgBodyFmt {
        proof fn lemma_parse_non_malleable (& self,
        buf1: Seq < u8 >,
        buf2: Seq < u8 >) {
            reveal(< TlvMsgBodyFmt as SpecParser>::spec_parse) ;
            let fmt = Self::spec_inner (self.kind_spec()) ;
            assert forall | input: TlvMsgBodyInner | # [trigger] fmt.1.inner.consistent (input) implies fmt.1.mapper.lossless (input) by {
                TlvMsgBodySpec::lemma_into_from (input) ;
            }
            assert (fmt.nonmal_inv()) ;
            fmt.lemma_parse_non_malleable (buf1,
            buf2) ;
        }
    }
    impl EquivSerializers for TlvMsgBodyFmt {
        proof fn lemma_serialize_equiv_on_empty (& self,
        v: Self::SVal) {
            reveal(< TlvMsgBodyFmt as SpecSerializerDps>::spec_serialize_dps) ;
            reveal(< TlvMsgBodyFmt as SpecSerializer>::spec_serialize) ;
            let fmt = Self::spec_inner (self.kind_spec()) ;
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

    impl<'i> Parser<&'i [u8]> for TlvKindFmt {
        type PT = TlvKind;

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<TlvKindFmt as SpecParser>::spec_parse);
            reveal(<TlvKind as DeepView>::deep_view);
            reveal(TlvKind::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n, v) = U8.parse(&rest)?;
            let enum_val = match v {
                1 => TlvKind::Ping,
                2 => TlvKind::Data,
                3 => TlvKind::Addr,
                _ => return Err (ParseError::invalid_tag()),
            };
            assert (self.spec_parse (ibuf @) == Some ((n as int, enum_val.deep_view()))) ;
            Ok((n, enum_val))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TlvKind> for TlvKindFmt {
        fn serialize_into(&self, v: &TlvKind, obuf: &mut Output) {
            reveal(<TlvKindFmt as SpecSerializer>::spec_serialize);
            reveal(<TlvKindFmt as SpecByteLen>::byte_len);
            reveal(<TlvKind as DeepView>::deep_view);
            reveal(TlvKind::into_structural);
            let ghost old_obuf = obuf@;

            let tag = match *v {
                TlvKind::Ping => 1,
                TlvKind::Data => 2,
                TlvKind::Addr => 3,
            };
            U8.serialize_into(&tag, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TlvKind> for TlvKindFmt {
        fn prepare(&self, v: &TlvKind) -> Result<usize, PreSerializeError> {
            reveal(<TlvKindFmt as SpecByteLen>::byte_len);
            reveal(<TlvKind as DeepView>::deep_view);
            reveal(TlvKind::into_structural);
            let tag = match *v {
                TlvKind::Ping => 1,
                TlvKind::Data => 2,
                TlvKind::Addr => 3,
                _ => return Err (PreSerializeError::not_compliant (ComplianceErrorKind::InvalidTag)),
            };
            U8.prepare(&tag)
        }
    }



    impl<'i> Parser<&'i [u8]> for TlvPingFmt {
        type PT = TlvPing;

        fn min_byte_len(&self) -> usize {
            8
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TlvPingFmt as SpecParser>::spec_parse);
            reveal(<TlvPing as DeepView>::deep_view);
            reveal(TlvPingSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, nonce) = (U64Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let total_n = n1;
            let final_v = TlvPing {
                nonce,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TlvPing> for TlvPingFmt {
        fn serialize_into(&self, v: &TlvPing, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<TlvPingFmt as SpecSerializer>::spec_serialize);
            reveal(<TlvPingFmt as SpecByteLen>::byte_len);
            reveal(<TlvPing as DeepView>::deep_view);
            reveal(TlvPingSpec::into_structural);
            let ghost old_obuf = obuf@;

            let TlvPing {
                nonce,
            } = v;
            U64Be.serialize_into(nonce, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TlvPing> for TlvPingFmt {
        fn prepare(&self, v: &TlvPing) -> Result<usize, PreSerializeError> {
            reveal(<TlvPingFmt as SpecByteLen>::byte_len);
            reveal(<TlvPing as DeepView>::deep_view);
            reveal(TlvPingSpec::into_structural);
            let TlvPing {
                nonce,
            } = v;
            let l1 = (U64Be).prepare (nonce) ?;
            let total_len = l1;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for TlvDataFmt {
        type PT = TlvData<'i>;

        fn min_byte_len(&self) -> usize {
            4
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TlvDataFmt as SpecParser>::spec_parse);
            reveal(<TlvData as DeepView>::deep_view);
            reveal(TlvDataSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, seq) = (U32Be).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, body) = (Tail).parse (& rest) ?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = TlvData {
                seq,
                body,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TlvData<'i>> for TlvDataFmt {
        fn serialize_into(&self, v: &TlvData<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<TlvDataFmt as SpecSerializer>::spec_serialize);
            reveal(<TlvDataFmt as SpecByteLen>::byte_len);
            reveal(<TlvData as DeepView>::deep_view);
            reveal(TlvDataSpec::into_structural);
            let ghost old_obuf = obuf@;

            let TlvData {
                seq,
                body,
            } = v;
            U32Be.serialize_into(seq, obuf);
            Tail.serialize_into(body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TlvData<'i>> for TlvDataFmt {
        fn prepare(&self, v: &TlvData<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TlvDataFmt as SpecByteLen>::byte_len);
            reveal(<TlvData as DeepView>::deep_view);
            reveal(TlvDataSpec::into_structural);
            let TlvData {
                seq,
                body,
            } = v;
            let l1 = (U32Be).prepare (seq) ?;
            let l2 = (Tail).prepare (body) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for TlvAddrFmt {
        type PT = TlvAddr<'i>;

        fn min_byte_len(&self) -> usize {
            6
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TlvAddrFmt as SpecParser>::spec_parse);
            reveal(<TlvAddr as DeepView>::deep_view);
            reveal(TlvAddrSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, host) = (Fixed::< 4 >).parse (& rest) ?;
            let rest = rest.skip(n1);
            let (n2, port) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n2);
            let total_n = n1 + n2;
            let final_v = TlvAddr {
                host,
                port,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TlvAddr<'i>> for TlvAddrFmt {
        fn serialize_into(&self, v: &TlvAddr<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<TlvAddrFmt as SpecSerializer>::spec_serialize);
            reveal(<TlvAddrFmt as SpecByteLen>::byte_len);
            reveal(<TlvAddr as DeepView>::deep_view);
            reveal(TlvAddrSpec::into_structural);
            let ghost old_obuf = obuf@;

            let TlvAddr {
                host,
                port,
            } = v;
            Fixed::< 4 >.serialize_into(* host, obuf);
            U16Be.serialize_into(port, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TlvAddr<'i>> for TlvAddrFmt {
        fn prepare(&self, v: &TlvAddr<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TlvAddrFmt as SpecByteLen>::byte_len);
            reveal(<TlvAddr as DeepView>::deep_view);
            reveal(TlvAddrSpec::into_structural);
            let TlvAddr {
                host,
                port,
            } = v;
            let l1 = (Fixed::< 4 >).prepare (host) ?;
            let l2 = (U16Be).prepare (port) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for TlvMsgFmt {
        type PT = TlvMsg<'i>;

        fn min_byte_len(&self) -> usize {
            3
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            broadcast use vest_lib::core::spec::SafeParser::lemma_parse_safe;
            broadcast use vest_lib::core::spec::SoundParser::lemma_parse_sound_value;

            reveal(<TlvMsgFmt as SpecParser>::spec_parse);
            reveal(<TlvMsg as DeepView>::deep_view);
            reveal(TlvMsgSpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            let (n1, kind) = (Named ("tlv_kind", TlvKindFmt)).parse (& rest) ?;
            proof {
                kind.lemma_deep_view();
            }
            let rest = rest.skip(n1);
            let (n2, len) = (U16Be).parse (& rest) ?;
            let rest = rest.skip(n2);
            proof {
                kind.lemma_deep_view();
            }

            let (n3, body) = (ExactLen (len, Named ("tlv_msg_body", TlvMsgBodyFmt {
                kind: kind
            }
            ))).parse (& rest) ?;
            let rest = rest.skip(n3);
            let total_n = n1 + n2 + n3;
            let final_v = TlvMsg {
                kind,
                len,
                body,
            };
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
            Ok((total_n, final_v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TlvMsg<'i>> for TlvMsgFmt {
        fn serialize_into(&self, v: &TlvMsg<'i>, obuf: &mut Output) {
            broadcast use vest_lib::core::exec::output::outbuf_lemmas;
            reveal(<TlvMsgFmt as SpecSerializer>::spec_serialize);
            reveal(<TlvMsgFmt as SpecByteLen>::byte_len);
            reveal(<TlvMsg as DeepView>::deep_view);
            reveal(TlvMsgSpec::into_structural);
            let ghost old_obuf = obuf@;

            let TlvMsg {
                kind,
                len,
                body,
            } = v;
            proof {
                kind.lemma_deep_view();
            }

            TlvKindFmt.serialize_into(kind, obuf);
            U16Be.serialize_into(len, obuf);
            ExactLen (*len, TlvMsgBodyFmt {
                kind: * kind
            }
            )
            .serialize_into(body, obuf);

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TlvMsg<'i>> for TlvMsgFmt {
        fn prepare(&self, v: &TlvMsg<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TlvMsgFmt as SpecByteLen>::byte_len);
            reveal(<TlvMsg as DeepView>::deep_view);
            reveal(TlvMsgSpec::into_structural);
            let TlvMsg {
                kind,
                len,
                body,
            } = v;
            proof {
                kind.lemma_deep_view();
            }

            let l1 = (Named ("tlv_kind", TlvKindFmt)).prepare (kind) ?;
            let l2 = (U16Be).prepare (len) ?;
            let l3 = (ExactLen (*len, Named ("tlv_msg_body", TlvMsgBodyFmt {
                kind: * kind
            }
            ))).prepare (body) ?;
            let total_len = l1.checked_add (l2).ok_or (PreSerializeError::length_too_large()) ?.checked_add (l3).ok_or (PreSerializeError::length_too_large()) ?;
            Ok(total_len)
        }
    }



    impl<'i> Parser<&'i [u8]> for TlvMsgBodyFmt {
        type PT = TlvMsgBody<'i>;

        fn min_byte_len(&self) -> usize {
            4
        }

        fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
            reveal(<TlvMsgBodyFmt as SpecParser>::spec_parse);
            reveal(<TlvMsgBody as DeepView>::deep_view);
            reveal(TlvMsgBodySpec::from_structural);
            let _ = ibuf.len();
            let rest = *ibuf;

            proof {
                use_type_invariant(self);
                self.kind.lemma_deep_view();
            }

            proof {
                self.kind.lemma_deep_view();
            }

            let (n, v) = match self.kind {
                TlvKind::Ping => {
                    let (n,
                    v) = (Named ("tlv_ping",
                    TlvPingFmt)).parse (& rest) ?;
                    (n,
                    TlvMsgBody::Ping (v))
                }
                ,
                TlvKind::Data => {
                    let (n,
                    v) = (Named ("tlv_data",
                    TlvDataFmt)).parse (& rest) ?;
                    (n,
                    TlvMsgBody::Data (v))
                }
                ,
                TlvKind::Addr => {
                    let (n,
                    v) = (Named ("tlv_addr",
                    TlvAddrFmt)).parse (& rest) ?;
                    (n,
                    TlvMsgBody::Addr (v))
                }
                ,
            };
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            Ok((n, v))
        }
    }

    impl<Output: OutputBuf, 'i> Serializer<Output, TlvMsgBody<'i>> for TlvMsgBodyFmt {
        fn serialize_into(&self, v: &TlvMsgBody<'i>, obuf: &mut Output) {
            reveal(<TlvMsgBodyFmt as SpecSerializer>::spec_serialize);
            reveal(<TlvMsgBodyFmt as SpecByteLen>::byte_len);
            reveal(<TlvMsgBody as DeepView>::deep_view);
            reveal(TlvMsgBodySpec::into_structural);
            proof {
                use_type_invariant(self);
                self.kind.lemma_deep_view();
            }

            let ghost old_obuf = obuf@;

            proof {
                self.kind.lemma_deep_view();
            }

            match (self.kind, v) {
                (TlvKind::Ping, TlvMsgBody::Ping (v)) => {
                    (TlvPingFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TlvKind::Data, TlvMsgBody::Data (v)) => {
                    (TlvDataFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                (TlvKind::Addr, TlvMsgBody::Addr (v)) => {
                    (TlvAddrFmt).serialize_into (v,
                    obuf) ;
                }
                ,
                _ => {},
            }

            assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        }
    }

    impl<'i> Prepare<TlvMsgBody<'i>> for TlvMsgBodyFmt {
        fn prepare(&self, v: &TlvMsgBody<'i>) -> Result<usize, PreSerializeError> {
            reveal(<TlvMsgBodyFmt as SpecByteLen>::byte_len);
            reveal(<TlvMsgBody as DeepView>::deep_view);
            reveal(TlvMsgBodySpec::into_structural);
            proof {
                use_type_invariant(self);
                self.kind.lemma_deep_view();
            }

            proof {
                self.kind.lemma_deep_view();
            }

            match (self.kind, v) {
                (TlvKind::Ping, TlvMsgBody::Ping (v)) => (Named ("tlv_ping", TlvPingFmt)).prepare (v),
                (TlvKind::Data, TlvMsgBody::Data (v)) => (Named ("tlv_data", TlvDataFmt)).prepare (v),
                (TlvKind::Addr, TlvMsgBody::Addr (v)) => (Named ("tlv_addr", TlvAddrFmt)).prepare (v),
                 _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        }
    }

}
}
